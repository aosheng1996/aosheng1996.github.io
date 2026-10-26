"""Validate one public snapshot, then stage only the paper-atlas data mirror.

No cloud credentials, private state, collection, or model calls are involved.
The workflow publishes the three prepared files together in one Git commit.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import datetime as dt
import gzip
import hashlib
import http.client
import io
import json
import os
from pathlib import Path
import re
import signal
import ssl
import sys
import tempfile
import threading
import time
import urllib.parse
import urllib.error
import urllib.request
import zlib

SOURCE_URL = "https://asc-d9g8a33rmaf55cf87-1505352887.tcloudbaseapp.com/paper-atlas/data/papers.json"
MAX_BYTES = 20 * 1024 * 1024
CATEGORIES = {"visual-localization", "point-localization", "place-recognition", "registration", "point-processing", "uav-navigation"}
PRIVATE_KEYS = {"review", "reviews", "candidates", "candidate_queue", "collector_state", "tokens", "token", "access_token", "refresh_token", "session_token", "secret", "secretid", "secretkey", "secret_id", "secret_key", "api_key", "apikey", "password", "authorization", "operator_notes", "private_notes", "credentials"}


class SnapshotError(ValueError):
    pass


class IncompleteTransfer(SnapshotError):
    """A fresh full download may recover; never reuse partial response bytes."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *_args, **_kwargs):
        raise SnapshotError("Public snapshot must be served directly without a redirect")


@contextmanager
def total_timeout(seconds):
    supported = hasattr(signal, "setitimer") and threading.current_thread() is threading.main_thread()
    if not supported:
        yield
        return
    old_handler = signal.getsignal(signal.SIGALRM)
    def stop(_signal, _frame):
        raise TimeoutError("Public snapshot total request deadline reached")
    signal.signal(signal.SIGALRM, stop)
    old_timer = signal.setitimer(signal.ITIMER_REAL, seconds)
    started = time.monotonic()
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
        if old_timer[0]:
            signal.setitimer(signal.ITIMER_REAL, max(0.001, old_timer[0] - (time.monotonic() - started)), old_timer[1])


def source_url(value):
    parsed = urllib.parse.urlsplit(value)
    if parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password or parsed.query or parsed.fragment:
        raise SnapshotError("Source must be a public HTTPS URL without credentials, query, or fragment")
    return value


def fetch_snapshot(url, timeout=30):
    source_url(url)
    if not 1 <= timeout <= 120:
        raise SnapshotError("Timeout must be between 1 and 120 seconds")
    request = urllib.request.Request(url, headers={"User-Agent": "SpatialAtlasPublicMirror/1.0", "Accept": "application/json", "Accept-Encoding": "gzip"})
    deadline = time.monotonic() + timeout
    opener = urllib.request.build_opener(NoRedirect())
    # One shared wall-clock budget covers all attempts, reads, and backoff.
    # A failed attempt's chunks are discarded before opening the next response.
    with total_timeout(timeout):
        for attempt in range(1, 4):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("Public snapshot total request deadline reached")
            expected, size, encoding, outcome = None, 0, "unknown", "failed"
            try:
                with opener.open(request, timeout=min(30, remaining)) as response:
                    if response.status != 200:
                        raise SnapshotError("Public snapshot did not return HTTP 200")
                    length = response.headers.get("Content-Length")
                    encoding = response.headers.get("Content-Encoding", "identity").lower().strip()
                    expected = int(length) if length is not None and length.isdigit() else None
                    if length is not None and (expected is None or expected > MAX_BYTES):
                        raise SnapshotError("Public snapshot has an invalid or excessive Content-Length")
                    if encoding not in ("gzip", "", "identity"):
                        raise SnapshotError("Unsupported snapshot content encoding")
                    chunks = []
                    while True:
                        if time.monotonic() >= deadline:
                            raise TimeoutError("Public snapshot total request deadline reached")
                        chunk = response.read1(min(65536, MAX_BYTES + 1 - size))
                        if not chunk:
                            break
                        chunks.append(chunk)
                        size += len(chunk)
                        if size > MAX_BYTES:
                            raise SnapshotError("Public snapshot exceeds 20 MB")
                    if expected is not None and size != expected:
                        raise IncompleteTransfer(f"Public snapshot transfer is incomplete (expected={expected}, received={size}, encoding={encoding})")
                    body = b"".join(chunks)
                    if encoding == "gzip":
                        try:
                            with gzip.GzipFile(fileobj=io.BytesIO(body)) as stream:
                                body = stream.read(MAX_BYTES + 1)
                        except EOFError as exc:
                            raise IncompleteTransfer("Compressed public snapshot transfer is incomplete") from exc
                        except (gzip.BadGzipFile, zlib.error) as exc:
                            raise SnapshotError("Invalid gzip public snapshot") from exc
                    if len(body) > MAX_BYTES:
                        raise SnapshotError("Decompressed public snapshot exceeds 20 MB")
                    if time.monotonic() >= deadline:
                        raise TimeoutError("Public snapshot total request deadline reached")
                    outcome = "complete"
                    return body
            except (IncompleteTransfer, OSError, urllib.error.URLError, http.client.HTTPException) as exc:
                outcome = type(exc).__name__
                if isinstance(exc, urllib.error.HTTPError) and exc.code not in (408, 429, 500, 502, 503, 504):
                    raise
                reason = exc.reason if isinstance(exc, urllib.error.URLError) else exc
                if isinstance(reason, ssl.SSLCertVerificationError) or attempt == 3:
                    raise
                remaining = deadline - time.monotonic()
                delay = float(attempt)
                if remaining <= delay:
                    raise TimeoutError("Public snapshot total request deadline reached") from exc
            finally:
                print(json.dumps({"event": "snapshot_download", "attempt": attempt, "expected_bytes": expected,
                                  "received_bytes": size, "encoding": encoding[:40], "outcome": outcome}), file=sys.stderr, flush=True)
            time.sleep(delay)


def decode_json(body):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise SnapshotError("Duplicate JSON key")
            result[key] = value
        return result
    def invalid_constant(_value):
        raise SnapshotError("Non-finite JSON number")
    try:
        return json.loads(body.decode("utf-8-sig"), object_pairs_hook=pairs, parse_constant=invalid_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise SnapshotError("Response is not a UTF-8 JSON snapshot") from exc


def timestamp(value):
    if not isinstance(value, str):
        raise SnapshotError("Snapshot timestamp must be a string")
    try:
        result = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as exc:
        raise SnapshotError("Invalid snapshot timestamp") from exc
    if result.tzinfo is None:
        raise SnapshotError("Snapshot timestamp must include its timezone")
    return result


def reject_private_fields(value, depth=0):
    if depth > 35:
        raise SnapshotError("Snapshot nesting is excessive")
    if isinstance(value, dict):
        for key, item in value.items():
            normalized = re.sub(r"[^a-z0-9]+", "_", key.lower()).strip("_")
            if normalized in PRIVATE_KEYS or normalized.startswith(("tencentcloud_secret", "tencentcloud_session")):
                raise SnapshotError("Snapshot contains a private field: " + key)
            reject_private_fields(item, depth + 1)
    elif isinstance(value, list):
        for item in value:
            reject_private_fields(item, depth + 1)


def validate_snapshot(snapshot):
    if not isinstance(snapshot, dict) or set(snapshot) != {"papers", "preprints", "meta", "sources"}:
        raise SnapshotError("Expected the complete public snapshot schema")
    reject_private_fields(snapshot)
    if not isinstance(snapshot["meta"], dict) or not isinstance(snapshot["sources"], list):
        raise SnapshotError("Invalid metadata or source status collection")
    identities = set()
    for collection in ("papers", "preprints"):
        records = snapshot[collection]
        if not isinstance(records, list):
            raise SnapshotError("Paper collection is not an array")
        for record in records:
            if not isinstance(record, dict):
                raise SnapshotError("Paper record is not an object")
            identity = record.get("id")
            if not isinstance(identity, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._:-]{0,159}", identity) or identity in identities:
                raise SnapshotError("Missing, malformed, or duplicate paper ID")
            identities.add(identity)
            for field in ("title", "venue", "published", "source_url"):
                if not isinstance(record.get(field), str) or not record[field].strip():
                    raise SnapshotError("Paper lacks a core text field: " + field)
            if type(record.get("year")) is not int or not 1900 <= record["year"] <= 2100:
                raise SnapshotError("Invalid paper year")
            published = record["published"]
            if not re.fullmatch(r"\d{4}(?:-\d{2})?(?:-\d{2})?", published):
                raise SnapshotError("Invalid publication date precision")
            try:
                dt.date.fromisoformat(published + {4: "-01-01", 7: "-01", 10: ""}[len(published)])
            except ValueError as exc:
                raise SnapshotError("Invalid publication date") from exc
            authors = record.get("authors")
            if not isinstance(authors, list) or not authors or any(not isinstance(a, str) or not a.strip() for a in authors):
                raise SnapshotError("Invalid author list")
            categories = record.get("categories")
            if not isinstance(categories, list) or not categories or any(c not in CATEGORIES for c in categories):
                raise SnapshotError("Invalid topic categories")
            if record.get("publication_status") not in ("published", "accepted", "preprint") or record.get("summary_status") not in ("reviewed", "generated", "pending"):
                raise SnapshotError("Invalid publication or summary status")
            if record["publication_status"] == "accepted":
                if record.get("acceptance_basis") not in ("official", "author_claim") or record.get("accepted_venue") != record["venue"]:
                    raise SnapshotError("Accepted paper lacks a clear venue or evidence basis")
                if record.get("accepted_year") is not None and (type(record["accepted_year"]) is not int or not 1900 <= record["accepted_year"] <= 2100):
                    raise SnapshotError("Invalid acceptance venue year")
                evidence = record.get("acceptance_evidence")
                if not isinstance(record.get("acceptance_note"), str) or not record["acceptance_note"].strip() or not isinstance(evidence, list) or not evidence:
                    raise SnapshotError("Accepted paper lacks an explanation or evidence")
                for item in evidence:
                    if not isinstance(item, dict) or any(not isinstance(item.get(k), str) or not item[k].strip() for k in ("url", "kind", "quote")):
                        raise SnapshotError("Invalid acceptance evidence")
                    parts = urllib.parse.urlsplit(item["url"])
                    if parts.scheme != "https" or not parts.hostname or parts.username or parts.password:
                        raise SnapshotError("Unsafe acceptance evidence link")
            if not isinstance(record.get("summary_zh"), str) or (record["summary_status"] != "pending" and not record["summary_zh"].strip()):
                raise SnapshotError("Invalid Chinese summary")
            if collection == "preprints" and (record["publication_status"] != "preprint" or record.get("review_status") != "pending"):
                raise SnapshotError("Observation record must remain a pending preprint")
            for field in ("source_url", "pdf_url", "code_url", "evidence_url"):
                url = record.get(field)
                if url and (not isinstance(url, str) or urllib.parse.urlsplit(url).scheme not in ("http", "https") or not urllib.parse.urlsplit(url).hostname):
                    raise SnapshotError("Invalid paper link")
    if not snapshot["papers"]:
        raise SnapshotError("Refusing an empty main catalogue")
    meta = snapshot["meta"]
    if meta.get("schema_version") != 1 or type(meta.get("total_papers")) is not int or meta["total_papers"] != len(snapshot["papers"]):
        raise SnapshotError("Main catalogue count disagrees with metadata")
    if "preprint_count" in meta and (type(meta["preprint_count"]) is not int or meta["preprint_count"] != len(snapshot["preprints"])):
        raise SnapshotError("Observation count disagrees with metadata")
    counts = {status: sum(r["summary_status"] == status for r in snapshot["papers"]) for status in ("reviewed", "generated", "pending")}
    if meta.get("summary_counts") != counts:
        raise SnapshotError("Summary counts disagree with records")
    if meta.get("collection_status") not in ("ok", "partial", "curated_only") or type(meta.get("candidate_count")) is not int or meta["candidate_count"] < 0:
        raise SnapshotError("Invalid collection status or candidate aggregate")
    generated = timestamp(meta.get("generated_at"))
    if generated > dt.datetime.now(dt.timezone.utc) + dt.timedelta(minutes=10):
        raise SnapshotError("Source timestamp is in the future")
    if meta.get("last_successful_update") is not None and timestamp(meta["last_successful_update"]) > generated:
        raise SnapshotError("Successful update is newer than the snapshot")
    names = set()
    for source in snapshot["sources"]:
        if not isinstance(source, dict) or not isinstance(source.get("name"), str) or not source["name"] or source["name"] in names or source.get("status") not in ("ok", "incomplete", "error"):
            raise SnapshotError("Invalid or duplicate source health record")
        names.add(source["name"])
    return generated


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n").encode("utf-8")


def derived_health(snapshot):
    meta = snapshot["meta"]
    return {"status": meta["collection_status"], "checked_at": meta["generated_at"],
            "last_successful_update": meta.get("last_successful_update"), "papers": len(snapshot["papers"]),
            "pending_candidates": meta["candidate_count"],
            "failed_sources": [source["name"] for source in snapshot["sources"] if source["status"] == "error"]}


def stage_and_replace(directory, payloads):
    """Prepare all files before replacement, roll back caught write failures.

    Filesystem rename is atomic per file, not across several files. The workflow
    commits only after this returns successfully; a failed/killed runner never
    publishes its working directory, preserving the previous public snapshot.
    """
    directory.mkdir(parents=True, exist_ok=True)
    if directory.is_symlink() or any((directory / name).is_symlink() for name in payloads):
        raise SnapshotError("Mirror targets may not be symbolic links")
    previous = {name: (directory / name).read_bytes() if (directory / name).exists() else None for name in payloads}
    staged, replaced = {}, []
    def temporary(content):
        fd, name = tempfile.mkstemp(prefix=".atlas-", dir=directory)
        with os.fdopen(fd, "wb") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        return Path(name)
    try:
        for name, content in payloads.items():
            staged[name] = temporary(content)
        for name, path in staged.items():
            os.replace(path, directory / name)
            replaced.append(name)
    except BaseException:
        for name in reversed(replaced):
            if previous[name] is None:
                (directory / name).unlink(missing_ok=True)
            else:
                rollback = temporary(previous[name])
                try:
                    os.replace(rollback, directory / name)
                finally:
                    rollback.unlink(missing_ok=True)
        raise
    finally:
        for path in staged.values():
            path.unlink(missing_ok=True)


def synchronize(directory, url=SOURCE_URL, timeout=30, removal_reason="", fetcher=fetch_snapshot):
    url = source_url(url)
    if len(removal_reason) > 500:
        raise SnapshotError("Removal explanation is too long")
    incoming = decode_json(fetcher(url, timeout))
    generated = validate_snapshot(incoming)
    paper_bytes = json_bytes(incoming)
    expected_health = derived_health(incoming)
    digest = hashlib.sha256(paper_bytes).hexdigest()
    directory = Path(directory)
    prior_path = directory / "papers.json"
    removed = []
    if prior_path.exists():
        previous = decode_json(prior_path.read_bytes())
        old_generated = validate_snapshot(previous)
        if generated < old_generated:
            raise SnapshotError("Source snapshot is older than the current mirror")
        if generated == old_generated and incoming != previous:
            raise SnapshotError("Source changed without advancing generated_at")
        old_ids = {r["id"] for r in previous["papers"]}
        removed = sorted(old_ids - {r["id"] for r in incoming["papers"]})
        if len(removed) / len(old_ids) > 0.2 and not removal_reason.strip():
            raise SnapshotError("More than 20% of main catalogue IDs disappeared; manual explanation required")
        if incoming == previous:
            try:
                old_health = decode_json((directory / "health.json").read_bytes())
                old_mirror = decode_json((directory / "mirror.json").read_bytes())
                consistent = old_health == expected_health and isinstance(old_mirror, dict) and old_mirror.get("snapshot_sha256") == digest and old_mirror.get("source_url") == url and old_mirror.get("source_generated_at") == incoming["meta"]["generated_at"]
            except (OSError, ValueError):
                consistent = False
            if consistent:
                return {"changed": False, "generated_at": incoming["meta"]["generated_at"], "papers": len(incoming["papers"])}
    mirror = {"source_url": url, "source_generated_at": incoming["meta"]["generated_at"],
              "mirrored_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
              "snapshot_sha256": digest, "removed_main_ids": removed}
    if removal_reason.strip():
        mirror["removal_explanation"] = removal_reason.strip()
    stage_and_replace(directory, {"papers.json": paper_bytes, "health.json": json_bytes(expected_health), "mirror.json": json_bytes(mirror)})
    return {"changed": True, "generated_at": incoming["meta"]["generated_at"], "papers": len(incoming["papers"]), "preprints": len(incoming["preprints"])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target-dir", default="paper-atlas/data")
    parser.add_argument("--source-url", default=SOURCE_URL)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--allow-removals-reason", default="", help="Public manual explanation permitting more than 20%% removed main IDs")
    args = parser.parse_args()
    try:
        print(json.dumps(synchronize(args.target_dir, args.source_url, args.timeout, args.allow_removals_reason)))
    except Exception as exc:
        print("Mirror update refused: " + type(exc).__name__ + ": " + str(exc)[:240])
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
