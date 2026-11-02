"""Run the public-only collector, then validate/stage the three Pages JSON files.

Deploy beside update_papers.py and collect_ai_venues.py at .github/atlas/.
The existing validator stays at .github/scripts/sync_public_catalogue.py.
Only the explicitly sanitized public-source progress file may enter Actions
cache. Candidates, reviews, backups, credentials and model outputs never do.
"""
from __future__ import annotations

import argparse
import base64
import copy
import datetime as dt
import importlib.util
import json
import logging
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import urllib.parse
import zlib

YEARS = (2025, 2026)
SOURCES = ("datacite", "arxiv-rss", "arxiv", "crossref", "cvf", "pmlr", "neurips", "iclr")
MAX_CACHE_BYTES = 32 * 1024 * 1024
OFFICIAL_HOSTS = {
    "arxiv.org", "export.arxiv.org", "rss.arxiv.org", "api.datacite.org",
    "api.crossref.org", "openaccess.thecvf.com", "proceedings.mlr.press",
    "proceedings.neurips.cc", "proceedings.iclr.cc", "neurips.cc", "icml.cc",
    "iclr.cc", "openreview.net", "api2.openreview.net",
}
JOB_FIELDS = {
    "cursor", "cursor_hashes", "offset", "done", "total", "updated_at", "resume_next",
    "records_seen", "split", "queue", "seen", "index_checked", "indexed_total", "cutoff",
    "topic_priority_count", "index_url", "resolved_index_url", "indexed_at",
    "catalogue", "bulk", "index_status", "checked_at", "accepted_mode",
    "accepted_bulk", "accepted_catalogue", "accepted_detail_day", "accepted_detail_turns",
    "accepted_unresolved", "accepted_missing", "accepted_detail_seen", "accepted_total",
    "accepted_abstracts_pending", "accepted_status", "last_success",
}
BULK_FIELDS = {"catalogue_hash", "phase", "matches", "matched", "scanned", "completed_at",
               "failed_on", "download", "rows", "refreshed_on"}
ROW_FIELDS = {"id", "title", "authors", "openreview_id", "pdf_url", "url", "paper_url",
              "decision", "venue_track"}
SOURCE_FIELDS = {"name", "status", "last_attempt", "last_success", "coverage_start", "coverage_end",
                 "query_start", "backfill_complete", "records_found", "pages_fetched"}


class CollectionRefused(ValueError):
    pass


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, allow_nan=False, indent=2) + "\n").encode("utf-8")


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(json_bytes(value))


def official_url(value):
    parts = urllib.parse.urlsplit(value)
    if (parts.scheme != "https" or parts.hostname not in OFFICIAL_HOSTS
            or parts.username or parts.password or parts.port not in (None, 443)):
        raise CollectionRefused("Cached progress contains a non-official URL")


def bounded_tree(value, depth=0):
    """JSON only; validate URLs before any cached queue can initiate requests."""
    if depth > 15:
        raise CollectionRefused("Progress nesting is excessive")
    if isinstance(value, dict):
        for key, item in value.items():
            if not isinstance(key, str):
                raise CollectionRefused("Progress keys must be text")
            if key.startswith(("https://", "http://")):
                official_url(key)
            bounded_tree(item, depth + 1)
    elif isinstance(value, list):
        for item in value:
            bounded_tree(item, depth + 1)
    elif isinstance(value, str):
        if len(value) > 4 * 1024 * 1024:
            raise CollectionRefused("Progress string is excessive")
        if value.startswith(("https://", "http://")):
            official_url(value)
    elif value is not None and type(value) not in (int, float, bool):
        raise CollectionRefused("Unsupported progress value")


def public_row(row):
    if not isinstance(row, dict):
        raise CollectionRefused("Malformed public metadata row")
    return {k: copy.deepcopy(v) for k, v in row.items() if k in ROW_FIELDS}


def clean_bulk(raw):
    if not isinstance(raw, dict):
        raise CollectionRefused("Malformed bulk progress")
    result = {k: copy.deepcopy(v) for k, v in raw.items() if k in BULK_FIELDS}
    for name in ("matches", "rows"):
        if name in result:
            result[name] = {key: public_row(row) for key, row in result[name].items()}
    if "download" in result:
        original = result["download"]
        download = {k: original[k] for k in ("url", "offset", "chunks", "total", "etag") if k in original}
        official_url(download["url"])
        # These are compressed bytes from the official public static JSON,
        # never a private candidate queue. Bound decompression before restoring.
        total = 0
        for chunk in download.get("chunks", []):
            decoder = zlib.decompressobj()
            decoded = decoder.decompress(base64.b64decode(chunk, validate=True), 2 * 1024 * 1024 + 1)
            if len(decoded) > 2 * 1024 * 1024 or not decoder.eof or decoder.unused_data:
                raise CollectionRefused("Invalid public bulk progress chunk")
            total += len(decoded)
        if (type(download.get("offset")) is not int or download["offset"] != total
                or total > 64 * 1024 * 1024
                or type(download.get("total", 0)) is not int
                or download.get("total", 0) > 64 * 1024 * 1024):
            raise CollectionRefused("Invalid public bulk progress offsets")
        result["download"] = download
    return result


def sanitize_state(raw):
    """Allow only audited public pagination/catalogue fields, not arbitrary data."""
    if not isinstance(raw, dict):
        raise CollectionRefused("Collector progress must be an object")
    result = {"jobs": {}, "sources": {}}
    for name, job in raw.get("jobs", {}).items():
        if not isinstance(name, str) or not re.fullmatch(
                r"(?:arxiv|arxiv-rss|datacite|crossref|cvf|ai-proceedings|ai-accepted):[A-Za-z0-9:._-]{1,180}", name):
            continue
        if not isinstance(job, dict):
            raise CollectionRefused("Malformed pagination job")
        kept = {k: copy.deepcopy(v) for k, v in job.items() if k in JOB_FIELDS}
        for field in ("bulk", "accepted_bulk"):
            if field in kept:
                kept[field] = clean_bulk(kept[field])
        if "catalogue" in kept:
            kept["catalogue"] = {url: public_row(row) for url, row in kept["catalogue"].items()}
        if "accepted_missing" in kept:
            kept["accepted_missing"] = [public_row(row) for row in kept["accepted_missing"]]
        # Failed detail URLs already occur in the pending queue. Preserve retry
        # membership but deliberately discard exception text/response fragments.
        if isinstance(job.get("failed"), dict):
            kept["failed"] = {url: "public detail retry" for url in job["failed"]}
        result["jobs"][name] = kept
    for name, status in raw.get("sources", {}).items():
        if name in SOURCES and isinstance(status, dict):
            result["sources"][name] = {k: v for k, v in status.items() if k in SOURCE_FIELDS}
    for field in ("query_signatures", "query_reset_at", "ai_venue_next_year"):
        values = raw.get(field, {})
        if isinstance(values, dict):
            result[field] = {k: v for k, v in values.items() if k in SOURCES and isinstance(v, (str, int))}
    result["ai_venue_volumes"] = {k: str(v) for k, v in raw.get("ai_venue_volumes", {}).items()
                                 if k in ("2025", "2026") and str(v).isdigit()}
    for field in ("arxiv_rss_next_feed", "cvf_next_task"):
        if type(raw.get(field)) is int and raw[field] >= 0:
            result[field] = raw[field]
    if re.fullmatch(r"\d{4}-\d{2}", str(raw.get("last_full_reset", ""))):
        result["last_full_reset"] = raw["last_full_reset"]
    bounded_tree(result)
    if len(json_bytes(result)) > MAX_CACHE_BYTES:
        raise CollectionRefused("Public progress exceeds the 32 MB cache limit")
    return result


def cache_envelope(state):
    return {"schema_version": 1, "origin": "github-public-collector", "state": sanitize_state(state)}


def restore_cache(path):
    if not path.exists():
        return {"jobs": {}, "sources": {}}
    try:
        if path.is_symlink() or path.stat().st_size > MAX_CACHE_BYTES + 1024:
            raise CollectionRefused("Invalid progress cache file")
        cached = json.loads(path.read_text(encoding="utf-8"))
        if cached.get("schema_version") != 1 or cached.get("origin") != "github-public-collector":
            raise CollectionRefused("Unrecognized progress cache provenance")
        return sanitize_state(cached["state"])
    except Exception as exc:
        print("Ignoring invalid public progress cache: " + type(exc).__name__, file=sys.stderr)
        return {"jobs": {}, "sources": {}}


def collector_environment(parent):
    # Build an allowlist, rather than trying to enumerate every provider's keys.
    keep = {"PATH", "HOME", "USERPROFILE", "SYSTEMROOT", "WINDIR", "TEMP", "TMP", "TMPDIR",
            "LANG", "LC_ALL", "SSL_CERT_FILE", "SSL_CERT_DIR", "PYTHONIOENCODING"}
    env = {name: value for name, value in parent.items() if name in keep}
    env.update(SUMMARY_LIMIT="0", ARXIV_SCREENING_LIMIT="0", ABSTRACT_ENRICH_LIMIT="0",
               SCHEDULE_ENABLED="1", SCHEDULE_TIMES="08:00,14:00", PYTHONUNBUFFERED="1")
    return env


def worker(args):
    sys.path.insert(0, str(Path(args.collector_dir).resolve()))
    import update_papers as pipeline
    successful_requests = 0
    successful_by_source = {name: 0 for name in SOURCES}
    active_source = None
    original_get = pipeline.HttpClient.get
    original_reset = pipeline.reset_changed_query
    def track_source(state, source, *a, **kw):
        nonlocal active_source
        active_source = source
        return original_reset(state, source, *a, **kw)
    def public_get(self, *a, **kw):
        nonlocal successful_requests
        response = original_get(self, *a, **kw)
        successful_requests += 1
        if active_source in successful_by_source:
            successful_by_source[active_source] += 1
        return response
    def no_models(*_a, **_kw):
        raise CollectionRefused("Model calls are disabled in the free public collector")
    pipeline.HttpClient.get = public_get
    pipeline.reset_changed_query = track_source
    pipeline.model_configuration = lambda: None
    pipeline.generate_summary = pipeline.screen_candidate = no_models
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    until = min(dt.datetime.now(pipeline.SHANGHAI).date(), dt.date(2026, 12, 31)).isoformat()
    options = argparse.Namespace(root=args.work_root, since="2025-01-01", until=until,
                                 sources=",".join(SOURCES), max_pages=12, lookback=45,
                                 timeout=25, retries=1, full=False, summary_limit=0,
                                 deadline_seconds=args.budget_seconds)
    try:
        return pipeline.run(options)
    finally:
        write_json(Path(args.work_root) / "request-stats.json", {
            "successful_http_requests": successful_requests, "successful_by_source": successful_by_source})


def assert_preserved(previous, incoming, pipeline, exclusions):
    all_new = {key for p in incoming["papers"] + incoming["preprints"] for key in pipeline.identity_keys(p)}
    main_new = {key for p in incoming["papers"] for key in pipeline.identity_keys(p)}
    for collection in ("papers", "preprints"):
        for p in previous[collection]:
            keys = set(pipeline.identity_keys(p))
            if pipeline.catalogue_year(p) not in YEARS or p["id"] in exclusions or keys.intersection(exclusions):
                continue
            if not keys.intersection(main_new if collection == "papers" else all_new):
                raise CollectionRefused("Previously public record disappeared: " + p["id"])


def collect(args, runner=subprocess.run):
    repository = Path(args.repository).resolve()
    collector_dir = Path(args.collector_dir).resolve()
    target = repository / "paper-atlas/data"
    validator = load_module("atlas_public_validator", repository / ".github/scripts/sync_public_catalogue.py")
    pipeline = load_module("atlas_public_identity", collector_dir / "update_papers.py")
    previous = validator.decode_json((target / "papers.json").read_bytes())
    validator.validate_snapshot(previous)
    cache_path = Path(args.cache_file).absolute()
    if cache_path.is_symlink():
        raise CollectionRefused("Progress cache may not be a symbolic link")
    if cache_path == target / "papers.json":
        raise CollectionRefused("Cache cannot overwrite the public catalogue")
    exclusions = {}
    exclusion_path = collector_dir / "editorial-reviews.json"
    if exclusion_path.exists():
        exclusions = validator.decode_json(exclusion_path.read_bytes())
        if not isinstance(exclusions, dict) or any(not isinstance(k, str) or v != {"decision": "exclude"} for k, v in exclusions.items()):
            raise CollectionRefused("Only public ID-to-exclude editorial decisions are allowed")
    with tempfile.TemporaryDirectory(prefix="atlas-public-collection-") as temporary:
        work = Path(temporary)
        write_json(work / "dist/data/papers.json", previous)
        write_json(work / "data/collector-state.json", restore_cache(cache_path))
        write_json(work / "data/editorial-reviews.json", exclusions)
        command = [sys.executable, str(Path(__file__).resolve()), "--worker", "--collector-dir", str(collector_dir),
                   "--work-root", str(work), "--budget-seconds", str(args.budget_seconds)]
        result = runner(command, env=collector_environment(os.environ), timeout=args.budget_seconds + 90, check=False)
        if result.returncode not in (0, 2):
            raise CollectionRefused("Collector failed; existing public snapshot is unchanged")
        incoming = validator.decode_json((work / "dist/data/papers.json").read_bytes())
        validator.validate_snapshot(incoming)
        validator.validate_catalogue_years(incoming, YEARS)
        stats = validator.decode_json((work / "request-stats.json").read_bytes())
        attempted = [s for s in incoming["sources"] if s.get("checked_this_run", True)]
        if ({s["name"] for s in attempted} != set(SOURCES)
                or not any(s["status"] in ("ok", "incomplete")
                           and stats.get("successful_by_source", {}).get(s["name"], 0) > 0 for s in attempted)
                or type(stats.get("successful_http_requests")) is not int
                or stats["successful_http_requests"] < 1):
            raise CollectionRefused("No successful public-source collection; refusing a false freshness update")
        assert_preserved(previous, incoming, pipeline, exclusions)
        incoming["meta"]["collection_runtime"] = "github-actions-public-runner"
        incoming["meta"]["schedule"]["note"] = "GitHub Actions schedules may be delayed; times are targets, not guarantees."
        # Never propagate unpublished candidate objects or private review files.
        try:
            pending_state = cache_envelope(validator.decode_json((work / "data/collector-state.json").read_bytes()))
        except Exception as exc:
            # Progress is optional. Restart from zero rather than retaining a
            # partially sanitized cursor that could skip uncommitted records.
            print("Discarding this run's progress cache: " + type(exc).__name__, file=sys.stderr)
            pending_state = cache_envelope({})
        snapshot_bytes = json_bytes(incoming)
        result = validator.synchronize(target, url=args.run_url, fetcher=lambda _url, _timeout: snapshot_bytes,
                                       max_age_hours=26, catalogue_years=YEARS)
        mirror = validator.decode_json((target / "mirror.json").read_bytes())
        mirror.update(source_kind="github-actions", collector_model_calls=False)
        validator.stage_and_replace(target, {"mirror.json": json_bytes(mirror)})
        try:
            validator.stage_and_replace(cache_path.parent, {cache_path.name: json_bytes(pending_state)})
        except Exception as exc:
            # Publication is valid even if the optional cache is unavailable.
            # An older cache can only replay already published records.
            print("Public catalogue staged; progress cache unavailable: " + type(exc).__name__, file=sys.stderr)
        return dict(result, sources_attempted=len(attempted), successful_http_requests=stats["successful_http_requests"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=".")
    parser.add_argument("--collector-dir", default=str(Path(__file__).parent))
    parser.add_argument("--cache-file", default=".atlas-public-progress/collector-state.json")
    parser.add_argument("--run-url")
    parser.add_argument("--budget-seconds", type=int, default=750)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--work-root", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not 600 <= args.budget_seconds <= 900:
        parser.error("Collection budget must be between 600 and 900 seconds")
    if args.worker:
        return worker(args)
    parsed = urllib.parse.urlsplit(args.run_url or "")
    if parsed.scheme != "https" or parsed.hostname != "github.com" or not re.fullmatch(r"/[^/]+/[^/]+/actions/runs/\d+", parsed.path):
        parser.error("--run-url must identify this public GitHub Actions run")
    try:
        print(json.dumps(collect(args), ensure_ascii=False))
    except Exception as exc:
        print("Public collection refused: " + type(exc).__name__ + ": " + str(exc)[:240], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
