"""Resumable official ICML, NeurIPS and ICLR proceedings collection.

Integration: ``yield from collect("pmlr", collector)`` (also neurips/iclr).
The existing Collector supplies client.get, budget(), job(), since and until.
Every accepted-paper detail is eventually inspected; topical titles are visited
first, but title-only filtering never permanently excludes a paper. Annual
indexes refresh daily, including past years, so late additions are discovered.
Only official proceedings pages with matching citation metadata are published.
Official virtual-conference JSON supplies bulk abstracts only after exact title
and author agreement with the official proceedings index. Submission APIs and
author acceptance claims are never publication evidence. When current NeurIPS
proceedings are not available, its official accepted programme is collected
separately with status ``accepted`` and explicit acceptance evidence.
"""
from __future__ import annotations

import datetime as dt
import base64
import html
import hashlib
import json
from html.parser import HTMLParser
import logging
import os
import re
import urllib.parse
import unicodedata
import zlib

LOG = logging.getLogger("paper-atlas.ai-venues")
SOURCES = {"pmlr": "ICML", "neurips": "NeurIPS", "iclr": "ICLR"}
VIRTUAL_HOSTS = {"pmlr": "icml.cc", "neurips": "neurips.cc", "iclr": "iclr.cc"}
BULK_CHUNK_BYTES = 2 * 1024 * 1024
BULK_MAX_BYTES = 64 * 1024 * 1024
PMLR_VOLUMES = {2025: "267", 2026: "306"}
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}


def bulk_chunk_bytes():
    """Bound cloud transfer chunks without changing local default/checkpoints."""
    configured = os.environ.get("BULK_CHUNK_BYTES")
    if configured is None:
        return BULK_CHUNK_BYTES
    try:
        return max(64 * 1024, min(2 * 1024 * 1024, int(configured)))
    except ValueError as exc:
        raise ValueError("BULK_CHUNK_BYTES must be an integer byte count") from exc


def helpers():
    # Lazy import avoids a circular import when the updater registers collectors.
    import update_papers
    return update_papers


class Document(HTMLParser):
    """Small HTML reader shared by official index and detail pages."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.meta, self.links, self.papers, self.list_items = {}, [], [], []
        self.text, self.abstract = [], []
        self.depth = 0
        self.anchor = None
        self.heading = None
        self.want_abstract = False
        self.abstract_at = None
        self.paper = None
        self.paper_title_at = None
        self.item = None
        self.author_at = None
        self.catalogue_entries = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag not in VOID:
            self.depth += 1
        if tag == "meta":
            key = a.get("name", a.get("property", "")).lower()
            self.meta.setdefault(key, []).append(a.get("content", ""))
        if tag == "a":
            self.anchor = {"href": a.get("href", ""), "text": []}
        if tag in {"h1", "h2", "h3", "h4", "h5", "h6"}:
            self.heading = {"depth": self.depth, "text": []}
        if a.get("id") == "abstract" or "abstract-text-inner" in a.get("class", "").split() or (tag == "p" and self.want_abstract):
            self.abstract_at = self.depth
            self.want_abstract = False
        if tag == "div" and "paper" in a.get("class", "").split():
            self.paper = {"depth": self.depth, "title": [], "url": "", "authors": [], "openreview_id": ""}
        if self.paper and tag == "p" and "title" in a.get("class", "").split():
            self.paper_title_at = self.depth
        if tag == "li":
            self.item = {"depth": self.depth, "text": [], "url": "", "authors": [], "title": ""}
        classes = a.get("class", "").split()
        if (self.paper is not None or self.item is not None) and ("authors" in classes or "paper-authors" in classes):
            self.author_at = self.depth

    def handle_data(self, data):
        self.text.append(data)
        if self.anchor is not None:
            self.anchor["text"].append(data)
        if self.heading is not None:
            self.heading["text"].append(data)
        if self.abstract_at is not None:
            self.abstract.append(data)
        if self.paper is not None and self.paper_title_at is not None:
            self.paper["title"].append(data)
        if self.item is not None:
            self.item["text"].append(data)
        if self.author_at is not None:
            target = self.paper if self.paper is not None else self.item
            if target is not None:
                target["authors"].append(data)

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        if tag == "a" and self.anchor is not None:
            href, text = self.anchor["href"], " ".join("".join(self.anchor["text"]).split())
            self.links.append((href, text))
            if self.paper is not None and text.casefold() == "abs":
                self.paper["url"] = href
            if self.paper is not None and _openreview_id(href):
                self.paper["openreview_id"] = _openreview_id(href)
            if self.item is not None and not self.item["url"]:
                self.item["url"] = href
                self.item["title"] = text
            self.anchor = None
        if self.heading is not None and self.depth == self.heading["depth"]:
            self.want_abstract = "".join(self.heading["text"]).strip().casefold() == "abstract"
            self.heading = None
        if self.abstract_at == self.depth:
            self.abstract_at = None
        if self.paper_title_at == self.depth:
            self.paper_title_at = None
        if self.author_at == self.depth:
            self.author_at = None
        if self.paper is not None and self.depth == self.paper["depth"]:
            self.papers.append((self.paper["url"], " ".join("".join(self.paper["title"]).split())))
            self.catalogue_entries.append({"url": self.paper["url"], "authors": "".join(self.paper["authors"]), "openreview_id": self.paper["openreview_id"]})
            self.paper = None
        if self.item is not None and self.depth == self.item["depth"]:
            self.list_items.append((self.item["url"], " ".join("".join(self.item["text"]).split())))
            self.catalogue_entries.append({"url": self.item["url"], "authors": "".join(self.item["authors"])})
            self.item = None
        self.depth = max(0, self.depth - 1)


def document(text):
    doc = Document()
    doc.feed(text)
    doc.close()
    return doc


def parse_index(text, url, source, year):
    doc = document(text)
    if source == "pmlr":
        if "international conference on machine learning" not in " ".join(doc.text).casefold():
            raise ValueError("PMLR index is not an ICML proceedings volume")
        candidates = doc.papers
    else:
        candidates = doc.links
    parsed = {}
    for href, title in candidates:
        link = urllib.parse.urljoin(url, href)
        parts = urllib.parse.urlsplit(link)
        if parts.netloc != urllib.parse.urlsplit(url).netloc or "workshop" in parts.path.casefold():
            continue
        if source == "pmlr":
            valid = parts.path.startswith(urllib.parse.urlsplit(url).path) and parts.path.endswith(".html")
        else:
            valid = f"/paper/{year}/hash/" in parts.path and (parts.path.endswith("-Abstract-Conference.html") or parts.path.endswith("-Abstract-Datasets_and_Benchmarks_Track.html"))
        if valid and title:
            parsed[link] = title
    if not parsed:
        raise ValueError("No accepted proceedings entries parsed; index unavailable or HTML changed: " + url)
    return parsed


def parse_catalogue(text, url, source, year):
    """Keep authoritative author names alongside accepted proceedings titles."""
    titles = parse_index(text, url, source, year)
    metadata = {link: {"title": title, "authors": []} for link, title in titles.items()}
    for entry in document(text).catalogue_entries:
        link = urllib.parse.urljoin(url, entry["url"])
        if link in metadata and entry["authors"].strip():
            metadata[link]["authors"] = [" ".join(name.split()) for name in entry["authors"].split(",") if name.strip()]
            if entry.get("openreview_id"):
                metadata[link]["openreview_id"] = entry["openreview_id"]
    return metadata


def _exact_key(value):
    # Typography/case/diacritics are normalized, but no fuzzy or token-subset
    # match can authorize attaching another paper's abstract.
    value = unicodedata.normalize("NFKD", html.unescape(str(value))).casefold()
    return "".join(c for c in value if c.isalnum() and not unicodedata.combining(c))


def _openreview_id(url):
    parsed = urllib.parse.urlsplit(url or "")
    if parsed.hostname == "openreview.net" and parsed.path == "/forum":
        value = urllib.parse.parse_qs(parsed.query).get("id", [""])[0]
        return value if re.fullmatch(r"[A-Za-z0-9_-]+", value) else ""
    return ""


def _author_names_align(official, authors, forum_id):
    expected = [_exact_key(a) for a in official.get("authors", [])]
    actual = [_exact_key(a) for a in authors]
    if not expected or not all(actual) or len(expected) != len(actual):
        return False
    if sorted(expected) == sorted(actual):
        return True
    # PMLR and the virtual site sometimes use middle names, initials or profile
    # names differently. Relax those only when both official services link to
    # the EXACT same persistent OpenReview paper ID, never from a title alone.
    if not forum_id or official.get("openreview_id") != forum_id:
        return False
    def tokens(name):
        return [_exact_key(t) for t in re.findall(r"[^\W_]+", html.unescape(name), re.UNICODE)]
    remaining = [tokens(a) for a in authors]
    for name in official["authors"]:
        wanted = tokens(name)
        if len(wanted) < 2:
            return False
        candidates = [i for i, candidate in enumerate(remaining)
                      if len(candidate) >= 2 and candidate[-1] == wanted[-1]
                      and (candidate[0][0] == wanted[0][0]
                           or wanted[0] in candidate[:-1] or candidate[0] in wanted[:-1])]
        if len(candidates) != 1:
            return False
        remaining.pop(candidates[0])
    return not remaining


def match_bulk_metadata(payload, catalogue):
    """Return compact matching rows; duplicate titles and author drift fail closed."""
    rows = payload.get("results") if isinstance(payload, dict) else None
    if not isinstance(rows, list) or payload.get("next"):
        raise ValueError("Official virtual catalogue must be a complete results list")
    by_title = {}
    for url, official in catalogue.items():
        by_title.setdefault(_exact_key(official["title"]), []).append((url, official))
    matched = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        hits = by_title.get(_exact_key(row.get("name", "")), [])
        if len(hits) != 1:
            continue
        url, official = hits[0]
        author_rows = row.get("authors", [])
        authors = [a.get("fullname", "") for a in author_rows if isinstance(a, dict)]
        forum_id = _openreview_id(row.get("paper_url"))
        if not _author_names_align(official, authors, forum_id):
            continue
        if row.get("id") is None:
            continue
        compact = {"id": str(row["id"]), "pdf_url": row.get("paper_pdf_url") or ""}
        if forum_id:
            compact["openreview_id"] = forum_id
        if isinstance(row.get("abstract"), str):
            compact["abstract"] = row["abstract"]
        # Oral and poster rows can repeat a paper. Identical IDs are harmless;
        # distinct IDs with one title need per-paper evidence instead.
        if url not in matched:
            matched[url] = compact
        elif matched[url] is not None:
            previous = matched[url]
            if previous["id"] == compact["id"] or (forum_id and previous.get("openreview_id") == forum_id):
                if not previous.get("abstract") and compact.get("abstract"):
                    matched[url] = compact
            else:
                matched[url] = None
    return {url: row for url, row in matched.items() if row is not None}


def _download_bulk_chunk(client, url, bulk):
    """Resume bounded byte ranges; pin ETag so checkpoints never mix versions.

    Official static JSON files can exceed 26 MB and whole transfers have been
    observed to truncate. A 2 MB request finishes quickly and counts against the
    same source budget. Compressed private checkpoints retain completed chunks.
    """
    download = bulk.setdefault("download", {"url": url, "offset": 0, "chunks": []})
    if download.get("url") != url:
        download.clear()
        download.update(url=url, offset=0, chunks=[])
    offset = download["offset"]
    headers = {"Range": f"bytes={offset}-{offset + bulk_chunk_bytes() - 1}", "Accept-Encoding": "identity"}
    if download.get("etag"):
        headers["If-Range"] = download["etag"]
    response = client.get(url, headers=headers, return_metadata=True)
    body = response["body"]
    response_headers = {k.casefold(): v for k, v in response["headers"].items()}
    status = response["status"]
    if status == 200:
        # If-Range returns the complete replacement representation when the ETag
        # changed. It is safe to discard the old chunks and parse this snapshot.
        if len(body) > BULK_MAX_BYTES:
            raise ValueError("Official bulk dataset exceeds the safety limit")
        payload = json.loads(body.decode("utf-8"))
        bulk.pop("download", None)
        return payload
    match = re.fullmatch(r"bytes (\d+)-(\d+)/(\d+)", response_headers.get("content-range", ""))
    if status != 206 or not match:
        raise ValueError("Official bulk range response lacks a valid Content-Range")
    start, end, total = map(int, match.groups())
    etag = response_headers.get("etag", "")
    if start != offset or end - start + 1 != len(body) or total > BULK_MAX_BYTES or end >= total:
        raise ValueError("Official bulk byte range does not match the request")
    if not etag or etag.startswith("W/"):
        raise ValueError("Official bulk response lacks a strong ETag")
    if offset and (etag != download.get("etag") or total != download.get("total")):
        # Do not combine even a malicious/nonconforming 206 with an old version.
        bulk.pop("download", None)
        raise ValueError("Official bulk snapshot changed during download; restart next run")
    download["chunks"].append(base64.b64encode(zlib.compress(body)).decode("ascii"))
    download.update(offset=end + 1, total=total, etag=etag)
    if end + 1 < total:
        return None
    assembled = b"".join(zlib.decompress(base64.b64decode(chunk)) for chunk in download["chunks"])
    if len(assembled) != total:
        raise ValueError("Official bulk checkpoint byte count does not match total")
    payload = json.loads(assembled.decode("utf-8"))
    bulk.pop("download", None)
    return payload


def _consume_abstracts(catalogue, matches, abstracts, source, year, metadata_url, abstracts_url, seen, job, collector):
    records = []
    for url, row in matches.items():
        if url in seen:
            continue
        abstract = abstracts.get(row["id"])
        if not isinstance(abstract, str) or len(abstract.strip()) < 40:
            continue
        record = _bulk_record(url, catalogue[url], " ".join(abstract.split()), row, source, year, metadata_url, abstracts_url)
        seen.add(url)
        job.setdefault("failed", {}).pop(url, None)
        if record and helpers().date_overlaps(record["published"], collector.since.isoformat(), collector.until.isoformat()):
            records.append(record)
    job["seen"] = sorted(seen)
    return records


def _bulk_record(url, official, abstract, row, source, year, metadata_url, abstracts_url):
    api = helpers()
    categories = api.classify(official["title"], abstract)
    if not categories:
        return None
    return api.normalize_paper({
        "title": official["title"], "authors": official["authors"], "year": year,
        "published": str(year), "venue": SOURCES[source], "publication_status": "published",
        "categories": categories, "abstract": abstract, "summary_status": "pending",
        "source_url": url, "evidence_url": url, "verified_at": api.now(),
        "pdf_url": row.get("pdf_url", ""), "review_status": "source-confirmed",
        "abstract_source_url": abstracts_url,
        "source_records": api.source_record(SOURCES[source] + " official proceedings", url)
                          + api.source_record(SOURCES[source] + " official virtual catalogue", metadata_url)
                          + api.source_record(SOURCES[source] + " official abstract dataset", abstracts_url),
        "publication_date_basis": "Official conference edition; exact publication date not present in bulk metadata",
    })


def _bulk_step(source, year, job, seen, collector):
    """One request per turn; checkpoint metadata before fetching all abstracts.

    Return (attempted, records). A failed optional accelerator falls back to the
    existing detail queue without turning a successful source into an error.
    """
    catalogue = job.get("catalogue", {})
    if not catalogue or not any(p.get("authors") for p in catalogue.values()):
        return False, []
    fingerprint = hashlib.sha256(json.dumps(catalogue, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    bulk = job.setdefault("bulk", {})
    if bulk.get("catalogue_hash") != fingerprint:
        bulk.clear()
        bulk.update(catalogue_hash=fingerprint, phase="metadata")
    if bulk.get("phase") == "done" or bulk.get("failed_on") == helpers().now()[:10]:
        return False, []
    if not collector.budget():
        return None, []
    base = f"https://{VIRTUAL_HOSTS[source]}/static/virtual/data/{SOURCES[source].lower()}-{year}"
    metadata_url, abstracts_url = base + "-orals-posters.json", base + "-abstracts.json"
    phase = bulk.get("phase", "metadata")
    request_url = metadata_url if phase == "metadata" else abstracts_url
    try:
        payload = _download_bulk_chunk(collector.client, request_url, bulk)
        if payload is None:
            return True, []
        if phase == "metadata":
            matches = match_bulk_metadata(payload, catalogue)
            if not matches:
                raise ValueError("No author-aligned official catalogue matches in virtual metadata")
            inline = {row["id"]: row.pop("abstract") for row in matches.values() if "abstract" in row}
            records = _consume_abstracts(catalogue, matches, inline, source, year, metadata_url, metadata_url, seen, job, collector)
            missing = {url: row for url, row in matches.items() if url not in seen}
            bulk.update(phase="abstracts" if missing else "done", matches=missing, matched=len(matches))
            if not missing:
                bulk.pop("matches", None)
                bulk["completed_at"] = helpers().now()
            return True, records
        if not isinstance(payload, dict) or not payload:
            raise ValueError("Official abstract dataset is empty or malformed")
        records = _consume_abstracts(catalogue, bulk.get("matches", {}), payload, source, year, metadata_url, abstracts_url, seen, job, collector)
        bulk.update(phase="done", scanned=len(bulk.get("matches", {})), completed_at=helpers().now())
        bulk.pop("matches", None)
        bulk.pop("last_error", None)
        return True, records
    except TimeoutError:
        raise
    except Exception as exc:
        bulk.update(failed_on=helpers().now()[:10], last_error=type(exc).__name__)
        LOG.warning("Official bulk metadata unavailable for %s %s (%s); continuing individual proceedings pages", source, year, type(exc).__name__)
        return True, []


def parse_paper(text, url, source, year):
    api = helpers()
    expected_host = "proceedings.mlr.press" if source == "pmlr" else f"proceedings.{source}.cc"
    if urllib.parse.urlsplit(url).hostname != expected_host:
        raise ValueError("Publication evidence is not hosted by the official proceedings")
    doc = document(text)
    m = doc.meta
    title = m.get("citation_title", [""])[0].strip()
    authors = m.get("citation_author", [])
    container = " ".join(value for key in ("citation_journal_title", "citation_conference_title", "citation_inbook_title") for value in m.get(key, []))
    if not title or not any(authors) or api.canonical_venue(container) != SOURCES[source]:
        raise ValueError("Missing or mismatched official publication metadata: " + url)
    # The page must belong to the official accepted catalogue; submission status
    # text on another service can never establish publication here.
    if source != "pmlr" and f"/paper/{year}/hash/" not in urllib.parse.urlsplit(url).path:
        raise ValueError("Unexpected proceedings year/path")
    abstract = " ".join(doc.abstract).strip()
    abstract = " ".join(abstract.split())
    categories = api.classify(title, abstract)
    if not categories:
        return None
    date = m.get("citation_publication_date", [str(year)])[0].replace("/", "-")
    if not re.fullmatch(r"\d{4}(?:-\d{1,2}){0,2}", date):
        date = str(year)
    date = "-".join([date.split("-")[0]] + [f"{int(x):02d}" for x in date.split("-")[1:]])
    # NeurIPS 2025 HTML was deposited in 2026. Preserve the conference edition;
    # never silently relabel its papers as NeurIPS 2026.
    published = date if date.startswith(str(year)) else str(year)
    clean_authors = []
    for author in authors:
        if not author.strip():
            continue
        if "," in author:
            family, given = author.split(",", 1)
            author = given.strip() + " " + family.strip()
        clean_authors.append(author.strip())
    record = {"title": title, "authors": clean_authors, "year": year, "published": published,
              "venue": SOURCES[source], "venue_full": container, "publication_status": "published",
              "categories": categories, "abstract": abstract, "summary_status": "pending",
              "source_url": url, "evidence_url": url, "verified_at": api.now(),
              "pdf_url": m.get("citation_pdf_url", [""])[0], "doi": m.get("citation_doi", [""])[0],
              "source_records": api.source_record(SOURCES[source] + " official proceedings", url),
              "review_status": "source-confirmed", "publisher_record_date": date,
              "publication_date_basis": "Official conference edition; publisher HTML deposit date retained separately"}
    if "Datasets_and_Benchmarks" in url:
        record["track"] = "Datasets and Benchmarks"
    if any(not a.strip() for a in authors):
        record["metadata_warnings"] = ["Official citation metadata contains empty author entries; author list may need verification"]
    return api.normalize_paper(record)


def _error(collector, job, url, exc):
    api = helpers()
    message = f"{type(exc).__name__}: {str(exc)[:240]}"
    collector.complete = False
    if not hasattr(collector, "source_errors"):
        collector.source_errors = []
    collector.source_errors.append({"url": url, "error": message})
    job["last_error"] = {"url": url, "error": message, "at": api.now()}
    LOG.warning("Official proceedings collection failed for %s: %s", url, message)


def _pmlr_volumes(collector):
    """Known volumes work offline; discover future ICML editions from PMLR."""
    volumes = dict(PMLR_VOLUMES)
    saved = collector.state.setdefault("ai_venue_volumes", {})
    volumes.update({int(y): str(v) for y, v in saved.items()})
    missing = [y for y in range(max(2025, collector.since.year), collector.until.year + 1) if y not in volumes]
    if missing:
        if not collector.budget():
            return volumes
        url = "https://proceedings.mlr.press/"
        try:
            doc = document(collector.client.get(url))
            found = {}
            for href, label in doc.list_items:
                match = re.search(r"\bICML\s+(20\d\d)\b", label, re.I)
                volume = re.search(r"(?:^|/)v(\d+)/?$", href)
                if match and volume and "workshop" not in label.casefold():
                    found[int(match.group(1))] = volume.group(1)
            if not found:
                raise ValueError("PMLR volume directory did not expose any ICML editions")
            volumes.update(found)
            saved.update({str(y): v for y, v in found.items()})
        except TimeoutError:
            raise
        except Exception as exc:
            _error(collector, {}, url, exc)
    return volumes


def accepted_neurips_rows(payload, year):
    """Only explicit decisions in the official main/evaluation track qualify."""
    rows = payload.get("results") if isinstance(payload, dict) else None
    if not isinstance(rows, list) or payload.get("next") or payload.get("count", len(rows)) != len(rows):
        raise ValueError("Incomplete official accepted programme")
    allowed = {f"NeurIPS.cc/{year}/Conference": "Main Conference",
               f"NeurIPS.cc/{year}/Evaluations_and_Datasets_Track": "Evaluations and Datasets"}
    result, conflicting = {}, set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        group = urllib.parse.urlsplit(row.get("sourceurl") or "")
        track = allowed.get(urllib.parse.parse_qs(group.query).get("id", [""])[0])
        decision = row.get("decision") or ""
        identity = str(row.get("id", ""))
        path = row.get("virtualsite_url") or ""
        authors = [a.get("fullname", "").strip() for a in row.get("authors", []) if isinstance(a, dict)]
        title = str(row.get("name") or "").strip()
        if (group.scheme != "https" or group.hostname != "openreview.net" or group.path != "/group"
                or not track or not re.fullmatch(r"Accept(?: \((?:poster|oral|spotlight)\))?", decision, re.I)
                or not identity.isdigit() or not re.fullmatch(rf"/virtual/{year}/(?:poster|oral)/{identity}", path)
                or not title or not authors or not all(authors)):
            continue
        compact = {"id": identity, "title": title, "authors": authors, "decision": decision,
                   "venue_track": track, "url": "https://neurips.cc" + path,
                   "paper_url": row.get("paper_url") or "", "pdf_url": row.get("paper_pdf_url") or ""}
        signature = (_exact_key(title), tuple(sorted(_exact_key(a) for a in authors)))
        if identity in result and result[identity]["signature"] != signature:
            conflicting.add(identity)
        compact["signature"] = signature
        result[identity] = compact
    for identity in conflicting:
        result.pop(identity, None)
    for row in result.values():
        row.pop("signature", None)
    return result


def accepted_neurips_record(row, abstract, year, metadata_url, abstracts_url):
    api = helpers()
    categories = api.classify(row["title"], abstract)
    if not categories:
        return None
    arxiv = next((api.clean_arxiv(url) for url in (row.get("paper_url"), row.get("pdf_url"))
                  if urllib.parse.urlsplit(url or "").hostname in ("arxiv.org", "export.arxiv.org")), "")
    return api.normalize_paper({
        "title": row["title"], "authors": row["authors"], "year": year, "published": str(year),
        "venue": "NeurIPS", "publication_status": "accepted", "accepted_venue": "NeurIPS",
        "accepted_year": year, "acceptance_basis": "official", "venue_track": row["venue_track"],
        "acceptance_evidence": [{"url": row["url"], "kind": "official-program", "quote": row["decision"]}],
        "acceptance_note": f"NeurIPS {year} 官方会议目录确认录用（{row['venue_track']}）；本次未取得该届正式论文集记录，出版状态待后续核验。",
        "categories": categories, "abstract": abstract, "summary_status": "pending", "arxiv_id": arxiv,
        "source_url": row["url"], "evidence_url": row["url"], "verified_at": api.now(),
        "pdf_url": row.get("pdf_url", ""), "review_status": "acceptance-confirmed",
        "publication_date_basis": "accepted-conference-edition-only",
        "publication_date_note": "日期暂记录用会议届次，预印本首次公开日期待补充；不代表正式出版日期。",
        "source_records": api.source_record("NeurIPS official accepted programme", metadata_url)
                          + api.source_record("NeurIPS official abstract dataset", abstracts_url),
    })


def _accepted_neurips_step(year, job, collector):
    """One budgeted transfer per turn, with resumable JSON and detail fallback."""
    today = helpers().now()[:10]
    bulk = job.setdefault("accepted_bulk", {"phase": "index"})
    if job.get("accepted_detail_day") != today:
        job.update(accepted_detail_day=today, accepted_detail_turns=0)
    refresh = bulk.get("phase") == "done" or (bulk.get("phase") == "details" and job.get("accepted_detail_turns", 0) >= 2)
    if refresh and bulk.get("refreshed_on") != today:
        bulk.clear()
        bulk["phase"] = "index"
    if bulk.get("phase") == "done":
        job["done"] = not bool(job.get("accepted_unresolved"))
        if not job["done"]:
            collector.complete = False
        return False, []
    if not collector.budget():
        return None, []
    base = f"https://neurips.cc/static/virtual/data/neurips-{year}"
    metadata_url, abstracts_url = base + "-orals-posters.json", base + "-abstracts.json"
    phase = bulk.get("phase", "index")
    url = f"https://neurips.cc/virtual/{year}/papers.html" if phase == "index" else metadata_url if phase == "metadata" else abstracts_url
    try:
        if phase == "index":
            catalogue = {}
            for href, title in document(collector.client.get(url)).links:
                parts = urllib.parse.urlsplit(urllib.parse.urljoin(url, href))
                match = re.fullmatch(rf"/virtual/{year}/poster/(\d+)", parts.path)
                if parts.hostname == "neurips.cc" and match and title:
                    catalogue[match.group(1)] = title
            if not catalogue:
                raise ValueError("No official poster directory entries parsed")
            job["accepted_catalogue"] = catalogue
            job["done"] = False
            job.pop("accepted_status", None)
            bulk["phase"] = "metadata"
            return True, []
        if phase == "details":
            queue = job.get("accepted_missing", [])
            if not queue:
                bulk["phase"] = "done"
                job["done"] = not bool(job.get("accepted_unresolved"))
                if not job["done"]:
                    collector.complete = False
                return False, []
            row = queue[0]
            url = row["url"]
            job["accepted_detail_turns"] += 1
            detail = collector.client.get(url)
            doc = document(detail)
            structured = re.search(r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>', detail, re.S | re.I)
            if structured:
                metadata = json.loads(structured.group(1))
                if not isinstance(metadata, dict) or _exact_key(metadata.get("name", "")) != _exact_key(row["title"]):
                    raise ValueError("Official poster title does not match accepted programme")
            abstract = " ".join(" ".join(doc.abstract).split())
            if len(abstract) < 40:
                raise ValueError("Official accepted abstract unavailable; retain pending detail")
            record = accepted_neurips_record(row, abstract, year, metadata_url, url)
            queue.pop(0)
            job.setdefault("accepted_detail_seen", []).append(row["id"])
            return True, [record] if record else []
        payload = _download_bulk_chunk(collector.client, url, bulk)
        if payload is None:
            return True, []
        if phase == "metadata":
            rows = accepted_neurips_rows(payload, year)
            catalogue = job.get("accepted_catalogue", {})
            rows = {identity: row for identity, row in rows.items()
                    if identity in catalogue and _exact_key(catalogue[identity]) == _exact_key(row["title"])}
            if not rows:
                raise ValueError("No explicit official main-track acceptances parsed")
            represented = {str(row.get("id")) for row in payload["results"] if isinstance(row, dict)}
            job["accepted_unresolved"] = {identity: title for identity, title in catalogue.items() if identity not in represented}
            bulk.update(phase="abstracts", rows=rows)
            return True, []
        if not isinstance(payload, dict) or not payload:
            raise ValueError("Official accepted abstract map is empty")
        records, missing = [], []
        seen = set(job.get("accepted_detail_seen", []))
        for row in bulk.get("rows", {}).values():
            abstract = payload.get(row["id"])
            if not isinstance(abstract, str) or len(abstract.strip()) < 40:
                if row["id"] not in seen:
                    missing.append(row)
                continue
            record = accepted_neurips_record(row, " ".join(abstract.split()), year, metadata_url, abstracts_url)
            if record:
                records.append(record)
        missing.sort(key=lambda row: (not bool(helpers().classify(row["title"])), row["title"].casefold()))
        job.update(accepted_missing=missing, accepted_total=len(bulk.get("rows", {})),
                   accepted_abstracts_pending=len(missing), indexed_at=helpers().now())
        bulk.pop("rows", None)
        bulk.update(phase="details" if missing else "done", refreshed_on=today)
        return True, records
    except TimeoutError:
        raise
    except Exception as exc:
        if phase == "details" and job.get("accepted_missing"):
            job["accepted_missing"].append(job["accepted_missing"].pop(0))
        # Only an unseen programme may legitimately be not yet public. Once
        # its directory exists, missing metadata or a failed directory refresh
        # is incomplete collection, not evidence that there is nothing to read.
        if getattr(exc, "code", None) == 404 and phase == "index" and not job.get("accepted_catalogue"):
            bulk.update(phase="done", refreshed_on=today)
            job.update(done=True, accepted_status="not-yet-public")
        else:
            job["done"] = False
            job.pop("accepted_status", None)
            _error(collector, job, url, exc)
        return phase == "details", []


def collect(source, collector):
    """Yield normalized papers; all HTTP requests consume Collector.budget()."""
    if source not in SOURCES:
        raise ValueError("Unknown official AI proceedings source: " + source)
    api = helpers()
    today = api.now()[:10]
    volumes = _pmlr_volumes(collector) if source == "pmlr" else {}
    active = []
    for year in range(collector.until.year, max(2025, collector.since.year) - 1, -1):
        if source == "pmlr":
            if year not in volumes:
                collector.complete = False
                continue
            url = f"https://proceedings.mlr.press/v{volumes[year]}/"
        else:
            url = f"https://proceedings.{source}.cc/paper_files/paper/{year}"
        job = collector.job(f"ai-proceedings:{source}:{year}")
        url = job.get("resolved_index_url", url)
        if job.get("indexed_at", "")[:10] != today or not job.get("catalogue"):
            if not collector.budget():
                return
            try:
                text = collector.client.get(url)
                try:
                    official = parse_catalogue(text, url, source, year)
                except ValueError:
                    # New NeurIPS editions expose a book chooser before the
                    # accepted-paper list. Follow only the main proceedings;
                    # never follow workshop or submission listings.
                    books = [urllib.parse.urljoin(url, href) for href, _ in document(text).links
                             if source == "neurips" and re.search(rf"/paper/{year}/vol\d+-main-conference/?$", urllib.parse.urljoin(url, href))
                             and urllib.parse.urlsplit(urllib.parse.urljoin(url, href)).hostname == "proceedings.neurips.cc"]
                    if not books:
                        raise
                    url = books[0]
                    job["resolved_index_url"] = url
                    if not collector.budget():
                        return
                    text = collector.client.get(url)
                    official = parse_catalogue(text, url, source, year)
                catalogue = {link: entry["title"] for link, entry in official.items()}
                seen = set(job.get("seen", []))
                old_queue = job.get("queue", [])
                old_cursor = min(job.get("cursor", 0), len(old_queue))
                remaining = old_queue[old_cursor:]
                pending = set(remaining)
                # New relevant titles go first. All other accepted titles remain
                # queued so relevant abstracts with generic titles are not lost.
                new = [u for u in catalogue if u not in seen and u not in pending]
                new.sort(key=lambda u: (not bool(api.classify(catalogue[u])), catalogue[u].casefold()))
                queue = list(dict.fromkeys(new + remaining))
                queue.sort(key=lambda u: not bool(api.classify(catalogue.get(u, ""))))
                # Keep failed/disappeared URLs for retries; never discard old work.
                queue.extend(u for u in job.get("failed", {}) if u not in seen and u not in queue)
                job.update(queue=queue, cursor=0, index_url=url, indexed_at=api.now(), total=len(catalogue), catalogue=official, done=False)
            except TimeoutError:
                raise
            except Exception as exc:
                known_accepted = collector.jobs.get(f"ai-accepted:neurips:{year}") if source == "neurips" else None
                if getattr(exc, "code", None) == 404 and (year == collector.until.year or known_accepted) and not job.get("queue") and not job.get("seen"):
                    job.update(index_status="not-published", checked_at=api.now(), done=True)
                    if source == "neurips":
                        accepted_job = collector.job(f"ai-accepted:neurips:{year}")
                        accepted_job["accepted_mode"] = True
                        active.append((year, accepted_job, set()))
                    continue
                # Existing queue/cursor/seen/indexed_at stay intact on failure.
                _error(collector, job, url, exc)
        seen = set(job.get("seen", []))
        active.append((year, job, seen))
    # Fair backfill: one detail from each annual queue per round.
    turns = collector.state.setdefault("ai_venue_next_year", {})
    next_year = turns.get(source)
    if next_year in [item[0] for item in active]:
        start = next(i for i, item in enumerate(active) if item[0] == next_year)
        active = active[start:] + active[:start]
    while active:
        next_active = []
        for position, (year, job, seen) in enumerate(active):
            if job.get("accepted_mode"):
                attempted, records = _accepted_neurips_step(year, job, collector)
                yield from records
                if attempted is None:
                    return
                if attempted:
                    next_active.append((year, job, seen))
                continue
            queue = job.get("queue", [])
            cursor = job.get("cursor", 0)
            while cursor < len(queue) and queue[cursor] in seen:
                cursor += 1
            job["cursor"] = cursor
            if cursor >= len(queue):
                job["done"] = bool(job.get("indexed_at")) and not job.get("failed")
                if not job["done"]:
                    collector.complete = False
                continue
            attempted, bulk_records = _bulk_step(source, year, job, seen, collector)
            if attempted is None:
                return
            if attempted:
                turns[source] = active[(position + 1) % len(active)][0]
                job["updated_at"] = api.now()
                next_active.append((year, job, seen))
                yield from bulk_records
                continue
            if not collector.budget():
                return
            link = queue[cursor]
            try:
                paper = parse_paper(collector.client.get(link), link, source, year)
            except TimeoutError:
                raise
            except Exception as exc:
                _error(collector, job, link, exc)
                job.setdefault("failed", {})[link] = {"at": api.now(), "error": type(exc).__name__}
            else:
                seen.add(link)
                job["seen"] = sorted(seen)
                job.setdefault("failed", {}).pop(link, None)
                if paper and api.date_overlaps(paper["published"], collector.since.isoformat(), collector.until.isoformat()):
                    yield paper
            job.update(cursor=cursor + 1, updated_at=api.now())
            turns[source] = active[(position + 1) % len(active)][0]
            next_active.append((year, job, seen))
        active = next_active
