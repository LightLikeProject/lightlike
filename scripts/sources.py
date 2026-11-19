#!/usr/bin/env python3
"""Verify the literature sources of the task board against the publishers' records.

  python3 scripts/sources.py verify [KEY ...]   fetch every reference (or the named ones), write
                                                docs/tasks/sources-verified.json and the report
  python3 scripts/sources.py check              offline: every reference in docs/tasks/sources.yaml
                                                has a passing record in sources-verified.json
  python3 scripts/sources.py find ARXIV WORD..   where the words occur in the arXiv full text, with
                                                the nearest preceding theorem-like label
  python3 scripts/sources.py chapters DOI N M    titles of chapters N..M of a book with chapter DOIs
  python3 scripts/sources.py search TEXT         arXiv and Crossref records matching a title/author query

A reference exists when its arXiv ID (arXiv API), DOI (Crossref) or ISBN (Open Library) resolves
to a record whose title matches the one recorded in sources.yaml. A location (for example
"Theorem 5.9" or "eq. (2.10)") is verified when it appears in the arXiv full text with one of
the reference's keywords near it; locations in books without an arXiv version stay unverified
and are reported as such. Citation counts come from OpenAlex (DOI) or Semantic Scholar (arXiv).
"""
import argparse
import datetime
import json
import re
import subprocess
import sys
import tempfile
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import api_map  # noqa: E402

SOURCES = ROOT / "docs/tasks/sources.yaml"
VERIFIED = ROOT / "docs/tasks/sources-verified.json"
UA = "lightlike-source-check/0.1 (https://github.com/LightlikeProject/lightlike)"
ATOM = "{http://www.w3.org/2005/Atom}"
LABELS = ("Theorem", "Lemma", "Proposition", "Corollary", "Definition", "Conjecture", "Example",
          "Remark", "Section", "Chapter", "Appendix", "Table", "Figure")


def norm(s):
    s = re.sub(r"[\u2010-\u2015\u2212]", "-", unicodedata.normalize("NFKD", s or ""))
    s = s.encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]+", " ", s).strip()


def title_ok(want, got):
    """Every word of the recorded title (beyond very short ones) occurs in the fetched title."""
    w = [x for x in norm(want).split() if len(x) > 2]
    g = set(norm(got).split())
    return bool(w) and sum(x in g for x in w) >= max(1, round(0.8 * len(w)))


def get(url, accept=None, tries=4):
    for i in range(tries):
        req = urllib.request.Request(url, headers={"User-Agent": UA, **({"Accept": accept} if accept else {})})
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            if e.code in (429, 500, 502, 503, 504) and i + 1 < tries:
                time.sleep(5 * (i + 1))
                continue
            raise
        except (urllib.error.URLError, TimeoutError):
            if i + 1 < tries:
                time.sleep(5 * (i + 1))
                continue
            raise
    return None


def arxiv_meta(ids):
    out = {}
    ids = sorted(set(ids))
    for k in range(0, len(ids), 50):
        chunk = ids[k:k + 50]
        q = urllib.parse.urlencode({"id_list": ",".join(chunk), "max_results": len(chunk)})
        root = ET.fromstring(get("https://export.arxiv.org/api/query?" + q))
        for e in root.findall(ATOM + "entry"):
            aid = (e.findtext(ATOM + "id") or "").split("/abs/")[-1]
            aid = re.sub(r"v\d+$", "", aid)
            title = " ".join((e.findtext(ATOM + "title") or "").split())
            if title and title != "Error":
                out[aid] = {"title": title, "authors": [a.findtext(ATOM + "name") for a in e.findall(ATOM + "author")],
                            "year": (e.findtext(ATOM + "published") or "")[:4],
                            "abstract": " ".join((e.findtext(ATOM + "summary") or "").split())}
        time.sleep(3)
    return out


def crossref(doi):
    raw = get("https://api.crossref.org/works/" + urllib.parse.quote(doi))
    if not raw:
        return None
    m = json.loads(raw)["message"]
    year = (m.get("issued", {}).get("date-parts") or [[None]])[0][0]
    title = " ".join(m.get("title") or []) + " " + " ".join(m.get("subtitle") or [])
    return {"title": re.sub(r"<[^>]+>", "", title),  # Crossref marks up symbols: 6<i>j</i>
            "authors": [a.get("family", "") for a in m.get("author", [])], "year": str(year or ""),
            "abstract": re.sub(r"<[^>]+>", " ", m.get("abstract") or "")}


def openlibrary(isbn):
    raw = get(f"https://openlibrary.org/isbn/{isbn}.json")
    if not raw:
        return None
    m = json.loads(raw)
    return {"title": (m.get("title", "") + " " + m.get("subtitle", "")).strip(), "authors": [],
            "year": re.sub(r"\D", "", m.get("publish_date", ""))[-4:]}


def citations(ref):
    try:
        if ref.get("doi"):
            raw = get("https://api.openalex.org/works/https://doi.org/" + urllib.parse.quote(ref["doi"]))
            if raw:
                return json.loads(raw).get("cited_by_count"), "OpenAlex"
        if ref.get("arxiv"):
            try:
                raw = get(f"https://api.semanticscholar.org/graph/v1/paper/arXiv:{ref['arxiv']}?fields=citationCount")
            except urllib.error.HTTPError:  # rate-limited: fall back to OpenAlex below
                raw = None
            time.sleep(3)
            if raw and json.loads(raw).get("citationCount") is not None:
                return json.loads(raw)["citationCount"], "Semantic Scholar"
            raw = get("https://api.openalex.org/works/https://doi.org/10.48550/arXiv." + ref["arxiv"])
            if raw:
                return json.loads(raw).get("cited_by_count"), "OpenAlex"
    except Exception as e:  # citation data is a ranking aid, never a verification result
        return None, f"unavailable ({type(e).__name__})"
    return None, "unavailable"


def fulltext(aid, cache):
    """The paper's text twice: in page layout (one-column papers) and in reading order (two-column)."""
    f = cache / (aid.replace("/", "_") + ".both.txt")
    if not f.exists():
        p = cache / (aid.replace("/", "_") + ".pdf")
        if not p.exists():
            pdf = get(f"https://arxiv.org/pdf/{aid}")
            if not pdf:
                return None
            p.write_bytes(pdf)
            time.sleep(3)
        parts = []
        for mode in (["-layout"], []):
            r = subprocess.run(["pdftotext", *mode, str(p), "-"], check=False, capture_output=True)
            parts.append(r.stdout.decode(errors="ignore"))
        f.write_text("\n\f\n".join(parts))
    return f.read_text(errors="ignore")


def location_pattern(loc):
    """A regex for the label of a location such as 'Theorem 5.9', 'eq. (2.10)' or '§4.2'."""
    m = re.match(r"\s*(?:eqs?\.?|equations?)\s*\(?([0-9A-Za-z.]+)\)?", loc, re.I)
    if m:
        return r"\(\s*" + re.escape(m.group(1)) + r"\s*\)"
    m = re.match(r"\s*§\s*([0-9.]+)", loc)
    if m:
        return r"(?m)^\s*" + re.escape(m.group(1)) + r"\.?\s+[A-Z]"
    for lab in LABELS:
        m = re.match(r"\s*" + lab + r"s?\.?\s+([0-9A-Z][0-9A-Z.]*[0-9A-Za-z]?)", loc, re.I)
        if m:
            if lab in ("Section", "Chapter", "Appendix"):
                return r"(?m)^\s*(?:" + lab + r"\s+)?" + re.escape(m.group(1)) + r"\.?\s+[A-Z]"
            return lab + r"\s*" + re.escape(m.group(1)) + r"\b"
    return None


def check_location(text, loc, keywords):
    pat = location_pattern(loc)
    if not text or not pat:
        return False, None
    t = " ".join(text.split()) if not pat.startswith("(?m)") else text
    kws = [norm(k) for k in keywords or []]
    for m in re.finditer(pat, t):
        window = norm(t[max(0, m.start() - 300): m.end() + 1500])
        if not kws or any(k in window for k in kws):
            snippet = " ".join(t[m.start(): m.start() + 220].split())
            return True, snippet
    return False, None


LABEL_RE = re.compile(r"\b(" + "|".join(LABELS[:8]) + r")\s+([0-9]+(?:\.[0-9]+)*)")


def cmd_find(aid, words, limit=12):
    cache = Path(tempfile.gettempdir()) / "lightlike-sources"
    cache.mkdir(exist_ok=True)
    meta = arxiv_meta([aid]).get(aid)
    print("title:", meta and meta["title"])
    text = fulltext(aid, cache)
    if not text:
        print("no full text")
        return
    t = " ".join(text.split())
    n = 0
    for w in words:
        for m in re.finditer(re.escape(w), t, re.I):
            labs = list(LABEL_RE.finditer(t, max(0, m.start() - 2500), m.start()))
            lab = f"{labs[-1].group(1)} {labs[-1].group(2)}" if labs else "-"
            eq = re.search(r"\((\d+(?:\.\d+)?[a-z]?)\)", t[m.start(): m.start() + 600])
            print(f"[{w}] near {lab}, eq {eq.group(1) if eq else '-'}: {t[max(0, m.start() - 60): m.start() + 110]}")
            n += 1
            if n >= limit:
                return


HEAD_RE = re.compile(r"(?m)^\s{0,8}((?:[0-9]+(?:\.[0-9]+){0,2}|[IVX]+|[A-H])\.?)\s{1,4}([A-Z][^\n.]{3,70})$")


def cmd_sections(aid):
    """Print the numbered headings of an arXiv paper, to choose a section as a location."""
    cache = Path(tempfile.gettempdir()) / "lightlike-sources"
    cache.mkdir(exist_ok=True)
    text = fulltext(aid, cache) or ""
    seen, out = set(), []
    for m in HEAD_RE.finditer(text):
        num, head = m.group(1).rstrip("."), " ".join(m.group(2).split())
        if num not in seen and len(out) < 40:
            seen.add(num)
            out.append(f"{num} {head[:45]}")
    print(" | ".join(out))


def cmd_search(text):
    q = urllib.parse.urlencode({"search_query": "all:" + " AND all:".join(text.split()), "max_results": 5})
    root = ET.fromstring(get("https://export.arxiv.org/api/query?" + q))
    for e in root.findall(ATOM + "entry"):
        aid = re.sub(r"v\d+$", "", (e.findtext(ATOM + "id") or "").split("/abs/")[-1])
        au = ", ".join(a.findtext(ATOM + "name") for a in e.findall(ATOM + "author")[:3])
        print(f"arXiv:{aid} | {' '.join((e.findtext(ATOM + 'title') or '').split())[:110]} | {au} | "
              f"{(e.findtext(ATOM + 'published') or '')[:4]}")
    raw = get("https://api.crossref.org/works?" + urllib.parse.urlencode({"query.bibliographic": text, "rows": 5}))
    for m in json.loads(raw)["message"]["items"] if raw else []:
        year = (m.get("issued", {}).get("date-parts") or [[None]])[0][0]
        au = ", ".join(a.get("family", "") for a in m.get("author", [])[:3])
        print(f"doi:{m.get('DOI')} | {' '.join(m.get('title') or [])[:110]} | {au} | {year} | {m.get('type')}")


def cmd_chapters(doi, a, b):
    for i in range(int(a), int(b) + 1):
        got = crossref(doi.format(i=i) if "{i" in doi else f"{doi}_{i}")
        print(i, got and got["title"])


class _NoDupLoader(yaml.SafeLoader):
    """A YAML loader that rejects duplicate keys, which safe_load would silently overwrite."""

    def construct_mapping(self, node, deep=False):
        seen = set()
        for k, _ in node.value:
            key = self.construct_object(k, deep=deep)
            if key in seen:
                raise yaml.constructor.ConstructorError(None, None, f"duplicate key {key!r}", k.start_mark)
            seen.add(key)
        return super().construct_mapping(node, deep)


def load():
    data = yaml.load(SOURCES.read_text(), Loader=_NoDupLoader) or {}
    return data.get("references") or {}, data


def cmd_verify(keys):
    refs, _ = load()
    old = json.loads(VERIFIED.read_text()) if VERIFIED.exists() else {}
    todo = {k: v for k, v in refs.items() if not keys or k in keys}
    meta = arxiv_meta([r["arxiv"] for r in todo.values() if r.get("arxiv")])
    today = datetime.date.today().isoformat()
    cache = Path(tempfile.gettempdir()) / "lightlike-sources"
    cache.mkdir(exist_ok=True)
    locs = location_uses()
    for k, r in todo.items():
        rec = {"checked": today, "exists": False, "via": None, "fetched_title": None, "locations": {}}
        got = None
        if r.get("arxiv"):
            got, rec["via"] = meta.get(r["arxiv"]), "arXiv API"
        if not got and r.get("doi"):
            got, rec["via"] = crossref(r["doi"]), "Crossref"
        if not got and r.get("isbn"):
            got, rec["via"] = openlibrary(r["isbn"]), "Open Library"
        if got:
            rec["fetched_title"] = got["title"]
            rec["exists"] = title_ok(r["title"], got["title"])
        rec["citations"], rec["citations_via"] = citations(r)
        if rec["citations"] is None and old.get(k, {}).get("citations") is not None:  # rate-limited: keep the last count
            rec["citations"], rec["citations_via"] = old[k]["citations"], old[k].get("citations_via")
        text = fulltext(r["arxiv"], cache) if r.get("arxiv") and rec["exists"] else None
        for loc in sorted(locs.get(k, {})):
            if "|" in loc:  # "Chapter 7|10.1007/...-8_7": a chapter with its own DOI
                cdoi = loc.split("|", 1)[1].strip()
                got_c = crossref(cdoi)
                snip = got_c and got_c["title"]
                ok = bool(snip) and norm(snip) in norm(loc.split("|", 1)[0])
                why = None if ok else ("chapter DOI not found" if not got_c else "chapter title differs")
                rec["locations"][loc] = {"verified": ok, "snippet": snip, "why": why}
                continue
            if loc.strip().lower() == "abstract":  # the abstract states the result
                ab = norm((got or {}).get("abstract"))
                kws = [norm(w) for w in sorted(locs[k][loc])]
                ok = bool(ab) and all(w in ab for w in kws)
                rec["locations"][loc] = {"verified": ok, "snippet": ab[:200] or None,
                                         "why": None if ok else ("no abstract" if not ab else "check word not in abstract")}
                continue
            ok, snip = check_location(text, loc, sorted(locs[k][loc]) or r.get("keywords"))
            rec["locations"][loc] = {"verified": ok, "snippet": snip,
                                     "why": None if ok else ("no arXiv full text" if not text else "label not found")}
        old[k] = rec
        print(f"{'ok ' if rec['exists'] else 'FAIL'} {k}: {rec['via']}: {rec['fetched_title']!s:.90}  "
              f"loc {sum(v['verified'] for v in rec['locations'].values())}/{len(rec['locations'])}  cites {rec['citations']}")
    # Re-read before writing, so that a concurrent run's results for other keys are kept.
    now = json.loads(VERIFIED.read_text()) if VERIFIED.exists() else {}
    now.update({k: old[k] for k in todo})
    VERIFIED.write_text(json.dumps(dict(sorted(now.items())), indent=1, ensure_ascii=False) + "\n")


def location_uses():
    _, data = load()
    uses = {}
    for m in (data.get("milestones") or {}).values():
        for r in m.get("refs") or []:
            if r.get("location"):
                uses.setdefault(r["ref"], {}).setdefault(r["location"], set()).update(
                    [r["check"]] if r.get("check") else [])
    for e in api_map.load(ROOT):
        for r in (e.get("source") or {}).get("refs", []) if isinstance(e.get("source"), dict) else []:
            if r.get("location"):
                uses.setdefault(r["ref"], {}).setdefault(r["location"], set()).update(
                    [r["check"]] if r.get("check") else [])
    return uses


def cmd_check():
    refs, data = load()
    ver = json.loads(VERIFIED.read_text()) if VERIFIED.exists() else {}
    errs = []
    for k, r in refs.items():
        for f in ("cite", "title"):
            if not r.get(f):
                errs.append(f"{k}: missing {f}")
        if not (r.get("arxiv") or r.get("doi") or r.get("isbn")):
            errs.append(f"{k}: needs an arXiv ID, DOI or ISBN to be verifiable")
        if not (ver.get(k) or {}).get("exists"):
            errs.append(f"{k}: not verified (run `python3 scripts/sources.py verify {k}`)")
    for area, keys in (data.get("canonical") or {}).items():
        for k in keys:
            if k not in refs:
                errs.append(f"canonical {area}: unknown reference {k}")
    for mid, m in (data.get("milestones") or {}).items():
        if m.get("class") not in ("sourced", "exploratory"):
            errs.append(f"milestone {mid}: class must be sourced or exploratory")
        if m.get("class") == "sourced" and not m.get("refs"):
            errs.append(f"milestone {mid}: a sourced milestone lists refs")
        for r in m.get("refs") or []:
            if r.get("ref") not in refs:
                errs.append(f"milestone {mid}: unknown reference {r.get('ref')}")
            if not r.get("location"):
                errs.append(f"milestone {mid}: reference {r.get('ref')} needs a location")
            elif not ((ver.get(r.get("ref")) or {}).get("locations", {}).get(r["location"]) or {}).get("verified"):
                errs.append(f"milestone {mid}: location {r['location']!r} in {r.get('ref')} not verified")
    results = api_map.load(ROOT)
    for e in results:
        src, rid = e.get("source"), e.get("id")
        if src in ("structural", "exploratory"):
            continue
        if not isinstance(src, dict) or not src.get("refs"):
            errs.append(f"result {rid}: needs `source: {{refs: [...]}}` or `source: structural|exploratory`")
            continue
        for r in src["refs"]:
            if r.get("ref") not in refs:
                errs.append(f"result {rid}: unknown reference {r.get('ref')}")
            elif not r.get("location"):
                errs.append(f"result {rid}: reference {r.get('ref')} needs a location")
            elif not ((ver.get(r["ref"]) or {}).get("locations", {}).get(r["location"]) or {}).get("verified"):
                errs.append(f"result {rid}: location {r['location']!r} in {r['ref']} not verified")
    # Every substantive task (milestone, proof) belongs to a milestone with a source entry.
    tasks_yaml = ROOT / "docs/tasks/tasks.yaml"
    tasks = (yaml.safe_load(tasks_yaml.read_text()) or {}).get("tasks", []) if tasks_yaml.exists() else []
    missing = sorted({t.get("milestone") for t in tasks if t.get("kind") in ("milestone", "proof")
                      and t.get("milestone") not in (data.get("milestones") or {})}, key=str)
    for mid in missing:
        errs.append(f"milestone {mid}: has substantive tasks but no entry in docs/tasks/sources.yaml")
    for e in errs:
        print("error:", e)
    print(f"sources check: {'OK' if not errs else 'FAILED'} ({len(refs)} references, "
          f"{len(data.get('milestones') or {})} milestones, {len(results)} results)")
    return 1 if errs else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("cmd", choices=["verify", "check", "find", "chapters", "search", "sections"])
    ap.add_argument("keys", nargs="*")
    a = ap.parse_args()
    if a.cmd == "find":
        cmd_find(a.keys[0], a.keys[1:])
        return 0
    if a.cmd == "search":
        cmd_search(" ".join(a.keys))
        return 0
    if a.cmd == "sections":
        return cmd_sections(a.keys[0])
    if a.cmd == "chapters":
        cmd_chapters(*a.keys)
        return 0
    if a.cmd == "verify":
        cmd_verify(set(a.keys))
        return 0
    return cmd_check()


if __name__ == "__main__":
    sys.exit(main())
