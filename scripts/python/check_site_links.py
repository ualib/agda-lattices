#!/usr/bin/env python3
"""
File: scripts/python/check_site_links.py

Description: Fail when a link in the built site points at a page or an
  anchor that does not exist, here or on the sibling site.

  `mkdocs build --strict` checks the links MkDocs writes from Markdown, but
  not the ones inside Agda's code blocks, which are raw HTML: every token of
  every highlighted block is a link to its definition, rewritten by
  scripts/python/mkdocs_gen_library.py to a page of this site, a page of the
  standard library under /classic/, or a page of the Agda Universal Algebra
  Library's site.  This check reads the built pages instead, and has two
  parts.

  Here (always).  Every `href` and `src` of every page that is not an
  absolute URL must name a file of the built site, and its fragment, if any,
  an `id` on that page.  A root-relative URL must lie under the path of
  `site_url` (the site is served from /agda-lattices/ until it has a domain
  of its own), so a link that works only at a domain's root is caught.

  The sibling site (`--sibling`, which needs the network).  Every link to
  the sibling site must name a page that exists there, and every anchor must
  name the same definition there as in this build.  Agda's anchors are
  character positions in a module's source, so `#5462` on the sibling's page
  of `Setoid.Algebras.Basic` is the definition this site means only while
  the sibling site was built from the commit of agda-algebras that this
  repository pins.  The check compares, for each anchor linked, the element
  that carries it (its text and class) on the live page with the element
  that carries it in this build's own render of that module
  (`.agda-html/md/<Module>.md`, written by `make agda-md` from the pinned
  sources).  A difference means the sibling site has moved on, and the fix
  is to move the pin.

Design Principles:
  Pure core, effectful shell: `targets_in`, `ids_in`, `resolve` and
  `anchor_element` map text to values and touch nothing; `scan_here` and
  `scan_sibling` read the files and the network through Results; `main`
  prints and sets the exit code.
"""
from __future__ import annotations

import argparse
import os
import posixpath
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional
from urllib.parse import urldefrag, urljoin, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parent))

from _utils import ErrorType, PipelineError, Result  # noqa: E402
from _utils.file_ops import read_text  # noqa: E402

# Attribute values in the generated HTML are always double-quoted (MkDocs,
# Material and Agda all write them so), which is what lets a regular
# expression stand in for a parser over 40 MB of pages.
LINK_ATTR_RE: re.Pattern[str] = re.compile(r'<(?:a|link|script|img)\b[^>]*?\s(?:href|src)="([^"]*)"')
ID_RE: re.Pattern[str] = re.compile(r'\sid="([^"]*)"')
EXTERNAL_RE: re.Pattern[str] = re.compile(r"^(?:[a-z][a-z0-9+.-]*:|//)", re.IGNORECASE)
FAKE_HOST: str = "http://site.invalid"


@dataclass(frozen=True)
class Finding:
    page: str
    target: str
    why: str

    def __str__(self) -> str:
        return f"{self.page}: {self.target}: {self.why}"


@dataclass(frozen=True)
class Element:
    """The element carrying an anchor: its class and its text, as written."""
    cls: str
    text: str


# --------------------------------------------------------------------------
# Pure core
# --------------------------------------------------------------------------

def targets_in(html: str) -> tuple[str, ...]:
    """Every href and src of a page's <a>, <link>, <script> and <img>."""
    return tuple(LINK_ATTR_RE.findall(html))


def ids_in(html: str) -> frozenset[str]:
    return frozenset(ID_RE.findall(html))


def page_url(rel_path: str) -> str:
    """The URL a built file is served at, relative to the site root."""
    return rel_path[: -len("index.html")] if rel_path.endswith("index.html") else rel_path


def resolve(page_rel: str, target: str, base_path: str) -> Optional[str]:
    """The built file a same-site ``target`` on ``page_rel`` names, as a path
    relative to the site root, or None when it leaves the site (a
    root-relative URL outside ``base_path``, or a relative one above the
    root).  The fragment and query are dropped; the caller checks the
    fragment."""
    url, _ = urldefrag(target)
    path = urlsplit(urljoin(f"{FAKE_HOST}{base_path}{page_url(page_rel)}", url)).path
    if not path.startswith(base_path):
        return None
    rel = posixpath.normpath(path[len(base_path):]) if path != base_path else "."
    if rel.startswith(".."):
        return None
    return "index.html" if rel == "." else (f"{rel}/index.html" if path.endswith("/") else rel)


def findings_here(page_rel: str, html: str, base_path: str,
                  exists: Callable[[str], bool],
                  ids_of: Callable[[str], frozenset[str]]) -> tuple[Finding, ...]:
    """The broken same-site links of one page.  ``exists`` answers whether a
    path relative to the site root is a file (a directory with an index.html
    counts, under the path the caller gives); ``ids_of`` the ids of a page."""
    def check(target: str) -> Optional[Finding]:
        if EXTERNAL_RE.match(target) or target.startswith("data:"):
            return None
        _, frag = urldefrag(target)
        if target.startswith("#"):
            return None if not frag or frag in ids_of(page_rel) else \
                Finding(page_rel, target, "no such id on this page")
        if target.startswith("?"):
            return None
        rel = resolve(page_rel, target, base_path)
        if rel is None:
            return Finding(page_rel, target, f"leaves the site (served under {base_path})")
        found = rel if exists(rel) else (f"{rel}/index.html" if exists(f"{rel}/index.html") else None)
        if found is None:
            return Finding(page_rel, target, f"no such file: {rel}")
        if frag and found.endswith(".html") and frag not in ids_of(found):
            return Finding(page_rel, target, f"no id {frag!r} in {found}")
        return None
    return tuple(f for f in map(check, sorted(set(targets_in(html)))) if f is not None)


def anchor_element(html: str, anchor: str) -> Optional[Element]:
    """The <a> element carrying ``id=anchor`` in an Agda render, if any."""
    m = re.search(rf'<a\b[^>]*\sid="{re.escape(anchor)}"[^>]*>(.*?)</a>', html, re.DOTALL)
    if m is None:
        return None
    cls = re.search(r'\sclass="([^"]*)"', m.group(0))
    return Element(cls.group(1) if cls else "", m.group(1))


def sibling_links(htmls: dict[str, str], sibling: str) -> dict[str, frozenset[str]]:
    """Every sibling page this site links, with the anchors linked on it."""
    pairs = [urldefrag(t) for html in htmls.values() for t in targets_in(html)
             if t.startswith(sibling)]
    pages = {p for p, _ in pairs}
    return {p: frozenset(f for q, f in pairs if q == p and f) for p in pages}


def module_of(page: str, sibling: str) -> str:
    """The module a sibling page URL renders: .../Setoid/Algebras/Basic/."""
    return page[len(sibling):].strip("/").replace("/", ".")


def findings_sibling(page: str, live: str, local: Optional[str],
                     anchors: frozenset[str]) -> tuple[Finding, ...]:
    """The anchors on one sibling page that do not name, on the live page,
    the definition they name in this build's render (``local``)."""
    if anchors and local is None:
        return (Finding(page, "", "linked with anchors, but this build has no render "
                        "of the module (run make agda-md)"),)

    def check(anchor: str) -> Optional[Finding]:
        ours = anchor_element(local or "", anchor)
        theirs = anchor_element(live, anchor)
        if ours is None:
            return Finding(page, f"#{anchor}", "no such anchor in this build's render")
        if theirs is None:
            return Finding(page, f"#{anchor}", f"no such anchor on the live page "
                           f"(here it is {ours.text!r}); the sibling site has moved on")
        if theirs != ours:
            return Finding(page, f"#{anchor}", f"the live page has {theirs.text!r} "
                           f"({theirs.cls}) where this build has {ours.text!r} ({ours.cls}); "
                           "the sibling site has moved on")
        return None
    return tuple(f for f in map(check, sorted(anchors, key=int_or_text)) if f is not None)


def int_or_text(s: str) -> tuple[int, str]:
    return (int(s), "") if s.isdigit() else (sys.maxsize, s)


# --------------------------------------------------------------------------
# Effectful shell
# --------------------------------------------------------------------------

def read_site(site: Path) -> Result[dict[str, str], PipelineError]:
    """Every built page, by its path relative to the site root."""
    if not (site / "index.html").is_file():
        return Result.err(PipelineError(ErrorType.FILE_NOT_FOUND,
                                        f"{site}/index.html not found; build the site first"))
    paths = sorted(p for p in site.rglob("*.html"))
    reads = [(p.relative_to(site).as_posix(), read_text(p)) for p in paths]
    bad = [r.unwrap_err() for _, r in reads if r.is_err]
    return Result.err(bad[0]) if bad else Result.ok({k: r.unwrap() for k, r in reads})


def scan_here(site: Path, htmls: dict[str, str], base_path: str) -> tuple[Finding, ...]:
    ids = {k: ids_in(v) for k, v in htmls.items()}

    def exists(rel: str) -> bool:
        return rel in htmls or (site / rel).is_file()

    def ids_of(rel: str) -> frozenset[str]:
        return ids.get(rel, frozenset())
    return tuple(f for k, v in htmls.items() for f in findings_here(k, v, base_path, exists, ids_of))


def fetch(url: str, tries: int = 3) -> Result[str, PipelineError]:
    """GET a page, retrying a transient failure; a 404 is not retried."""
    def attempt(n: int) -> Result[str, PipelineError]:
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "agda-lattices-link-check"})
            with urllib.request.urlopen(req, timeout=30) as resp:
                return Result.ok(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            if e.code < 500 or n + 1 >= tries:
                return Result.err(PipelineError(ErrorType.VALIDATION_ERROR, f"HTTP {e.code}"))
        except (urllib.error.URLError, TimeoutError) as e:
            if n + 1 >= tries:
                return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"unreachable: {e}"))
        time.sleep(2 ** n)
        return attempt(n + 1)
    return attempt(0)


def scan_sibling(htmls: dict[str, str], sibling: str, agda_md: Path) -> tuple[tuple[Finding, ...], int, int]:
    """The sibling findings, with the number of pages and anchors checked."""
    links = sibling_links(htmls, sibling)

    def one(page: str) -> tuple[Finding, ...]:
        live = fetch(page)
        if live.is_err:
            return (Finding(page, "", str(live.unwrap_err().message)),)
        module = module_of(page, sibling)
        local = read_text(agda_md / f"{module}.md") if module else Result.ok("")
        return findings_sibling(page, live.unwrap(), local.unwrap() if local.is_ok else None,
                                links[page])
    found = tuple(f for page in sorted(links) for f in one(page))
    return found, len(links), sum(len(a) for a in links.values())


def site_settings(mkdocs_yml: str, site_url: Optional[str]) -> tuple[str, str]:
    """(the path of the site's URL, the sibling URL).  The site's URL is
    ``site_url`` when given (the build's SITE_URL), else mkdocs.yml's default."""
    url = re.search(r'^site_url:.*?"(https?://[^"]+)"', mkdocs_yml, re.MULTILINE)
    sib = re.search(r"^\s+agda_algebras:\s*(\S+)\s*$", mkdocs_yml, re.MULTILINE)
    path = urlsplit(site_url or (url.group(1) if url else "/")).path
    return (path if path.endswith("/") else path + "/",
            sib.group(1) if sib else "https://agda-algebras.universalalgebra.org/")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("site", type=Path, nargs="?", default=Path("site"))
    ap.add_argument("--sibling", action="store_true",
                    help="also check every link to the sibling site against the live pages")
    ap.add_argument("--base-path", help="the path the site is served under "
                    "(default: that of $SITE_URL, else of mkdocs.yml's default site_url)")
    ap.add_argument("--agda-md", type=Path, default=Path(".agda-html/md"),
                    help="this build's Agda render (default: .agda-html/md)")
    args = ap.parse_args()

    settings = read_text(Path("mkdocs.yml")).map(
        lambda text: site_settings(text, os.environ.get("SITE_URL")))
    if settings.is_err:
        print(f"error: {settings.unwrap_err()}", file=sys.stderr)
        return 2
    default_base, sibling = settings.unwrap()
    base_path = args.base_path or default_base

    site = read_site(args.site)
    if site.is_err:
        print(f"error: {site.unwrap_err()}", file=sys.stderr)
        return 2
    htmls = site.unwrap()

    here = scan_here(args.site, htmls, base_path)
    n_links = sum(len(targets_in(v)) for v in htmls.values())
    for f in here:
        print(f"✗ {f}", file=sys.stderr)
    print(f"{'✗' if here else '✓'} here: {len(htmls)} pages, {n_links} links "
          f"and assets, {len(here)} broken")

    there: tuple[Finding, ...] = ()
    if args.sibling:
        there, n_pages, n_anchors = scan_sibling(htmls, sibling, args.agda_md)
        for f in there:
            print(f"✗ {f}", file=sys.stderr)
        print(f"{'✗' if there else '✓'} sibling: {n_pages} pages of {sibling}, "
              f"{n_anchors} anchors, {len(there)} broken")
    return 1 if here or there else 0


if __name__ == "__main__":
    raise SystemExit(main())
