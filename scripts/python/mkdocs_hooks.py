"""MkDocs build hooks for the agda-lattices site.

Adapted from the hooks of the Agda Universal Algebra Library's site (its
``scripts/python/mkdocs_hooks.py``, Apache-2.0; see NOTICE).

`on_page_markdown` rewrites the *repo-relative* links that the prose uses for
GitHub viewing into links MkDocs resolves, so cross-references work on the
site as they do on GitHub:

    ](src/Lattices/Free/Term.lagda.md#...)  ->  ](/Lattices/Free/Term.md#...)
    ](NOTICE)                               ->  ](https://github.com/.../NOTICE)
    ](Lattices/Free.md)  (from docs/index.md)   unchanged: a docs page

A link to a repository file goes to GitHub only when git tracks the file;
anything else is left for MkDocs to check, and --strict fails on it.

A target such as ``/Lattices/Free/Term.md`` is relative to the docs
directory (mkdocs.yml: ``validation.links.absolute_links:
relative_to_docs``), so MkDocs checks that the page exists, fails the strict
build when it does not, and writes the link relative to the page it is on.
Only link targets OUTSIDE fenced code blocks are touched, so Agda source is
never altered.  External (http, mailto), root-relative (/...) and pure-anchor
(#...) targets pass through unchanged.

On the landing page, `on_page_markdown` first writes the counted figures into
its `<!-- ualib:stat:NAME -->` markers, by the functions `make corpus-stats`
and its CI check use (corpus_stats.py), so the deployed page and the committed
source cannot disagree.

`on_config` gives the site's own stylesheets and scripts a content hash in
their URLs, so a returning reader never pairs a new page with a stale cached
stylesheet.
"""
from __future__ import annotations

import hashlib
import logging
import posixpath
import re
import subprocess
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
if str(_SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPT_DIR))

from corpus_stats import fill, landing_values  # noqa: E402

log = logging.getLogger("mkdocs.plugins.lattices.render")

REPO_BLOB = "https://github.com/ualib/agda-lattices/blob/main/"

LINK = re.compile(r"(\]\()([^)\s]+)(\))")
FENCE = re.compile(r"^\s*```")

_total = 0
_done = 0
_docs: frozenset[str] = frozenset()
_tracked: frozenset[str] = frozenset()


def retarget(target: str, page_dir: str = "", docs: frozenset[str] = frozenset(),
             tracked: frozenset[str] = frozenset()) -> str:
    """The link MkDocs should see for ``target``, written in prose on a page
    whose source sits in ``page_dir`` (relative to docs/).  ``docs`` holds
    the docs-relative paths of the site's pages, ``tracked`` the repository's
    tracked files (git ls-files)."""
    base, sep, frag = target.partition("#")
    anchor = (sep + frag) if sep else ""

    if base == "" or re.match(r"^(?:https?:|mailto:|/)", base):
        return target  # external, root-relative, or pure anchor

    # A link from one docs page to another is MkDocs' own: it resolves it
    # against the page, checks it, and writes it.
    if posixpath.normpath(posixpath.join(page_dir, base)) in docs:
        return target

    # Prose links in the modules are repo-relative and written from varying
    # directory depths (./src/..., ../../src/...); strip the leading
    # dot-segments so we can match on the repo path regardless of where the
    # source module sits.
    base = re.sub(r"^(?:\.{1,2}/)+", "", base)

    m = re.match(r"^src/(.+)\.lagda\.md$", base)
    if m:
        return f"/{m.group(1)}.md{anchor}"
    # Any other file the repository tracks (README.md, LICENSE, NOTICE,
    # CITATION.cff, a script, a workflow): view it on GitHub rather than 404
    # on the site.  Anything else is left as written, so that MkDocs reports
    # it under --strict rather than the site sending a reader to a GitHub
    # page that does not exist.
    if base in tracked:
        return f"{REPO_BLOB}{base}{anchor}"
    return target


def tracked_files() -> frozenset[str]:
    """The repository's tracked files, or none when git cannot say (then
    every link to a repository file is left for MkDocs to report)."""
    try:
        out = subprocess.run(["git", "ls-files", "-z"], capture_output=True,
                             check=True).stdout.decode("utf-8")
    except (OSError, subprocess.CalledProcessError):
        log.warning("git ls-files failed: links to repository files cannot be resolved")
        return frozenset()
    return frozenset(p for p in out.split("\0") if p)


def _cache_bust(entry, docs_dir: Path):
    """Append a short content hash to a local asset reference.  ``entry`` is a
    ``str`` (extra_css) or an ``ExtraScriptValue`` carrying a ``.path``
    (extra_javascript).  Absolute URLs and already-queried refs pass through.
    """
    has_path = hasattr(entry, "path")
    ref = entry.path if has_path else entry
    if "://" in ref or "?" in ref:
        return entry
    try:
        digest = hashlib.md5((docs_dir / ref).read_bytes()).hexdigest()[:8]
    except OSError:
        return entry
    busted = f"{ref}?h={digest}"
    if has_path:
        entry.path = busted
        return entry
    return busted


def on_config(config):
    """Cache-bust the site's own CSS and JS (a hash in each local URL)."""
    docs_dir = Path(config["docs_dir"])
    config["extra_css"] = [_cache_bust(e, docs_dir) for e in config["extra_css"]]
    config["extra_javascript"] = [_cache_bust(e, docs_dir) for e in config["extra_javascript"]]
    return config


def on_files(files, config):
    """Keep the generated navigation file off the site, and count the pages
    so the per-page log can show progress.

    gen-files writes SUMMARY.md for literate-nav, which reads it when the
    navigation is built; left included, MkDocs would also publish it as a
    page (/SUMMARY/) and index it for search.  Hooks run after the plugins
    listed in mkdocs.yml, so the file exists here."""
    from mkdocs.structure.files import InclusionLevel
    summary = files.get_file_from_path("SUMMARY.md")
    if summary is not None:
        summary.inclusion = InclusionLevel.EXCLUDED
    global _total, _done, _docs, _tracked
    _total = sum(1 for f in files if getattr(f, "is_documentation_page", lambda: False)())
    _done = 0
    _docs = frozenset(f.src_uri for f in files
                      if getattr(f, "is_documentation_page", lambda: False)())
    _tracked = tracked_files()
    return files


def fill_corpus_stats(markdown: str) -> str:
    """The landing page with its stat markers holding freshly counted values.

    A failure to count (a toolchain file whose shape changed, say) leaves the
    committed values in place and warns.  They are gated by CI, so they are
    the right fallback, and the warning stops `mkdocs build --strict`, which
    is `make site`: the same failure fails the gate on the same commit.
    """
    values = landing_values()
    if values.is_err:
        log.warning(f"corpus stats not recomputed: {values.unwrap_err().message}")
        return markdown
    counted = values.unwrap()
    log.info(f"corpus stats: {counted['modules']} modules, "
             f"{counted['loc']} lines of Agda, {counted['checked']} machine-checked, "
             f"Agda {counted['agda']} · stdlib {counted['stdlib']}")
    return fill(markdown, counted)


def on_page_markdown(markdown: str, *, page=None, config=None, files=None) -> str:
    global _done
    _done += 1

    src_uri = getattr(getattr(page, "file", None), "src_uri", None) or ""
    if src_uri == "index.md":
        markdown = fill_corpus_stats(markdown)
    page_dir = posixpath.dirname(src_uri)
    out: list[str] = []
    in_code = False
    rewrites = 0
    for line in markdown.split("\n"):
        if FENCE.match(line):
            in_code = not in_code
        elif not in_code:
            new = LINK.sub(lambda m: m.group(1) + retarget(m.group(2), page_dir, _docs, _tracked)
                           + m.group(3), line)
            if new != line:
                rewrites += 1
            line = new
        out.append(line)

    src = getattr(getattr(page, "file", None), "src_uri", None) or "?"
    note = f", {rewrites} link(s) retargeted" if rewrites else ""
    log.debug(f"[{_done}/{_total}] {src}{note}")
    return "\n".join(out)
