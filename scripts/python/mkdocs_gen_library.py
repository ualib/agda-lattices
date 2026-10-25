"""Mount the agda-lattices library into the MkDocs site.

Run by ``mkdocs-gen-files`` during ``mkdocs build`` / ``mkdocs serve``.
Adapted from the generator of the Agda Universal Algebra Library's site
(its ``scripts/python/mkdocs_gen_library.py``, Apache-2.0; see NOTICE).  It

  1.  walks ``src/**/*.lagda.md`` and, for each module, writes a *virtual*
      site page at the module's hierarchical path with the ``.lagda`` infix
      stripped (``/Lattices/Free/Term/``).  Two rendering modes:

        + **highlighted**: if ``.agda-html/md/<Dotted>.md`` exists (written by
          ``make agda-md``, that is ``agda --html --html-highlight=code``),
          mount that: its code blocks are ``<pre class="Agda">`` with every
          token classed and linked to its definition.  Agda's
          ``Module.Sub.html#id`` links are rewritten by ``agda_href``, below;
        + **plain**: otherwise mount the raw ``.lagda.md`` (the fast path of
          ``make site``, for work on prose and the theme);

  2.  publishes, at ``/classic/``, Agda's own pages (``agda --html``, written
      by ``make html``) of the standard library modules the library reaches,
      and only those: this library's modules have their pages above, and the
      Agda Universal Algebra Library's are on that library's site; and

  3.  emits ``SUMMARY.md``, the literate-nav file that becomes the
      navigation: the module tree under ``Lattices``.

Where a link goes (``agda_href``).  A link to one of this library's modules
goes to its page here; a link to a module of the Agda Universal Algebra
Library goes to that module's page on its site, anchor kept; a link to any
other module (the standard library) goes to its page under ``/classic/``.
Every internal link is written relative to the page it is on, never
root-relative, so the site works at any address (a project page under
``/agda-lattices/`` as well as a domain of its own).  Agda's anchors are
positions in a module's source, so an anchor into the sibling site is right
only while the pinned agda-algebras is the commit that site was built from;
``scripts/python/check_site_links.py --sibling`` checks every one of them
against the live pages.

In every mode the Jekyll front matter is dropped, a ``# Dotted.Module`` title
is prepended, and blocks that the sources hide in ``<!-- ... -->`` comments
are re-surfaced as toggleable ``hidden-source`` blocks.  The sources are
never modified.
"""

from __future__ import annotations

import logging
import os
import posixpath
import re
from pathlib import Path
from typing import Optional

import mkdocs_gen_files
from mkdocs.exceptions import PluginError

log = logging.getLogger("mkdocs.plugins.lattices.gen")

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

SRC_DIR = Path("src")
DOCS_DIR = Path("docs")
AGDA_MD_DIR = Path(".agda-html/md")          # agda --html --html-highlight=code
CLASSIC_DIR = Path(".agda-html/classic")     # agda --html (whole-page) output
STYLESHEETS = DOCS_DIR / "stylesheets"

# The pinned agda-algebras sources, as the dev shell copies them (flake.nix);
# the shell exports ALGEBRAS, which AGDA_ALGEBRAS_DIR can redirect.
ALGEBRAS_SRC = Path(os.environ.get("ALGEBRAS", ".deps/agda-algebras")) / "src"

# Every module lives under this namespace; the navigation starts below it.
ROOT_NAMESPACE = "Lattices"
# Under it, the free lattices first (the README's order), the worked
# examples last, and the rest alphabetically between.
FIRST = ["Free"]
LAST = ["Examples"]

FRONT_MATTER_RE = re.compile(r"\A---\r?\n.*?\r?\n---\r?\n", re.DOTALL)
LIQUID_LINE_RE = re.compile(r"^[ \t]*\{%.*?%\}[ \t]*\r?\n?", re.MULTILINE)
FIRST_H1_RE = re.compile(r"^# \S", re.MULTILINE)
# An agda --html hyperlink: href="Module.Dotted.html" with an optional #offset.
AGDA_HREF_RE = re.compile(r'href="([A-Za-z0-9._]+)\.html(#\d+)?"')
# A block hidden in the source: an HTML comment whose whole payload is one
# Agda code block, highlighted (`<pre class="Agda">`) or plain fenced.
HIDDEN_PRE_RE = re.compile(r'<!--\s*(<pre class="Agda">.*?</pre>)\s*-->', re.DOTALL)
HIDDEN_FENCE_RE = re.compile(r'<!--\s*(```agda\r?\n.*?\r?\n```)\s*-->', re.DOTALL)
# Every code block on a mounted page, for the all-code-hidden tripwire below.
ANY_PRE_RE = re.compile(r'<pre class="Agda[" ]')
ANY_FENCE_RE = re.compile(r"^```agda[ \t]*$", re.MULTILINE)

# Modules whose only code block is hidden by design, exempt from the
# all-code-hidden tripwire.  None so far.
PROSE_ONLY_MODULES: set[str] = set()


# --------------------------------------------------------------------------
# Module names and URLs
# --------------------------------------------------------------------------

def dotted_name(parts: tuple[str, ...]) -> str:
    return ".".join(parts)


def modules_under(root: Path, suffixes: tuple[str, ...]) -> set[str]:
    """The dotted names of the modules under ``root`` with the given suffixes."""
    out: set[str] = set()
    for suffix in suffixes:
        for p in root.rglob(f"*{suffix}"):
            out.add(dotted_name(p.relative_to(root).as_posix()[: -len(suffix)].split("/")))
    return out


def page_dir(dotted: str) -> str:
    """The directory a module's page is served from: ``Lattices/Free/Term``."""
    return dotted.replace(".", "/")


def agda_href(target: str, anchor: str, here: str, library: set[str],
              algebras: set[str], sibling: str) -> str:
    """The URL a token on ``here``'s page links to, for Agda's link to
    ``target`` (a dotted module name) at ``anchor`` (``#offset`` or empty).

    This library's modules: the page here, relative to ``here``'s page.  The
    Agda Universal Algebra Library's: its page on ``sibling``.  Any other
    module: its page under ``/classic/``, relative to ``here``'s page.
    """
    if target in library:
        if target == here:
            return anchor or "./"
        rel = posixpath.relpath(page_dir(target), page_dir(here))
        return f"{rel}/{anchor}"
    if target in algebras:
        return f"{sibling}{page_dir(target)}/{anchor}"
    rel = posixpath.relpath(f"classic/{target}.html", page_dir(here))
    return f"{rel}{anchor}"


def rewrite_agda_hrefs(html: str, here: str, library: set[str],
                       algebras: set[str], sibling: str) -> str:
    """Rewrite every agda --html token link on ``here``'s page (agda_href)."""
    def repl(m: "re.Match[str]") -> str:
        url = agda_href(m.group(1), m.group(2) or "", here, library, algebras, sibling)
        return f'href="{url}"'
    return AGDA_HREF_RE.sub(repl, html)


# --------------------------------------------------------------------------
# Per-page source -> site transformation
# --------------------------------------------------------------------------

def normalise(source: str, title: str) -> str:
    """Drop the Jekyll front matter and Liquid tags, and ensure a ``# Title``."""
    body = FRONT_MATTER_RE.sub("", source, count=1)
    body = LIQUID_LINE_RE.sub("", body)
    body = body.lstrip("\n")
    if not FIRST_H1_RE.search(body):
        body = f"# {title}\n\n{body}"
    return body


def reveal_hidden_agda(body: str) -> str:
    """Re-surface the blocks hidden in HTML comments.

    Module sources wrap their import scaffolding in ``<!-- ... -->`` so that
    GitHub collapses it.  On the site the block becomes *toggleable* instead
    of lost: the comment is unwrapped and the block tagged ``hidden-source``,
    hidden by docs/stylesheets/site.css until the reader flips the header's
    "Show all Agda" switch (docs/assets/js/agda-toggle.js).
    """
    body = HIDDEN_PRE_RE.sub(
        lambda m: m.group(1).replace(
            '<pre class="Agda">', '<pre class="Agda hidden-source">', 1),
        body)
    # Plain mode keeps the fence so pymdownx renders it normally; md_in_html
    # (markdown="1") lets the wrapping <div> carry the hidden-source class.
    body = HIDDEN_FENCE_RE.sub(
        lambda m: f'<div class="hidden-source" markdown="1">\n\n{m.group(1)}\n\n</div>',
        body)
    return body


def all_code_hidden(body: str) -> bool:
    """Would this page render with hidden blocks but no visible code at all?"""
    hidden = body.count("hidden-source")
    total = len(ANY_PRE_RE.findall(body)) + len(ANY_FENCE_RE.findall(body))
    return hidden > 0 and total == hidden


# --------------------------------------------------------------------------
# Navigation tree
# --------------------------------------------------------------------------

class Node:
    def __init__(self, name: str) -> None:
        self.name = name
        self.page: Optional[str] = None
        self.children: dict[str, "Node"] = {}

    def child(self, name: str) -> "Node":
        return self.children.setdefault(name, Node(name))


def ordered(names: list[str]) -> list[str]:
    """FIRST, then the rest alphabetically, then LAST."""
    middle = sorted(n for n in names if n not in FIRST and n not in LAST)
    return ([n for n in FIRST if n in names] + middle
            + [n for n in LAST if n in names])


def emit_node(node: Node, lines: list[str], depth: int) -> None:
    indent = "    " * depth
    for name in sorted(node.children):
        kid = node.children[name]
        if kid.page:
            lines.append(f"{indent}- [{name}]({kid.page})")
        else:
            lines.append(f"{indent}- {name}")
        emit_node(kid, lines, depth + 1)


# --------------------------------------------------------------------------
# Main (run by gen-files at build time; the functions above are importable)
# --------------------------------------------------------------------------

def main() -> None:
    config = mkdocs_gen_files.config
    sibling = (config.get("extra") or {}).get("agda_algebras", "")
    if not sibling.endswith("/"):
        sibling += "/"

    modules = sorted(SRC_DIR.rglob("*.lagda.md"))
    library = modules_under(SRC_DIR, (".lagda.md",))
    highlight = AGDA_MD_DIR.is_dir()

    # agda-algebras' modules, which both Agda outputs need: a highlighted
    # page's links into them go to the sibling site, and their pages are
    # left out of /classic/.  Without the sources neither can be told from
    # the standard library, so a build that has either output refuses to
    # guess.
    if (highlight or CLASSIC_DIR.is_dir()) and not ALGEBRAS_SRC.is_dir():
        raise PluginError(f"{ALGEBRAS_SRC} not found: run the build inside "
                          "`nix develop`, which copies the pinned agda-algebras")
    algebras = (modules_under(ALGEBRAS_SRC, (".lagda.md", ".agda"))
                if ALGEBRAS_SRC.is_dir() else set())

    mode = ("highlighted (agda --html)" if highlight
            else "plain (no agda --html; run `make site-full` for highlighting)")
    log.info(f"Mounting {len(modules)} library modules, {mode}")

    root = Node("")
    n_high = n_plain = 0
    for src_path in modules:
        parts = src_path.relative_to(SRC_DIR).as_posix()[: -len(".lagda.md")].split("/")
        dotted = dotted_name(tuple(parts))
        dest = "/".join(parts) + ".md"

        agda_md = AGDA_MD_DIR / f"{dotted}.md"
        if highlight and agda_md.is_file():
            text = rewrite_agda_hrefs(agda_md.read_text(encoding="utf-8"),
                                      dotted, library, algebras, sibling)
            n_high += 1
        else:
            text = src_path.read_text(encoding="utf-8")
            n_plain += 1
        body = reveal_hidden_agda(normalise(text, dotted))
        if dotted not in PROSE_ONLY_MODULES and all_code_hidden(body):
            log.warning(f"{dotted}: every code block on this page is hidden, "
                        "so it renders blank by default")

        with mkdocs_gen_files.open(dest, "w") as fh:
            fh.write(body)
        mkdocs_gen_files.set_edit_path(dest, src_path.as_posix())

        node = root
        for part in parts:
            node = node.child(part)
        node.page = dest

    log.info(f"Mounted {len(modules)} modules ({n_high} highlighted, {n_plain} plain)")

    # ---- The standard library's pages at /classic/ ------------------------
    # Agda writes a page for every module the build reaches.  Only the
    # standard library's are published: neither this library's own (they
    # have their pages above) nor agda-algebras' (they are on its site).
    # The pages are Agda's, byte for byte; their stylesheet is the site's
    # tokens (classic_stylesheet), as on the sibling site's /classic/.
    n_classic = 0
    if CLASSIC_DIR.is_dir():
        for f in sorted(CLASSIC_DIR.iterdir()):
            if f.name == "Agda.css":
                data = classic_stylesheet()
            elif f.suffix == ".html" and f.stem not in library | algebras \
                    and f.stem != "EverythingLattices":
                data = f.read_bytes()
            else:
                continue
            with mkdocs_gen_files.open(f"classic/{f.name}", "wb") as fh:
                fh.write(data)
            n_classic += 1
        log.info(f"/classic/: published {n_classic} files of the standard library")
    else:
        log.info("/classic/: skipped (run `make html` to write the standard library's pages)")

    # ---- SUMMARY.md -------------------------------------------------------
    nav: list[str] = ["- [Home](index.md)", "- The Library"]
    top = root.children.get(ROOT_NAMESPACE, Node(ROOT_NAMESPACE))
    for name in ordered(list(top.children)):
        group = Node("")
        group.children[name] = top.children[name]
        emit_node(group, nav, 1)
    # The sibling library, from mkdocs.yml's extra.agda_algebras, which the
    # footer and the landing page's card point at too.
    if sibling != "/":
        nav.append(f"    - [agda-algebras ↗]({sibling})")
    with mkdocs_gen_files.open("SUMMARY.md", "w") as fh:
        fh.write("\n".join(nav) + "\n")


# /classic/Agda.css.  Agda's own stylesheet colors tokens with Emacs'
# defaults, several of which fail WCAG AA as text, and names no font.  The
# sibling site replaces it with its tokens and token colors in the light
# scheme (these pages carry no scheme switch), with JuliaMono from the site's
# fonts; so does this one, with the same glue.  An @import must precede every
# other rule, so it heads the file.
CLASSIC_IMPORT = '@import url("../assets/fonts/fonts.css");\n'
CLASSIC_GLUE = """
/* -- /classic/ only (scripts/python/mkdocs_gen_library.py) -------------------
   Agda's plain HTML pages: the light tokens from :root, the faces from the
   site's fonts, and the page and block surfaces. */
body {
  margin: 0;
  background-color: var(--c-bg);
  color: var(--c-fg);
}
pre.Agda {
  margin: 0;
  padding: 1.5rem;
  font-family: var(--font-mono), monospace;
  font-variant-ligatures: none;  /* JuliaMono would draw `-->` as one arrow */
  line-height: 1.5;
}
"""


def classic_stylesheet() -> bytes:
    """/classic/Agda.css: the fonts, tokens.css, agda.css, then the glue."""
    sheets = [(STYLESHEETS / name).read_text(encoding="utf-8")
              for name in ("tokens.css", "agda.css")]
    return "\n".join([CLASSIC_IMPORT, *sheets, CLASSIC_GLUE]).encode("utf-8")


# gen-files runs this file with runpy.run_path, whose default module name is
# "<run_path>"; an import (the tests) does not run the build.
if __name__ == "<run_path>":
    main()
