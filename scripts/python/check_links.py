#!/usr/bin/env python3
"""Fail if any reference-style cross-link in the rendered corpus is undefined.

The site leans on *reference-style* Markdown links (`[Lattices.Free.Term][]`,
`[Setoid.Algebras.Basic][]`, `[`text`][Some.Module]`), resolved from
the shared library docs/_links.md that pymdownx.snippets auto-appends to every
page.  When a label has no definition, python-markdown does NOT error: it emits
the literal source text (`[Lattices.Nope][]`) into the HTML.  So a missing definition
sails straight through `mkdocs build --strict` and ships as a visibly broken
link.  This checker is the guard `--strict` cannot be: it scans the source for
every reference *usage* and fails when the label it needs is not defined.

Paired with `gen_links.py --check` (which keeps _links.md's generated
sections in sync with the trees), the two together make it impossible to add
a module or a cross-reference and silently reintroduce a broken link.

Adapted from the Agda Universal Algebra Library's
``scripts/python/check_links.py`` (Apache-2.0; see NOTICE): the scanner is
unchanged, and the scope is this repository's.

Scope: every module, src/**/*.lagda.md, and every page under docs/ except the
_links.md library itself.

Definitions counted: every `[label]: target` in docs/_links.md (global, since it
is appended to every page) plus any defined locally in the page under scan.

Usages checked: collapsed `[text][]` and full `[text][ref]` references, outside
fenced code blocks, `<!-- … -->` comments, and inline `code` spans (all of which
Markdown renders literally, so a reference there is not a link).  Shortcut
`[text]` references are not checked: they are ambiguous against ordinary bracket
text and the corpus does not use them for cross-links.

Run from the repo root:  python3 scripts/python/check_links.py
Exit status is 0 when every reference resolves, 1 otherwise (with a report).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

SRC = Path("src")
DOCS = Path("docs")
LINKS = DOCS / "_links.md"

# The reference-link library itself, which is definitions, not prose.
DOCS_EXCLUDE_FILES = {"_links.md"}

# A reference definition:  [label]: target   (indented ≤3 spaces; not a [^fn]).
DEF = re.compile(r"^ {0,3}\[([^\]^][^\]]*)\]:\s+\S")
# A reference usage:  [text][ref]  or collapsed  [text][]
USE = re.compile(r"\[([^\]\n]+)\]\[([^\]\n]*)\]")
# Inline code span; its contents render verbatim.  A span is a run of N
# backticks closed by the next run of exactly N (CommonMark), so a multi-backtick
# span (used when the code itself contains a backtick, e.g. the kramdown
# ``` ``Algebra`{.AgdaRecord}`` ``` idiom) is matched whole.  A
# plain `[^`]*` would see only single-backtick spans and check reference-like
# text that is really inside a longer code span.
CODESPAN = re.compile(r"(`+)(.+?)\1")
FENCE = re.compile(r"^\s*(```|~~~)")


def norm(label: str) -> str:
    """Markdown reference ids are case-insensitive with internal whitespace
    collapsed and the ends trimmed."""
    return re.sub(r"\s+", " ", label).strip().lower()


def defined_labels(text: str) -> set[str]:
    # A backtick in a label makes it unusable as a reference id (Markdown turns
    # it into a code span), so such a "definition" never satisfies a use.
    return {lbl for line in text.splitlines() if (m := DEF.match(line))
            if "`" not in (lbl := norm(m.group(1)))}


def is_resolved(ref: str, known: set[str]) -> bool:
    """Whether a reference id resolves the way python-markdown resolves it.  A
    backtick in the id means a code span was consumed there before reference
    resolution runs, so the reference can never resolve however it is defined
    (this is the STYLE_GUIDE `[text][`path`]` failure mode)."""
    return "`" not in ref and ref in known


def iter_uses(text: str):
    """Yield ``(lineno, ref_id, raw)`` for each reference usage in ``text`` that
    sits in rendered prose, skipping fenced code, HTML comments, and inline
    code spans."""
    in_fence = False
    in_comment = False
    for lineno, line in enumerate(text.splitlines(), 1):
        if in_comment:
            if "-->" not in line:
                continue
            # Python-Markdown renders what follows the comment's close on its
            # last line as prose, so scan it like any other line.
            in_comment = False
            line = line[line.index("-->") + 3:]
        elif FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        # Drop fully-closed comments, then detect an opening one that runs on.
        line = re.sub(r"<!--.*?-->", "", line)
        if "<!--" in line:
            in_comment = True
            line = line[: line.index("<!--")]
        spans = [(m.start(), m.end()) for m in CODESPAN.finditer(line)]
        for m in USE.finditer(line):
            if any(start <= m.start() < end for start, end in spans):
                continue  # inside an inline code span → not a link
            text_part, ref_part = m.group(1), m.group(2)
            ref = norm(ref_part) if ref_part.strip() else norm(text_part)
            yield lineno, ref, m.group(0)


def pages() -> list[Path]:
    """The rendered, hand-authored corpus (see the module docstring)."""
    out: list[Path] = sorted(SRC.rglob("*.lagda.md"))
    out += [p for p in sorted(DOCS.rglob("*.md")) if p.name not in DOCS_EXCLUDE_FILES]
    return out


def main() -> int:
    if not LINKS.exists():
        sys.stderr.write(f"error: {LINKS} not found (run gen_links.py)\n")
        return 1
    global_defs = defined_labels(LINKS.read_text(encoding="utf-8"))

    missing: list[tuple[Path, int, str]] = []
    for page in pages():
        text = page.read_text(encoding="utf-8")
        known = global_defs | defined_labels(text)
        for lineno, ref, raw in iter_uses(text):
            if not is_resolved(ref, known):
                missing.append((page, lineno, raw))

    if missing:
        sys.stderr.write(
            f"✗ {len(missing)} undefined reference-style link(s) "
            f"in {len({p for p, _, _ in missing})} file(s):\n\n")
        for page, lineno, raw in missing:
            sys.stderr.write(f"  {page}:{lineno}: {raw}\n")
        sys.stderr.write(
            "\nEither the label is a typo, or it needs a definition.  For a new\n"
            "module, or a newly named module of agda-algebras, run  make gen-links .\n"
            "For any other target, add a definition to the External-links section\n"
            f"of {LINKS}.\n")
        return 1

    print(f"✓ all reference-style links resolve ({len(pages())} pages checked).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
