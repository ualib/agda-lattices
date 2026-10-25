#!/usr/bin/env python3
"""
File: scripts/python/theme/check_theme.py

Description: Fail when a file copied from the Agda Universal Algebra
  Library's site differs from that library at the stated commit.

  This site wears that site's theme, and the theme is shared, not imitated:
  the files below are copies, byte for byte, so that a change to either
  site's look is a copy, never a redesign.  `make theme-check` fetches
  agda-algebras at THEME_REV (the Makefile) and runs this check against it;
  a difference means a copy was edited here (the change belongs in
  agda-algebras first) or THEME_REV moved without the files being copied
  again (`make theme-sync` copies them).

  The list is the theme's shareable files, as agda-algebras names them, and
  the site components this site takes unchanged: the copy button and the
  "Show all Agda" switch, with the utilities the offline check imports.
  Two files of the shareable set are not taken: build_fonts.py and its test
  regenerate the fonts, which is agda-algebras' work; this site copies the
  fonts it writes.

Design Principles:
  Pure core, effectful shell: `differences` compares two mappings of bytes;
  `main` reads both trees and prints.
"""
from __future__ import annotations

import argparse
import shutil
import sys
from pathlib import Path
from typing import Optional

COPIED: tuple[str, ...] = (
    ".gitattributes",
    "docs/assets/fonts/OFL-Inter.txt",
    "docs/assets/fonts/OFL-JuliaMono.txt",
    "docs/assets/fonts/OFL-SpaceGrotesk.txt",
    "docs/assets/fonts/fonts.css",
    "docs/assets/fonts/inter-400-italic.woff2",
    "docs/assets/fonts/inter-400.woff2",
    "docs/assets/fonts/inter-600.woff2",
    "docs/assets/fonts/juliamono-mathalpha.woff2",
    "docs/assets/fonts/juliamono-symbols.woff2",
    "docs/assets/fonts/juliamono-text.woff2",
    "docs/assets/fonts/spacegrotesk-600.woff2",
    "docs/assets/js/agda-copy.js",
    "docs/assets/js/agda-toggle.js",
    "docs/stylesheets/agda.css",
    "docs/stylesheets/theme.css",
    "docs/stylesheets/tokens.css",
    "overrides/404.html",
    "overrides/partials/source.html",
    "scripts/js/_browser.mjs",
    "scripts/js/audit_contrast.mjs",
    "scripts/js/audit_fonts.mjs",
    "scripts/js/audit_offline.mjs",
    "scripts/python/_utils/__init__.py",
    "scripts/python/_utils/file_ops.py",
    "scripts/python/_utils/pipeline_types.py",
    "scripts/python/test_check_links.py",
    "scripts/python/theme/check_offline.py",
    "scripts/python/theme/test_check_offline.py",
)


def read(path: Path) -> Optional[bytes]:
    return path.read_bytes() if path.is_file() else None


def differences(ours: dict[str, Optional[bytes]],
                theirs: dict[str, Optional[bytes]]) -> tuple[str, ...]:
    """The files whose bytes differ, or which are missing on either side."""
    def why(rel: str) -> Optional[str]:
        a, b = ours[rel], theirs[rel]
        if b is None:
            return f"{rel}: not in agda-algebras at this commit"
        if a is None:
            return f"{rel}: missing here"
        return None if a == b else f"{rel}: differs from agda-algebras"
    return tuple(w for w in map(why, COPIED) if w is not None)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("upstream", type=Path, help="a tree of agda-algebras at THEME_REV")
    ap.add_argument("--sync", action="store_true",
                    help="copy the files from upstream instead of comparing")
    args = ap.parse_args()

    if args.sync:
        for rel in COPIED:
            (Path(rel).parent).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(args.upstream / rel, rel)
        print(f"copied {len(COPIED)} files from {args.upstream}")
        return 0

    found = differences({rel: read(Path(rel)) for rel in COPIED},
                        {rel: read(args.upstream / rel) for rel in COPIED})
    for line in found:
        print(f"✗ {line}", file=sys.stderr)
    print(f"{'✗' if found else '✓'} theme: {len(COPIED)} files compared, {len(found)} differ")
    return 1 if found else 0


if __name__ == "__main__":
    raise SystemExit(main())
