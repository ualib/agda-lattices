#!/usr/bin/env python3
"""
File: scripts/python/test_site_pipeline.py

Description: Tests for the site's own tools: where the generator points
  Agda's links (mkdocs_gen_library), how the hook retargets prose links
  (mkdocs_hooks), the built-site link check and its sibling half
  (check_site_links), the theme comparison (theme/check_theme), and the
  shapes gen_links treats as generated.

  Run with `make site-test` inside `nix develop` (the generator imports
  mkdocs-gen-files), or under pytest.  Prints `OK (n tests)` and exits 0.
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / "theme"))

import check_site_links as csl  # noqa: E402
import check_theme as ct  # noqa: E402
import gen_links as gl  # noqa: E402
import mkdocs_gen_library as gen  # noqa: E402
import mkdocs_hooks as hooks  # noqa: E402

SIB = "https://agda-algebras.universalalgebra.org/"
LIB = {"Lattices.Free", "Lattices.Free.Term", "Lattices.Free.Whitman", "Lattices.Dual"}
ALG = {"Setoid.Algebras.Basic"}


def href(target: str, anchor: str, here: str) -> str:
    return gen.agda_href(target, anchor, here, LIB, ALG, SIB)


# --------------------------------------------------------------------------- #
# Where Agda's links go.
# --------------------------------------------------------------------------- #
def test_a_link_to_this_library_is_relative_to_the_page() -> None:
    assert href("Lattices.Free.Whitman", "#12", "Lattices.Free.Term") == "../Whitman/#12"
    assert href("Lattices.Dual", "", "Lattices.Free.Term") == "../../Dual/"
    # The barrel's page is the section page, one level up from its children.
    assert href("Lattices.Free", "#3", "Lattices.Free.Term") == "../#3"
    assert href("Lattices.Free.Term", "#3", "Lattices.Free") == "Term/#3"


def test_a_link_within_the_page_is_its_anchor() -> None:
    assert href("Lattices.Free.Term", "#40", "Lattices.Free.Term") == "#40"
    assert href("Lattices.Free.Term", "", "Lattices.Free.Term") == "./"


def test_a_link_into_agda_algebras_goes_to_its_site_with_the_anchor() -> None:
    assert href("Setoid.Algebras.Basic", "#5462", "Lattices.Dual") \
        == f"{SIB}Setoid/Algebras/Basic/#5462"


def test_any_other_link_goes_to_the_classic_pages() -> None:
    assert href("Data.Nat.Base", "#7", "Lattices.Free.Term") == "../../../classic/Data.Nat.Base.html#7"
    assert href("Level", "", "Lattices.Dual") == "../../classic/Level.html"


def test_rewrite_touches_only_agda_links() -> None:
    html = ('<a id="1" href="Lattices.Dual.html#9" class="Module">x</a>'
            '<a href="https://example.org/a.html">y</a>')
    out = gen.rewrite_agda_hrefs(html, "Lattices.Free.Term", LIB, ALG, SIB)
    assert 'href="../../Dual/#9"' in out
    assert 'href="https://example.org/a.html"' in out


def test_hidden_block_is_revealed_as_toggleable() -> None:
    body = gen.reveal_hidden_agda('<!--\n<pre class="Agda">import X</pre>\n-->')
    assert body == '<pre class="Agda hidden-source">import X</pre>'
    assert gen.all_code_hidden(body)


def test_navigation_order() -> None:
    assert gen.ordered(["Examples", "Dual", "Free", "Breadth"]) \
        == ["Free", "Breadth", "Dual", "Examples"]


# --------------------------------------------------------------------------- #
# The hook's prose links.
# --------------------------------------------------------------------------- #
def test_retarget() -> None:
    assert hooks.retarget("src/Lattices/Free/Term.lagda.md#x") == "/Lattices/Free/Term.md#x"
    assert hooks.retarget("../../src/Lattices/Dual.lagda.md") == "/Lattices/Dual.md"
    assert hooks.retarget("NOTICE") == f"{hooks.REPO_BLOB}NOTICE"
    assert hooks.retarget("CITATION.cff") == f"{hooks.REPO_BLOB}CITATION.cff"
    for unchanged in ("#why", "https://x.org/a", "/Lattices/Dual.md", "mailto:a@b"):
        assert hooks.retarget(unchanged) == unchanged


# --------------------------------------------------------------------------- #
# The built-site check, here.
# --------------------------------------------------------------------------- #
PAGES = {
    "index.html": '<a id="top" href="Lattices/Dual/">d</a>',
    "Lattices/Dual/index.html": '<a id="9">x</a>',
    "classic/Level.html": '<a id="7">Level</a>',
}


def broken(page: str, html: str, base: str = "/agda-lattices/") -> list[str]:
    def exists(rel: str) -> bool:
        return rel in PAGES or rel == "assets/x.css"

    def ids_of(rel: str) -> frozenset[str]:
        return csl.ids_in(PAGES.get(rel, ""))
    return [f.why for f in csl.findings_here(page, html, base, exists, ids_of)]


def test_good_links_pass() -> None:
    html = ('<a href="../../classic/Level.html#7">L</a><a href="../Dual/#9">d</a>'
            '<link href="../../assets/x.css" rel="stylesheet"><a href="#9">self</a>'
            '<a href="https://elsewhere.org/">e</a><a href="/agda-lattices/Lattices/Dual/">r</a>')
    assert broken("Lattices/Dual/index.html", html) == []


def test_a_missing_page_is_caught() -> None:
    assert broken("index.html", '<a href="classic/Nope.html">n</a>') == ["no such file: classic/Nope.html"]


def test_a_missing_anchor_is_caught() -> None:
    assert broken("index.html", '<a href="classic/Level.html#8">n</a>') \
        == ["no id '8' in classic/Level.html"]
    assert broken("index.html", '<a href="#nowhere">n</a>') == ["no such id on this page"]


def test_a_root_relative_link_outside_the_base_path_is_caught() -> None:
    assert broken("index.html", '<a href="/Lattices/Dual/">r</a>') \
        == ["leaves the site (served under /agda-lattices/)"]
    assert broken("index.html", '<a href="/Lattices/Dual/">r</a>', base="/") == []


def test_a_link_above_the_root_is_caught() -> None:
    assert broken("index.html", '<a href="../README.md">r</a>')[0].startswith("leaves the site")


# --------------------------------------------------------------------------- #
# The built-site check, the sibling site.
# --------------------------------------------------------------------------- #
LOCAL = '<a id="5462" href="Setoid.Algebras.Basic.html#5462" class="Function Operator">𝔻[_]</a>'


def test_anchor_element_reads_class_and_text() -> None:
    assert csl.anchor_element(LOCAL, "5462") == csl.Element("Function Operator", "𝔻[_]")
    assert csl.anchor_element(LOCAL, "546") is None


def test_the_same_definition_passes() -> None:
    live = '<a id="5462" href="/Setoid/Algebras/Basic/#5462" class="Function Operator">𝔻[_]</a>'
    assert csl.findings_sibling("p", live, LOCAL, frozenset({"5462"})) == ()


def test_a_moved_anchor_is_caught() -> None:
    live = '<a id="5462" class="Function">𝕌[_]</a>'
    found = csl.findings_sibling("p", live, LOCAL, frozenset({"5462"}))
    assert len(found) == 1 and "moved on" in found[0].why
    assert "no such anchor on the live page" in \
        csl.findings_sibling("p", "", LOCAL, frozenset({"5462"}))[0].why


def test_sibling_links_groups_anchors_by_page() -> None:
    htmls = {"a.html": f'<a href="{SIB}X/Y/#1">a</a><a href="{SIB}X/Y/#2">b</a><a href="{SIB}">c</a>'}
    assert csl.sibling_links(htmls, SIB) == {f"{SIB}X/Y/": frozenset({"1", "2"}),
                                             SIB: frozenset()}
    assert csl.module_of(f"{SIB}Setoid/Algebras/Basic/", SIB) == "Setoid.Algebras.Basic"


# --------------------------------------------------------------------------- #
# The theme comparison and the generated link shapes.
# --------------------------------------------------------------------------- #
def test_theme_differences() -> None:
    same = {rel: b"x" for rel in ct.COPIED}
    assert ct.differences(same, same) == ()
    edited = {**same, "docs/stylesheets/tokens.css": b"y"}
    assert ct.differences(edited, same) == ("docs/stylesheets/tokens.css: differs from agda-algebras",)
    gone = {**same, "overrides/404.html": None}
    assert ct.differences(same, gone) == ("overrides/404.html: not in agda-algebras at this commit",)


def test_generated_link_shapes() -> None:
    assert gl.is_generated("Lattices.Dual", "/Lattices/Dual.md", SIB)
    assert gl.is_generated("Setoid.Algebras.Basic", f"{SIB}Setoid/Algebras/Basic/", SIB)
    assert not gl.is_generated("sibling", SIB, SIB)
    assert gl.sibling_url("extra:\n  agda_algebras: https://a.org\n") == "https://a.org/"


# --------------------------------------------------------------------------- #
def main() -> int:
    tests = [v for k, v in sorted(globals().items())
             if k.startswith("test_") and callable(v)]
    for t in tests:
        t()
    print(f"OK ({len(tests)} tests)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
