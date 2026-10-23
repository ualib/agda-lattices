#!/usr/bin/env bash
# File: scripts/check-safety.sh
#
# The textual half of what "checked" means here: every module under the
# given directory (default src/) carries the pragma
#
#   {-# OPTIONS --without-K --exact-split --safe #-}
#
# as its one active OPTIONS pragma, ahead of its first declaration, and its
# Agda code holds no postulate and no pragma that switches a check off
# (termination, positivity, universe, coverage).  A worked example (a module
# under an Examples/ directory) may add --lossy-unification to that pragma:
# the option is sound and not infective, --safe accepts it, and it only lets
# Agda compare two applications of a function by their arguments, which an
# example applying general theorems to concrete lattices can need; no other
# module may use it.  Agda's --safe already
# refuses all of these, and the aggregator's --without-K --safe refuses to
# import a module checked without them; this script makes the claim visible
# without running Agda, and is what holds a module to --exact-split, which
# no importing module enforces.
#
#   bash scripts/check-safety.sh [src]
#
# It reads a module as the pinned Agda 2.9.0 does.  In a literate Markdown
# module, a code block opens at a line that ends in a fence of three
# backquotes, optionally followed by `agda`, whatever text comes before it;
# a line that is only a fence naming another language ([a-zA-Z0-9-]*) opens
# a block Agda skips; either closes at the next line that is only a bare
# fence; any other line is prose (Agda's literateMd).  In the code it skips
# nested block comments ({- -}), line comments (-- at the start of a token)
# and string and character literals, which may run over several lines and
# hold escapes and string gaps (a backslash, whitespace, a backslash), and
# reads pragmas ({-# #-}) whole, with the string literals in them.
# scripts/test-check-safety.sh holds the cases.  It prints each failure and
# exits 1, or prints a one-line summary and exits 0; a directory with no
# modules exits 2.
set -u
DIR=${1:-src}
PRAGMA='{-# OPTIONS --without-K --exact-split --safe #-}'
LOSSY='{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}'
UNSAFE='TERMINATING NON_TERMINATING NO_TERMINATION_CHECK NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING INJECTIVE INJECTIVE_FOR_INFERENCE'

# The tokens of a module that matter here, one per line: "P LINE PLACE TEXT"
# for a pragma (PLACE is head before the first declaration, late after it,
# TEXT with its whitespace collapsed) and "K LINE" for the keyword postulate.
scan() {
  local literate=0
  case "$1" in *.lagda.md) literate=1 ;; esac
  awk -v literate="$literate" -v q="'" '
    function tokstart(s, i) { return i == 1 || substr(s, i - 1, 1) ~ /[[:space:].;{}()@"]/ }
    function foreign(    t) {
      t = substr(text, 5)
      return match(t, /^[[:space:]]*(COMPILE|FOREIGN)([[:space:]]|$)/)
    }
    function lex(s, n,    i, len, c, c2, c3, j, w, step) {
      len = length(s); i = 1
      while (i <= len) {
        c = substr(s, i, 1); c2 = substr(s, i, 2); c3 = substr(s, i, 3)
        if (instr) {
          step = 1
          if (ingap) { if (c == "\\") ingap = 0 }
          else if (c == "\\") { step = 2; if (i == len || substr(s, i + 1, 1) ~ /[[:space:]]/) ingap = 1 }
          else if (c == del) instr = 0
          if (strpragma) text = text substr(s, i, step)
          i += step; continue
        }
        if (depth > 0) {
          if (c2 == "{-") { depth++; i += 2 } else if (c2 == "-}") { depth--; i += 2 } else i++
          continue
        }
        if (inpragma) {
          if (c3 == "#-}") {
            text = text "#-}"; gsub(/[[:space:]]+/, " ", text)
            print "P", pline, place, text; inpragma = 0; i += 3
          } else {
            if (c == "\"" && !foreign()) { instr = 1; del = c; ingap = 0; strpragma = 1 }
            text = text c; i++
          }
          continue
        }
        if (c3 == "{-#") { inpragma = 1; text = "{-# "; pline = n; place = seen ? "late" : "head"; i += 3; continue }
        if (c2 == "{-")  { depth = 1; i += 2; continue }
        if (c2 == "--" && tokstart(s, i)) break
        if (c == "\"" || (c == q && tokstart(s, i))) {
          instr = 1; del = c; ingap = 0; strpragma = 0; seen = 1; i++; continue
        }
        if (c ~ /[[:space:]]/) { i++; continue }
        for (j = i; j <= len && substr(s, j, 1) !~ /[[:space:].;{}()@"]/; j++) ;
        if (j == i) j = i + 1
        w = substr(s, i, j - i); seen = 1
        if (w == "postulate") print "K", n
        i = j
      }
      if (inpragma) text = text " "
    }
    literate && state == "" && /```(agda)?[[:space:]]*$/                  { state = "code";  next }
    literate && state == "" && /^[[:space:]]*```[a-zA-Z0-9-]*[[:space:]]*$/ { state = "other"; next }
    literate && state != "" && /^[[:space:]]*```[[:space:]]*$/            { state = "";      next }
    literate && state != "code" { next }
    { lex($0, NR) }' "$1"
}

mapfile -t modules < <(find "$DIR" \( -name '*.lagda.md' -o -name '*.agda' \) \
                         ! -name 'EverythingLattices.agda' | LC_ALL=C sort)
[ "${#modules[@]}" -gt 0 ] || { echo "safety: no modules under $DIR" >&2; exit 2; }

failures=0
fail() { echo "$1: $2"; failures=$((failures + 1)); }
for m in "${modules[@]}"; do
  tokens=$(scan "$m")
  options=$(printf '%s\n' "$tokens" | awk '$1 == "P" && $5 == "OPTIONS"')
  count=$(printf '%s\n' "$options" | grep -c .)
  [ "$count" -gt 0 ] || fail "$m" "missing the pragma $PRAGMA in its code"
  [ "$count" -le 1 ] || fail "$m" "$count OPTIONS pragmas, where one is allowed"
  while read -r _ line place text; do
    [ -n "$line" ] || continue
    case "$text" in
      "$PRAGMA") ;;
      "$LOSSY")
        case "$m" in
          */Examples/*) ;;
          *) fail "$m" "line $line: --lossy-unification outside a worked example" ;;
        esac ;;
      *) fail "$m" "line $line: another OPTIONS pragma: $text" ;;
    esac
    [ "$place" = head ] || fail "$m" "line $line: an OPTIONS pragma after the first declaration, where Agda ignores it"
  done <<< "$options"
  while read -r _ line _ _ name _; do
    [ -n "$line" ] || continue
    case " $UNSAFE " in *" $name "*) fail "$m" "line $line: the pragma $name" ;; esac
  done < <(printf '%s\n' "$tokens" | awk '$1 == "P"')
  while read -r _ line; do
    [ -n "$line" ] && fail "$m" "line $line: postulate"
  done < <(printf '%s\n' "$tokens" | awk '$1 == "K"')
done

if [ "$failures" -gt 0 ]; then
  echo "safety: $failures problems in ${#modules[@]} modules"
  exit 1
fi
echo "safety: ${#modules[@]} modules, each with the pragma and no postulate or unsafe pragma"
