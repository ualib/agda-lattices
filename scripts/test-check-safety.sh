#!/usr/bin/env bash
# File: scripts/test-check-safety.sh
#
# The cases of scripts/check-safety.sh: each writes one literate module into a
# fresh directory and names the exit status the check must give it, and the
# last runs the check on src/.  Each case is how the pinned Agda 2.9.0 reads
# the module: which lines are code (bare, indented and prose-prefixed fences
# open code; a fence naming another language does not; `agda` after a space
# or with more text after it is prose), and which pragmas are active (not
# those in a block comment, and an OPTIONS pragma only ahead of the first
# declaration); string and character literals may run over several lines
# and hold string gaps.  Set FIXTURES to a directory to keep the modules
# there.
#
#   bash scripts/test-check-safety.sh
set -u
CHECK=${CHECK:-scripts/check-safety.sh}
PRAGMA='{-# OPTIONS --without-K --exact-split --safe #-}'
F='```'
work=${FIXTURES:-$(mktemp -d)}
[ -n "${FIXTURES:-}" ] || trap 'rm -rf "$work"' EXIT
failures=0

# expect NAME STATUS LINE...: the module made of the lines must give STATUS.
# EXPECT_AT, if set, is the module's path under the case's directory.
expect() {
  local name=$1 want=$2 dir="$work/$1" got at=${EXPECT_AT:-M.lagda.md}
  mkdir -p "$(dirname "$dir/$at")"
  printf '%s\n' "${@:3}" > "$dir/$at"
  bash "$CHECK" "$dir" > "$dir/out" 2>&1
  got=$?
  if [ "$got" -eq "$want" ]; then
    echo "ok    $name"
  else
    echo "FAIL  $name: exit $got, expected $want"
    sed 's/^/      /' "$dir/out"
    failures=$((failures + 1))
  fi
}

HEAD=("# M" "" "${F}agda" "$PRAGMA" "module M where" "$F" "" "Prose may say postulate.")
POST="postulate A : Set"

# Which lines are code.
expect clean                0 "${HEAD[@]}"
expect bare-fence           1 "${HEAD[@]}" "" "$F" "$POST" "$F"
expect indented-fence       1 "${HEAD[@]}" "" "  ${F}agda" "$POST" "  $F"
expect prose-before-fence   1 "${HEAD[@]}" "" "Example: ${F}agda" "$POST" "$F"
expect prose-before-bare    1 "${HEAD[@]}" "" "Example: $F" "$POST" "$F"
expect other-language       0 "${HEAD[@]}" "" "${F}haskell" "postulate = 1" "$F" "" "Then prose: postulate."
expect space-agda           0 "${HEAD[@]}" "" "$F agda" "$POST" "$F"
expect tagged-then-code     1 "${HEAD[@]}" "" "${F}agda title" "prose for Agda" "$F" "$POST" "$F"
expect pragma-in-prose      1 "# M" "" "$PRAGMA" "" "${F}agda" "module M where" "$F"
expect options-in-prose     0 "${HEAD[@]}" "" "Prose may show {-# OPTIONS --with-K #-}."

# Comments and literals inside the code.
expect line-comment         0 "${HEAD[@]}" "" "${F}agda" "-- postulate is not used here" "$F"
expect block-comment        0 "${HEAD[@]}" "" "${F}agda" "{- postulate A : Set" "   {-# TERMINATING #-} -}" "$F"
expect pragma-in-comment    1 "# M" "" "${F}agda" "{-" "$PRAGMA" "-}" "module M where" "$F"
expect pragma-in-nested     1 "# M" "" "${F}agda" "{- {- -}" "$PRAGMA" "-}" "module M where" "$F"
expect string-not-comment   1 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"{-\"" "$POST" "$F"
expect char-not-string      1 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.Char" "c : Char ; c = '\"' ; $POST" "$F"
expect multiline-string     1 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first line" "{-\"" "$POST" "$F"
expect string-gap           1 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first\\" "  \\\" ; $POST" "$F"
expect char-gap             1 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.Char" "c : Char" "c = '\\" "  \\\"' ; $POST" "$F"
expect postulate-in-string  0 "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first line" "postulate\"" "$F"

# Which OPTIONS pragmas are active, and which other pragmas.
expect weaker-pragma        1 "# M" "" "${F}agda" "{-# OPTIONS --without-K --safe #-}" "module M where" "$F"
expect extra-same-line      1 "# M" "" "${F}agda" "$PRAGMA" "$PRAGMA {-# OPTIONS --no-exact-split #-}" "module M where" "$F"
expect extra-own-line       1 "# M" "" "${F}agda" "$PRAGMA" "{-# OPTIONS --no-exact-split #-}" "module M where" "$F"
expect duplicate-pragma     1 "# M" "" "${F}agda" "$PRAGMA" "$PRAGMA" "module M where" "$F"
expect pragma-after-header  1 "# M" "" "${F}agda" "module M where" "$PRAGMA" "$F"
expect terminating          1 "${HEAD[@]}" "" "${F}agda" "{-# TERMINATING #-}" "f : Set" "f = f" "$F"
expect terminating-comment  0 "${HEAD[@]}" "" "${F}agda" "-- {-# TERMINATING #-}" "$F"

# --lossy-unification: in a worked example only, and only added to the pragma.
LOSSY='{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}'
expect lossy-in-theory      1 "# M" "" "${F}agda" "$LOSSY" "module M where" "$F"
EXPECT_AT=Examples/M.lagda.md expect lossy-in-example    0 "# M" "" "${F}agda" "$LOSSY" "module M where" "$F"
EXPECT_AT=Examples/M.lagda.md expect lossy-without-safe  1 "# M" "" "${F}agda" "{-# OPTIONS --without-K --lossy-unification #-}" "module M where" "$F"

if bash "$CHECK" src > "$work/src.out" 2>&1; then
  echo "ok    src"
else
  echo "FAIL  src"; sed 's/^/      /' "$work/src.out"; failures=$((failures + 1))
fi

[ "$failures" -eq 0 ] || { echo "test-check-safety: $failures failures"; exit 1; }
echo "test-check-safety: all cases pass"
