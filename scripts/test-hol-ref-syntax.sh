#!/usr/bin/env bash
set -euo pipefail

# Compile throwaway declarations so syntax tests do not create false HOL ports
# in the repository's declaration inventory.
root_dir=$(cd "$(dirname "$0")/.." && pwd)
cd "$root_dir"
lake build Flapjack.HolRef >/dev/null
test_file=$(mktemp --suffix=.lean)
trap 'rm -f "$test_file"' EXIT

printf '%s\n' \
  'import Flapjack.HolRef' \
  'open Flapjack' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def"]' \
  'theorem exactSyntax : True := trivial' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [degrees])]' \
  'theorem qualifiedSyntax : True := trivial' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" 252 (list_as_array := [degrees, moves])]' \
  'theorem qualifiedLineSyntax : True := trivial' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (words_as_type_indexed_bitvec)]' \
  'theorem wordsQualifierSyntax : True := trivial' \
  '#hol_refs' > "$test_file"
output=$(lake env lean "$test_file")
[[ "$output" == *'qualifiedSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def (list_as_array := [degrees])'* ]]
[[ "$output" == *'qualifiedLineSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def :252 (list_as_array := [degrees, moves])'* ]]
[[ "$output" == *'exactSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def'* ]]
[[ "$output" == *'wordsQualifierSyntax  cakeml/compiler/backend/reg_alloc/reg_allocScript.sml  dec_deg_def (words_as_type_indexed_bitvec)'* ]]

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [])]' \
  'theorem emptyQualifier : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'empty list_as_array qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "dec_deg_def" (list_as_array := [degrees, degrees])]' \
  'theorem duplicateFields : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'duplicate list_as_array fields were accepted' >&2
  exit 1
fi

# A literal or compound `NeZero` argument is never a valid positivity
# discharge, a reducible zero-width abbreviation must be unfolded, and nested
# binders must be resolved in their own de Bruijn context.
printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem literalNeZero [NeZero 5] (x : BitVec 5) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'literal NeZero binder under the words qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem compoundNeZero {w : Nat} [NeZero (w - w)] (x : BitVec w) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'compound NeZero binder under the words qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  'abbrev ZeroWord (w : Nat) := BitVec w' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem zeroWidthAbbrev (x : ZeroWord 0) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'zero-width reducible abbreviation under the words qualifier was accepted' >&2
  exit 1
fi

# A nullary reducible abbreviation used as a type is a bare `.const`, not an
# application, so it must be unfolded before the `.app` default is applied;
# otherwise `abbrev ZeroWord := BitVec 0` hides a zero-width word.
printf '%s\n' \
  'import Flapjack.HolRef' \
  'abbrev ZeroWord := BitVec 0' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem nullaryZeroWidthAbbrev (x : ZeroWord) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'nullary zero-width abbreviation under the words qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  'abbrev W (w : Nat) := BitVec w' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem parameterizedZeroWidthAbbrev (x : W 0) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'parameterized zero-width abbreviation under the words qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  'abbrev W (w : Nat) := BitVec w' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem parameterizedPositiveWidthAbbrev {w : Nat} [NeZero w] (x : W w) : True := trivial' > "$test_file"
if ! lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'parameterized positive-width abbreviation under the words qualifier was rejected' >&2
  exit 1
fi

# A declaration type containing a structure projection must be traversed
# (`Expr.proj`), not skipped or crashed on.
printf '%s\n' \
  'import Flapjack.HolRef' \
  'structure Box where' \
  '  n : Nat' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem projectionTraversal {w : Nat} [NeZero w] (x : BitVec w) (b : Box)' \
  '    (h : b.n = 0) : True := trivial' > "$test_file"
if ! lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'a structure projection in the declaration type was rejected or crashed' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem nestedMissingNeZero (f : (u : Unit) → (m : Nat) → BitVec m) : True := trivial' > "$test_file"
if lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'nested forall with an undischarged width under the words qualifier was accepted' >&2
  exit 1
fi

printf '%s\n' \
  'import Flapjack.HolRef' \
  '@[hol "cakeml/pancake/semantics/panSemScript.sml" "state" (words_as_type_indexed_bitvec)]' \
  'theorem nestedBoundNeZero (a : ∀ {w : Nat} [NeZero w], BitVec w) : True := trivial' > "$test_file"
if ! lake env lean "$test_file" >/dev/null 2>&1; then
  echo 'nested forall with its own NeZero binder was rejected' >&2
  exit 1
fi

echo 'HOL reference attribute syntax: exact and qualified forms pass; invalid qualifiers rejected'
