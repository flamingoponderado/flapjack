-- Generated from scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out by
-- scripts/generate-bignum-stubs-eq.py; do not edit.
module

public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Part0
public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Part1
public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Part2
public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Part3
public import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Evaluation

@[expose] public section

/-! HOL `generated_bignum_stubs_eq` (`word_bignumScript.sml:576-577`). -/

namespace Flapjack.Compiler.Backend.WordBignum
open Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq

/-- HOL `generated_bignum_stubs_eq`, the evaluation of `generated_bignum_stubs n`
at an arbitrary word dimension, as an explicit list of `(index, arity, program)`
triples. The list and each program are rendered term by term from the HOL
capture by `scripts/generate-bignum-stubs-eq.py`; the programs are named
`stubsEqProgK` only to split the literal into modules. HOL's word dimension
`dimindex (:α)` is `width`, `dimword (:α)` is `2 ^ width`, `n2w m` is
`BitVec.ofNat width m`, and the `ShiftN sh e m` overload is
`.shift sh e (.const (BitVec.ofNat width m))`.

The proof evaluates `generatedBignumStubs` in the kernel through the
constant-independent compiler of `GeneratedStubsEq.Evaluation`. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "generated_bignum_stubs_eq"
  (words_as_type_indexed_bitvec)]
theorem generatedBignumStubs_eq {width : Nat} [NeZero width] (n : Nat) :
    (generatedBignumStubs width n : List (Nat × Nat × WordLangProgHOL (BitVec width))) =
      [(n, 1, stubsEqProg0 width n),
        (n + 22, 1, stubsEqProg1 width n),
        (n + 21, 1, stubsEqProg2 width n),
        (n + 20, 1, stubsEqProg3 width n),
        (n + 19, 1, stubsEqProg4 width n),
        (n + 15, 1, stubsEqProg5 width n),
        (n + 18, 1, stubsEqProg6 width n),
        (n + 17, 1, stubsEqProg7 width n),
        (n + 16, 1, stubsEqProg8 width n),
        (n + 14, 1, stubsEqProg9 width n),
        (n + 13, 1, stubsEqProg10 width n),
        (n + 12, 1, stubsEqProg11 width n),
        (n + 11, 1, stubsEqProg12 width n),
        (n + 10, 1, stubsEqProg13 width n),
        (n + 8, 1, stubsEqProg14 width n),
        (n + 9, 1, stubsEqProg15 width n),
        (n + 7, 1, stubsEqProg16 width n),
        (n + 6, 1, stubsEqProg17 width n),
        (n + 5, 1, stubsEqProg18 width n),
        (n + 4, 1, stubsEqProg19 width n),
        (n + 3, 1, stubsEqProg20 width n),
        (n + 2, 1, stubsEqProg21 width n),
        (n + 1, 1, stubsEqProg22 width n)] := by
  rw [generatedBignumStubs_eq_K]
  kernel_rfl

end Flapjack.Compiler.Backend.WordBignum
