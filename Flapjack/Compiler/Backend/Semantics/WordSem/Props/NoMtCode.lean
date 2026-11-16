module

public import Flapjack.Pancake.WordConvs.NotCreated
public import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public import Flapjack.Misc.Sptree

@[expose] public section
namespace Flapjack
namespace WordProps

/-- HOL `no_mt_code_def` (`wordPropsScript.sml:4772-4775`): no code entry
contains `MustTerminate`. The word dimension is the only representation
translation; the tree carrier and lookup are the reviewed HOL
constructor-for-constructor port. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml"
  "no_mt_code_def" (words_as_type_indexed_bitvec)]
def noMtCode {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ (k n : Nat) (p : WordLangProgHOL (BitVec width)),
    sptLookup k code = some (n, p) → noMtSubprogsHOL p = true

/-- Exact HOL `no_mt_find_code` (`wordPropsScript.sml:4777-4791`): any code
entry reached by `find_code` under `no_mt_code` is free of `MustTerminate`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "no_mt_find_code"
  (words_as_type_indexed_bitvec)]
theorem noMtFindCode {width : Nat} {progWidth : Nat} [NeZero width] [NeZero progWidth]
    {StackSize : Type}
    (code : Spt (Nat × WordLangProgHOL (BitVec progWidth))) (dest : Option Nat)
    (args : List (WordLocW width)) (lsize : Spt StackSize)
    (args1 : List (WordLocW width)) (expr : WordLangProgHOL (BitVec progWidth))
    (ps : Option StackSize)
    (premises : wordSemFindCode dest args code lsize = some (args1, expr, ps) ∧
      noMtCode code) : noMtSubprogsHOL expr = true := by
  obtain ⟨run, ok⟩ := premises
  cases dest with
  | some p =>
    cases hl : sptLookup p code with
    | none =>
      simp only [wordSemFindCode, hl] at run
      simp at run
    | some entry =>
      obtain ⟨arity, exp⟩ := entry
      by_cases hlen : args.length = arity
      · simp only [wordSemFindCode, hl, if_pos hlen, Option.some.injEq,
          Prod.mk.injEq] at run
        obtain ⟨-, rfl, -⟩ := run
        exact ok p arity exp hl
      · simp only [wordSemFindCode, hl, if_neg hlen] at run
        simp at run
  | none =>
    by_cases hempty : args = []
    · simp only [wordSemFindCode, dif_pos hempty] at run
      simp at run
    · cases hlast : args.getLast hempty with
      | word value =>
        simp only [wordSemFindCode, dif_neg hempty, hlast] at run
        simp at run
      | loc block offset =>
        cases offset with
        | zero =>
          cases hl : sptLookup block code with
          | none =>
            simp only [wordSemFindCode, dif_neg hempty, hlast, hl] at run
            simp at run
          | some entry =>
            obtain ⟨arity, exp⟩ := entry
            by_cases hlen : args.length = arity + 1
            · simp only [wordSemFindCode, dif_neg hempty, hlast, hl, if_pos hlen,
                Option.some.injEq, Prod.mk.injEq] at run
              obtain ⟨-, rfl, -⟩ := run
              exact ok block arity exp hl
            · simp only [wordSemFindCode, dif_neg hempty, hlast, hl, if_neg hlen] at run
              simp at run
        | succ offset =>
          simp only [wordSemFindCode, dif_neg hempty, hlast] at run
          simp at run
end WordProps
end Flapjack
