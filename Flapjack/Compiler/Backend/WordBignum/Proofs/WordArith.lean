module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.Semantics

@[expose] public section

/-! Small arithmetic and list facts used by the bignum generator's correctness
proof, ported from `cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc.Multiword

/-- The boolean-to-word embedding is the source's two-value case split. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "b2w_if"
  (words_as_type_indexed_bitvec)]
theorem b2w_if {width : Nat} [NeZero width] (b : Bool) :
    b2w b = if b then (1 : BitVec width) else 0 := by
  cases b
  · rfl
  · rfl

/-- The boolean-to-natural embedding is the source's two-value case split. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "b2n_if"]
theorem b2n_if (b : Bool) : b2n b = if !b then 0 else 1 := by
  cases b
  · rfl
  · rfl

/-- A list position below the length splits the list as a prefix of exactly that
length, one element and a suffix. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "LESS_LENGTH_IMP_APPEND"]
theorem lessLengthImpAppend {α : Type} :
    ∀ (xs : List α) (n : Nat), n < xs.length →
      ∃ ys z zs, xs = ys ++ z :: zs ∧ ys.length = n := by
  intro xs
  induction xs with
  | nil =>
    intro n hn
    simp at hn
  | cons x xs ih =>
    intro n hn
    cases n with
    | zero =>
      exact ⟨[], x, xs, rfl, rfl⟩
    | succ n =>
      simp only [List.length_cons] at hn
      obtain ⟨ys, z, zs, hsplit, hlen⟩ := ih n (by omega)
      refine ⟨x :: ys, z, zs, ?_, ?_⟩
      · simp only [List.cons_append, hsplit]
      · simp only [List.length_cons, hlen]

end Flapjack.Compiler.Backend.WordBignum
