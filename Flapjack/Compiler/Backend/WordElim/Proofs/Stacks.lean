module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-!
# Stack-frame lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:203-289`:
`get_stack_hd_thm`, `get_stack_LASTN`, `get_stack_CONS`,
`get_stack_enc_stack` and `get_stack_dec_stack`.

HOL's `StackFrame lsz e0 e handler` is the tagged `WordSemStackFrame width`, and
HOL's `LASTN` is `wordSemLastN` (the `rich_list` rendering in `WordSem.Env`).
The untagged helpers `getStack_nil`, `getStack_cons` and
`sptUnion_ln_right` are Flapjack infrastructure with no separate HOL original.
-/

namespace Flapjack.Compiler.Backend.WordElim

/-- Flapjack-only helper: the `get_stack` clause for the empty stack. -/
@[simp] theorem getStack_nil {width : Nat} [NeZero width] :
    getStack ([] : List (WordSemStackFrame width)) = .ln := rfl

/-- Flapjack-only helper: the `get_stack` clause for a cons. -/
@[simp] theorem getStack_cons {width : Nat} [NeZero width] (lsz : Option Nat)
    (nonGcCutset gcCutset : List (Nat × WordLocW width))
    (handler : Option (Nat × Nat × Nat)) (rest : List (WordSemStackFrame width)) :
    getStack (.stackFrame lsz nonGcCutset gcCutset handler :: rest) =
      sptUnion (sptUnion (getNumWordlocAlist nonGcCutset) (getNumWordlocAlist gcCutset))
        (getStack rest) := rfl

/-- Flapjack-only helper: unioning `LN` on the right is the identity. -/
@[simp] theorem sptUnion_ln_right {α : Type} (tree : Spt α) : sptUnion tree .ln = tree := by
  cases tree <;> simp [sptUnion]

/-- Exact HOL `get_stack_hd_thm` (`word_elimProofScript.sml:212-231`): with the
    frame's cut sets at the head, the head frame's locals and the tail stack are
    inside `dr`.  HOL's `lsz` is free in the source statement and is bound here
    after `t`. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_hd_thm"
  (words_as_type_indexed_bitvec)]
theorem getStack_hd_thm {width : Nat} [NeZero width] (stack : List (WordSemStackFrame width))
    (dr : Nat → Prop) (l0 l : List (Nat × WordLocW width))
    (opt : Option (Nat × Nat × Nat)) (t : List (WordSemStackFrame width))
    (lsz : Option Nat)
    (premise : (∀ n, sptMem n (getStack stack) → dr n) ∧
      stack = .stackFrame lsz l l0 opt :: t) :
    (∀ n, sptMem n (getLocals (sptUnion (sptFromAList l0) (sptFromAList l))) → dr n) ∧
      ∀ n, sptMem n (getStack t) → dr n := by
  obtain ⟨hd, shape⟩ := premise
  subst shape
  constructor
  · intro n hmem
    have hunion := getLocals_union_subset (sptFromAList l0) (sptFromAList l) n hmem
    rcases (sptMem_sptUnion _ _ _).mp hunion with hl0 | hl
    · apply hd n
      simp only [getStack_cons, sptMem_sptUnion]
      exact Or.inl (Or.inr (getNumWordlocAlist_get_locals l0 n hl0))
    · apply hd n
      simp only [getStack_cons, sptMem_sptUnion]
      exact Or.inl (Or.inl (getNumWordlocAlist_get_locals l n hl))
  · intro n hmem
    apply hd n
    simp only [getStack_cons, sptMem_sptUnion]
    exact Or.inr hmem

/-- Exact HOL `get_stack_CONS` (`word_elimProofScript.sml:241-246`): a single
    frame and the tail are both inside the whole stack's location set. -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "get_stack_CONS"
  (words_as_type_indexed_bitvec)]
theorem getStack_CONS {width : Nat} [NeZero width] (h : WordSemStackFrame width)
    (t : List (WordSemStackFrame width)) :
    (∀ n, sptMem n (getStack [h]) → sptMem n (getStack (h :: t))) ∧
      ∀ n, sptMem n (getStack t) → sptMem n (getStack (h :: t)) := by
  cases h with
  | stackFrame lsz nonGcCutset gcCutset handler =>
      constructor
      · intro n hmem
        rw [getStack_cons, getStack_nil, sptUnion_ln_right, sptMem_sptUnion] at hmem
        rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
        exact Or.inl hmem
      · intro n hmem
        rw [getStack_cons, sptMem_sptUnion, sptMem_sptUnion]
        exact Or.inr hmem

end Flapjack.Compiler.Backend.WordElim
