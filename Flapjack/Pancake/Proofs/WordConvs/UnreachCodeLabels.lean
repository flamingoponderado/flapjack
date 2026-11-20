module

public import Flapjack.Pancake.Proofs.WordConvs.Unreach
public import Flapjack.Pancake.WordConvs.CodeLabels

@[expose] public section

/-!
Code-label set containment for the native `SimpSeq` / `Seq_assoc_right` /
`remove_unreach` family. These are the `word_get_code_labels_*` theorems of
`wordConvsProofScript.sml:2302-2355`, kept in a sibling module so that the
`Set`-based statements do not enter `CompileConventions.Labels`'s environment.
-/

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Backend.WordUnreach

set_option linter.unusedSimpArgs false in
/-- Original label equality of the move-destructuring helper: every successful
`dest_Seq_Move` returns a remainder with exactly the source's code labels.
HOL binds `x`, `y`, `z` as free variables and `p` under the universal. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_dest_Seq_Move" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_destSeqMove {width : Nat} [NeZero width]
    (x : Nat) (y : List (Nat × Nat)) (z : WordLangProgHOL (BitVec width))
    (p : WordLangProgHOL (BitVec width))
    (found : destSeqMove p = some (x, y, z)) :
    getCodeLabelsHOL z = getCodeLabelsHOL p := by
  cases p <;> simp_all [destSeqMove, getCodeLabelsHOL]
  case move priority moves =>
    rw [← found.2.2]
    simp [getCodeLabelsHOL]
  case seq first second =>
    cases first <;> simp_all [destSeqMove, getCodeLabelsHOL]

/-- Flapjack-only consequence of `getCodeLabels_destSeqMove`, used to close the
`SimpSeq` move-merge branch; no separate HOL declaration. -/
private theorem subset_of_destSeqMove {width : Nat} [NeZero width]
    (q rest : WordLangProgHOL (BitVec width))
    (found : ∃ n l, destSeqMove q = some (n, l, rest)) :
    getCodeLabelsHOL rest ⊆ getCodeLabelsHOL q := by
  obtain ⟨n, l, h⟩ := found
  rw [getCodeLabels_destSeqMove n l rest q h]

/-- Original `SimpSeq` label containment: the simplified sequence keeps only
labels of its two operands. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_SimpSeq" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_simpSeq {width : Nat} [NeZero width]
    (p q : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (simpSeq p q) ⊆ getCodeLabelsHOL p ∪ getCodeLabelsHOL q := by
  fun_cases simpSeq p q <;> simp_all +zetaDelta [getCodeLabelsHOL]
  all_goals
    first
      | exact Set.subset_union_left
      | exact Set.subset_union_right
      | exact Set.empty_subset _
      | exact subset_of_destSeqMove q _ ⟨_, _, by assumption⟩

/-- Original recursive right-association label containment: the reassociated
program keeps only labels of the two operands, for every accumulator. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_Seq_assoc_right" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_seqAssocRight {width : Nat} [NeZero width]
    (ps qs : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (seqAssocRight ps qs) ⊆ getCodeLabelsHOL ps ∪ getCodeLabelsHOL qs := by
  induction ps using
      (measure (fun p : WordLangProgHOL (BitVec width) => sizeOf p)).wf.induction
      generalizing qs with
  | h ps ih =>
    fun_cases seqAssocRight ps qs <;> try simp_all +zetaDelta [getCodeLabelsHOL]
    case h.case2 q1 q2 =>
      have hq1 : WellFoundedRelation.rel q1
          (.seq q1 q2 : WordLangProgHOL (BitVec width)) := by
        change sizeOf q1 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega
      have hq2 : WellFoundedRelation.rel q2
          (.seq q1 q2 : WordLangProgHOL (BitVec width)) := by
        change sizeOf q2 < sizeOf (.seq q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega
      have one := ih q1 hq1 (seqAssocRight q2 qs)
      have two := ih q2 hq2 qs
      intro x hx
      have h1 := one hx
      rw [Set.mem_union] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (Or.inl h1)
      · have h2 := two h1
        rw [Set.mem_union] at h2
        rcases h2 with h2 | h2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h2
    case h.case3 v n r q1 q2 =>
      have hq1 : WellFoundedRelation.rel q1
          (.ite v n r q1 q2 : WordLangProgHOL (BitVec width)) := by
        change sizeOf q1 < sizeOf (.ite v n r q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega
      have hq2 : WellFoundedRelation.rel q2
          (.ite v n r q1 q2 : WordLangProgHOL (BitVec width)) := by
        change sizeOf q2 < sizeOf (.ite v n r q1 q2 : WordLangProgHOL (BitVec width))
        simp
        omega
      have branch1 : getCodeLabelsHOL (seqAssocRight q1 .skip) ⊆ getCodeLabelsHOL q1 := by
        have := ih q1 hq1 .skip
        simpa [getCodeLabelsHOL] using this
      have branch2 : getCodeLabelsHOL (seqAssocRight q2 .skip) ⊆ getCodeLabelsHOL q2 := by
        have := ih q2 hq2 .skip
        simpa [getCodeLabelsHOL] using this
      intro x hx
      have hs := getCodeLabels_simpSeq _ qs hx
      simp only [getCodeLabelsHOL, Set.mem_union] at hs ⊢
      rcases hs with hs | hs
      · rcases hs with hs | hs
        · exact Or.inl (Or.inl (branch1 hs))
        · exact Or.inl (Or.inr (branch2 hs))
      · exact Or.inr hs
    case h.case4 q =>
      have hq : WellFoundedRelation.rel q
          (.mustTerminate q : WordLangProgHOL (BitVec width)) := by
        change sizeOf q < sizeOf (.mustTerminate q : WordLangProgHOL (BitVec width))
        simp
      have branch : getCodeLabelsHOL (seqAssocRight q .skip) ⊆ getCodeLabelsHOL q := by
        have := ih q hq .skip
        simpa [getCodeLabelsHOL] using this
      intro x hx
      have hs := getCodeLabels_simpSeq _ qs hx
      simp only [getCodeLabelsHOL, Set.mem_union] at hs ⊢
      rcases hs with hs | hs
      · exact Or.inl (branch hs)
      · exact Or.inr hs
    case h.case6 dest args handler x1 x2 q1 x3 x4 =>
      have hq1 : WellFoundedRelation.rel q1
          (.call (some (x1, x2, q1, x3, x4)) dest args handler :
            WordLangProgHOL (BitVec width)) := by
        change sizeOf q1 < sizeOf
          (.call (some (x1, x2, q1, x3, x4)) dest args handler :
            WordLangProgHOL (BitVec width))
        simp
        omega
      have branch1 : getCodeLabelsHOL (seqAssocRight q1 .skip) ⊆ getCodeLabelsHOL q1 := by
        have := ih q1 hq1 .skip
        simpa [getCodeLabelsHOL] using this
      cases handler with
      | none =>
        intro x hx
        have hs := getCodeLabels_simpSeq _ qs hx
        simp only [getCodeLabelsHOL, Set.mem_union, Set.mem_empty_iff_false,
          or_false] at hs ⊢
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · exact Or.inl (Or.inl hs)
          · exact Or.inl (Or.inr (branch1 hs))
        · exact Or.inr hs
      | some h =>
        obtain ⟨y1, q2, y2, y3⟩ := h
        have hq2 : WellFoundedRelation.rel q2
            (.call (some (x1, x2, q1, x3, x4)) dest args (some (y1, q2, y2, y3)) :
              WordLangProgHOL (BitVec width)) := by
          change sizeOf q2 < sizeOf
            (.call (some (x1, x2, q1, x3, x4)) dest args (some (y1, q2, y2, y3)) :
              WordLangProgHOL (BitVec width))
          simp
          omega
        have branch2 : getCodeLabelsHOL (seqAssocRight q2 .skip) ⊆ getCodeLabelsHOL q2 := by
          have := ih q2 hq2 .skip
          simpa [getCodeLabelsHOL] using this
        intro x hx
        have hs := getCodeLabels_simpSeq _ qs hx
        simp only [getCodeLabelsHOL, Set.mem_union] at hs ⊢
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · rcases hs with hs | hs
            · exact Or.inl (Or.inl (Or.inl hs))
            · exact Or.inl (Or.inl (Or.inr (branch1 hs)))
          · exact Or.inl (Or.inr (branch2 hs))
        · exact Or.inr hs
    case h.case7 names body exitNames =>
      have hbody : WellFoundedRelation.rel body
          (.loop names body exitNames : WordLangProgHOL (BitVec width)) := by
        change sizeOf body < sizeOf (.loop names body exitNames : WordLangProgHOL (BitVec width))
        simp
        omega
      have branch : getCodeLabelsHOL (seqAssocRight body .skip) ⊆ getCodeLabelsHOL body := by
        have := ih body hbody .skip
        simpa [getCodeLabelsHOL] using this
      intro x hx
      have hs := getCodeLabels_simpSeq _ qs hx
      simp only [getCodeLabelsHOL, Set.mem_union] at hs ⊢
      rcases hs with hs | hs
      · exact Or.inl (branch hs)
      · exact Or.inr hs
    case h.case8 =>
      exact getCodeLabels_simpSeq ps qs

/-- Original whole-program containment for native `remove_unreach`: the
reassociated program keeps only source labels. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_remove_unreach" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_removeUnreach {width : Nat} [NeZero width]
    (ps : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (removeUnreach ps) ⊆ getCodeLabelsHOL ps := by
  unfold removeUnreach
  have := getCodeLabels_seqAssocRight ps .skip
  simpa [getCodeLabelsHOL] using this

end Flapjack.WordConvs
