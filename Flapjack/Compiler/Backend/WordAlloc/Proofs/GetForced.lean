import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.GetForced
import Flapjack.Compiler.Backend.RegAlloc.Proofs

/-!
# `get_forced` accumulator lemmas

The `get_forced` lemmas of `word_allocProofScript.sml:3311-3375`: the
accumulator splits off as a tail, so `EVERY` over the result splits; the forced
pairs are distinct; and every forced register occurs in the program's clash
tree. HOL `EVERY P l` is `∀ x ∈ l, P x`, and HOL's paired `λ(x,y). Q x y` reads
the pair's projections.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-- HOL `get_forced_tail_split` (`word_allocProofScript.sml:3311-3318`). -/
theorem getForcedTailSplit {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (ls ls' : List (Nat × Nat)) :
    getForced c p (ls ++ ls') = getForced c p ls ++ ls' := by
  induction p, ls using getForced.induct c with
  | _ => simp_all [getForced]

/-- HOL `EVERY_get_forced` (`word_allocProofScript.sml:3320-3326`). -/
theorem everyGetForced {width : Nat} [NeZero width] (P : Nat × Nat → Prop)
    (c : AsmConfigExact width) (p : WordLangProgHOL (BitVec width)) (ls : List (Nat × Nat)) :
    (∀ x ∈ getForced c p ls, P x) ↔ (∀ x ∈ getForced c p [], P x) ∧ ∀ x ∈ ls, P x := by
  have h := getForcedTailSplit c p [] ls
  rw [List.nil_append] at h
  rw [h]
  simp only [List.mem_append]
  exact ⟨fun hx => ⟨fun x m => hx x (Or.inl m), fun x m => hx x (Or.inr m)⟩,
    fun ⟨h1, h2⟩ x m => m.elim (h1 x) (h2 x)⟩

/-- HOL `get_forced_pairwise_distinct` (`word_allocProofScript.sml:3328-3335`). -/
theorem getForcedPairwiseDistinct {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (prog : WordLangProgHOL (BitVec width)) (ls : List (Nat × Nat))
    (h : ∀ x ∈ ls, x.1 ≠ x.2) : ∀ x ∈ getForced c prog ls, x.1 ≠ x.2 := by
  induction prog, ls using getForced.induct c with
  | _ =>
      first
        | (simp only [getForced]; (repeat' split) <;> simp_all)
        | simp_all [getForced]

/-- Every forced pair is either from the accumulator or has both registers in
the clash tree, at every loop context (Flapjack infrastructure for the
`get_forced_ind` proof of `get_forced_in_get_clash_tree`). -/
theorem getForcedInClashTreeAcc {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (prog : WordLangProgHOL (BitVec width)) (acc : List (Nat × Nat)) :
    ∀ lt, ∀ x ∈ getForced c prog acc, x ∈ acc ∨
      (inClashTree (getClashTree prog lt) x.1 ∧ inClashTree (getClashTree prog lt) x.2) := by
  induction prog, acc using getForced.induct c with
  | case10 i acc =>
      intro lt x hx; left
      rcases i with _ | _ | a | _ <;> (try rcases a) <;>
        simp_all [getForced]
      all_goals exfalso; rename_i hneg
      all_goals first
        | exact hneg _ _ _ _ rfl rfl rfl rfl
        | exact hneg _ _ _ rfl rfl rfl
  | case17 p acc =>
      intro lt x hx; left
      cases p <;> (try simp_all [getForced])
      all_goals exfalso; rename_i hneg
      exact hneg _ _ _ _ _ rfl rfl rfl rfl rfl
  | case11 s acc ih =>
      intro lt x hx
      simp only [getForced] at hx
      simpa [getClashTree] using ih lt x hx
  | case12 s1 s2 acc ih2 ih1 =>
      intro lt x hx
      simp only [getForced] at hx
      rcases ih1 lt x hx with h | ⟨h1, h2⟩
      · rcases ih2 lt x h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
      · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
  | case13 op cond right e2 e3 acc ih2 ih1 =>
      intro lt x hx
      simp only [getForced] at hx
      rcases ih1 lt x hx with h | ⟨h1, h2⟩
      · rcases ih2 lt x h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (by cases right <;> simp [getClashTree, inClashTree, h1, h2])
      · exact Or.inr (by cases right <;> simp [getClashTree, inClashTree, h1, h2])
  | case14 vs cs rh l1 l2 dest args acc ih =>
      intro lt x hx
      simp only [getForced] at hx
      rcases ih lt x hx with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
  | case15 vs cs rh l1 l2 dest args v prog l1' l2' acc ih2 ih1 =>
      intro lt x hx
      simp only [getForced] at hx
      rcases ih1 lt x hx with h | ⟨h1, h2⟩
      · rcases ih2 lt x h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
      · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
  | case16 names body exitNames acc ih =>
      intro lt x hx
      simp only [getForced] at hx
      rcases ih ((names, exitNames) :: lt) x hx with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (by simp [getClashTree, inClashTree, h1, h2])
  | _ =>
      intro lt x hx
      rcases x with ⟨a, b⟩
      simp_all [getForced, getClashTree, getDeltaInst, HolInst.ofWordLangInst,
        HolArith.ofWordLangArith, inClashTree]
      all_goals
        refine Or.elim (Classical.em _) Or.inl (fun hm => Or.inr ?_)
        simp only [hm, or_false] at hx
      all_goals first
        | omega
        | (have h64 : width ≠ 64 := by omega
           simp only [h64, if_false, inClashTree, List.mem_cons, List.mem_nil_iff, or_false]
           omega)

/-- HOL `get_forced_in_get_clash_tree` (`word_allocProofScript.sml:3337-3375`):
both registers of every forced pair occur in the program's clash tree. -/
theorem getForcedInGetClashTree {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (lt : List (NumSet × NumSet))
    (c : AsmConfigExact width) :
    ∀ x ∈ getForced c prog [],
      inClashTree (getClashTree prog lt) x.1 ∧ inClashTree (getClashTree prog lt) x.2 :=
  fun x hx => (getForcedInClashTreeAcc c prog [] lt x hx).resolve_left (List.not_mem_nil)

end Flapjack.WordAlloc
