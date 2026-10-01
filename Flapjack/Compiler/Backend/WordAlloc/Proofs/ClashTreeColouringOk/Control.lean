import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Inst
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

/-!
# `clash_tree_colouring_ok` `Seq`, `If` and `MustTerminate` cases

The recursive cases of `word_allocProofScript.sml:2813-3309`
`clash_tree_colouring_ok` (proof `word_allocProofScript.sml:2995-3032`), with the
induction hypotheses of HOL `get_clash_tree_ind` for the sub-programs. The
untagged helpers are Flapjack proof infrastructure for the tagged cases.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- HOL `clash_tree_colouring_ok`, `Seq` case: the second statement is checked
first and its output feeds the first. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_Seq {width : Nat} [NeZero width]
    (c1 c2 : WordLangProgHOL (BitVec width)) (ih1 : clashTreeGoal c1) (ih2 : clashTreeGoal c2) :
    clashTreeGoal (.seq c1 c2 : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, hlt, hd, hi, hc⟩
  rw [getClashTree] at hc
  unfold checkClashTree at hc
  cases h2 : checkClashTree f (getClashTree c2 lt) live flive with
  | none => rw [h2] at hc; cases hc
  | some p =>
  obtain ⟨o2, f2⟩ := p
  rw [h2] at hc
  dsimp only at hc
  obtain ⟨w2, i2, co2, e2, d2⟩ := ih2 lt f live flive o2 f2 ⟨hwc.2, hw, hlt, hd, hi, h2⟩
  obtain ⟨w1, i1, co1, e1, d1⟩ := ih1 lt f o2 f2 livein flivein ⟨hwc.1, w2, hlt, d2, i2, hc⟩
  have hl : livein = getLive (.seq c1 c2 : WordLangProgHOL (BitVec width)) live lt := by
    rw [getLive, ← e2]; exact e1
  refine ⟨w1, i1, ?_, hl, d1⟩
  show (∀ a b, sptDomain (getLive c1 (getLive c2 live lt) lt) a →
      sptDomain (getLive c1 (getLive c2 live lt) lt) b → f a = f b → a = b) ∧
    colouringOk f c2 live lt ∧ colouringOk f c1 (getLive c2 live lt) lt
  rw [← e2, ← e1]
  exact ⟨i1, co2, co1⟩

/-- HOL `clash_tree_colouring_ok`, `MustTerminate` case. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_MustTerminate {width : Nat} [NeZero width]
    (body : WordLangProgHOL (BitVec width)) (ih : clashTreeGoal body) :
    clashTreeGoal (.mustTerminate body : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, hlt, hd, hi, hc⟩
  rw [getClashTree] at hc
  obtain ⟨w, i, co, e, d⟩ := ih lt f live flive livein flivein ⟨hwc, hw, hlt, hd, hi, hc⟩
  exact ⟨w, i, co, by rw [getLive]; exact e, d⟩

/-- Keys of `toAList` are the domain (HOL `toAList_domain`; Flapjack infrastructure). -/
theorem mem_sptToAList_keys {α : Type} (x : Spt α) (k : Nat) :
    k ∈ (sptToAList x).map Prod.fst ↔ (sptLookup k x).isSome = true := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨a, v⟩, hm, rfl⟩
    simp [(sptToAList_mem_iff_lookup x a v).mp hm]
  · intro hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    exact ⟨(k, v), (sptToAList_mem_iff_lookup x k v).mpr hv, rfl⟩

/-- Inserting the keys of `difference o2 o1` into `o1` is `union o1 o2` on
well-formed sets (the HOL `If` step with `spt_eq_thm`, `lookup_difference` and
`toAList_domain`; Flapjack infrastructure). -/
theorem insertDiffKeys_eq_union (o1 o2 : NumSet) (h1 : sptWf o1 = true) (h2 : sptWf o2 = true) :
    numsetListInsert ((sptToAList (sptDifference o2 o1)).map Prod.fst) o1 = sptUnion o1 o2 := by
  rw [sptEqThm _ _ ⟨sptWf_numsetListInsert o1 h1 _, sptWfUnion o1 o2 ⟨h1, h2⟩⟩]
  intro k
  rw [lookupNumsetListInsert, sptLookup_sptUnion]
  have hk := mem_sptToAList_keys (sptDifference o2 o1) k
  rw [sptLookupDifference] at hk
  cases ha : sptLookup k o1 with
  | some u => rw [ha] at hk; simp at hk; simp [hk]
  | none =>
    rw [ha] at hk
    cases hb : sptLookup k o2 with
    | none => rw [hb] at hk; simp at hk; simp [hk]
    | some u => rw [hb] at hk; simp at hk; simp [hk]

/-- The checked `If` tree `Seq (Delta [] R) (Branch NONE t1 t2)` (Flapjack
infrastructure for the `If` case). -/
theorem ifCore {width : Nat} [NeZero width] (c1 c2 : WordLangProgHOL (BitVec width))
    (ih1 : clashTreeGoal c1) (ih2 : clashTreeGoal c2) (R : List Nat)
    (lt : List (NumSet × NumSet)) (f : Nat → Nat) (live flive livein flivein : NumSet)
    (hwc1 : wfCutsets c1) (hwc2 : wfCutsets c2) (hw : sptWf live = true)
    (hlt : ∀ p, p ∈ lt → sptWf p.1 = true ∧ sptWf p.2 = true)
    (hd : sptDomain flive = (fun y => ∃ x, sptDomain live x ∧ f x = y))
    (hi : ∀ a b, sptDomain live a → sptDomain live b → f a = f b → a = b)
    (hc : checkClashTree f (.seq (.delta [] R)
      (.branch none (getClashTree c1 lt) (getClashTree c2 lt))) live flive =
        some (livein, flivein)) :
    sptWf livein = true ∧
      (∀ a b, sptDomain livein a → sptDomain livein b → f a = f b → a = b) ∧
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y) ∧
      livein = numsetListInsert R (sptUnion (getLive c1 live lt) (getLive c2 live lt)) ∧
      sptWf (sptUnion (getLive c1 live lt) (getLive c2 live lt)) = true ∧
      colouringOk f c1 live lt ∧ colouringOk f c2 live lt := by
  unfold checkClashTree at hc
  cases hb : checkClashTree f (.branch none (getClashTree c1 lt) (getClashTree c2 lt))
      live flive with
  | none => rw [hb] at hc; cases hc
  | some p =>
  obtain ⟨bo, bc⟩ := p
  rw [hb] at hc
  dsimp only at hc
  unfold checkClashTree at hb
  cases h1 : checkClashTree f (getClashTree c1 lt) live flive with
  | none => rw [h1] at hb; cases hb
  | some p1 =>
  obtain ⟨o1, fc1⟩ := p1
  rw [h1] at hb
  dsimp only at hb
  cases h2 : checkClashTree f (getClashTree c2 lt) live flive with
  | none => rw [h2] at hb; cases hb
  | some p2 =>
  obtain ⟨o2, fc2⟩ := p2
  rw [h2] at hb
  dsimp only at hb
  obtain ⟨w1, i1, co1, e1, d1⟩ := ih1 lt f live flive o1 fc1 ⟨hwc1, hw, hlt, hd, hi, h1⟩
  obtain ⟨w2, -, co2, e2, -⟩ := ih2 lt f live flive o2 fc2 ⟨hwc2, hw, hlt, hd, hi, h2⟩
  obtain ⟨wb, eb, ib, db⟩ := checkPartialColInj _ f o1 fc1 bo bc w1 d1 i1 hb
  have hbo : bo = sptUnion o1 o2 := eb.trans (insertDiffKeys_eq_union o1 o2 w1 w2)
  obtain ⟨-, wl, el, il, dl⟩ := checkDelta f [] R bo bc livein flivein wb db ib hc
  refine ⟨wl, il, dl, ?_, ?_, co1, co2⟩
  · rw [el, hbo, e1, e2]; rfl
  · rw [← e1, ← e2]; exact sptWfUnion o1 o2 ⟨w1, w2⟩

/-- HOL `clash_tree_colouring_ok`, `If` case: both branches from the same live
set, the branch-difference names checked into the first branch's output, then
the condition registers. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "clash_tree_colouring_ok"
  (words_as_type_indexed_bitvec)]
theorem clashTreeColouringOk_If {width : Nat} [NeZero width] (cmp : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (c1 c2 : WordLangProgHOL (BitVec width))
    (ih1 : clashTreeGoal c1) (ih2 : clashTreeGoal c2) :
    clashTreeGoal (.ite cmp r ri c1 c2 : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, hlt, hd, hi, hc⟩
  rw [getClashTree.eq_def] at hc
  cases ri with
  | reg r2 =>
    dsimp only at hc
    obtain ⟨wl, il, dl, el, wu, co1, co2⟩ :=
      ifCore c1 c2 ih1 ih2 [r, r2] lt f live flive livein flivein hwc.1 hwc.2 hw hlt hd hi hc
    have hl : livein = getLive (.ite cmp r (.reg r2) c1 c2 : WordLangProgHOL (BitVec width))
        live lt := by
      rw [getLive, el]
      exact wfInsertSwap _ r r2 wu
    refine ⟨wl, il, ?_, hl, dl⟩
    show (∀ a b, sptDomain (sptInsert r2 () (sptInsert r ()
        (sptUnion (getLive c1 live lt) (getLive c2 live lt)))) a →
      sptDomain (sptInsert r2 () (sptInsert r ()
        (sptUnion (getLive c1 live lt) (getLive c2 live lt)))) b → f a = f b → a = b) ∧
      colouringOk f c1 live lt ∧ colouringOk f c2 live lt
    have hm : sptInsert r2 () (sptInsert r () (sptUnion (getLive c1 live lt)
        (getLive c2 live lt))) = livein := by
      rw [hl, getLive]
    rw [hm]
    exact ⟨il, co1, co2⟩
  | imm c =>
    dsimp only at hc
    obtain ⟨wl, il, dl, el, -, co1, co2⟩ :=
      ifCore c1 c2 ih1 ih2 [r] lt f live flive livein flivein hwc.1 hwc.2 hw hlt hd hi hc
    have hl : livein = getLive (.ite cmp r (.imm c) c1 c2 : WordLangProgHOL (BitVec width))
        live lt := by
      rw [getLive, el]; rfl
    refine ⟨wl, il, ?_, hl, dl⟩
    show (∀ a b, sptDomain (sptInsert r ()
        (sptUnion (getLive c1 live lt) (getLive c2 live lt))) a →
      sptDomain (sptInsert r ()
        (sptUnion (getLive c1 live lt) (getLive c2 live lt))) b → f a = f b → a = b) ∧
      colouringOk f c1 live lt ∧ colouringOk f c2 live lt
    have hm : sptInsert r () (sptUnion (getLive c1 live lt) (getLive c2 live lt)) = livein := by
      rw [hl, getLive]
    rw [hm]
    exact ⟨il, co1, co2⟩

end Flapjack.WordAlloc
