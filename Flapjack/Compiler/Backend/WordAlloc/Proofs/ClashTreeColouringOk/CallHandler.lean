import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.CutSets
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Inst

/-!
# `clash_tree_colouring_ok` returning `Call` with handler

The returning-`Call`-with-exception-handler branch of the `Call` case of
`word_allocProofScript.sml:2813-3309` `clash_tree_colouring_ok` (proof
`word_allocProofScript.sml:3253-3268`): a `Branch (SOME live_set)` whose left
tree checks the return names and the return handler, whose right tree checks the
handler variable and the handler program, and whose fixed set is the cut sets
with the arguments. The untagged helpers are Flapjack proof infrastructure for
the tagged case.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- Injectivity transfers between equal domains (Flapjack infrastructure). -/
theorem inj_of_domain_iff (f : Nat → Nat) (s t : NumSet) (h : ∀ k, sptDomain s k ↔ sptDomain t k)
    (hi : ∀ a b, sptDomain s a → sptDomain s b → f a = f b → a = b) :
    ∀ a b, sptDomain t a → sptDomain t b → f a = f b → a = b :=
  fun a b ha hb => hi a b ((h a).mpr ha) ((h b).mpr hb)

/-- The checked `Seq (Set t) tree` subtree of a returning call: the program tree is
checked first, then the fixed set (Flapjack infrastructure). -/
theorem setAfterTree (f : Nat → Nat) (t : NumSet) (tree : ClashTree)
    (live flive a b : NumSet)
    (hc : checkClashTree f (.seq (.set t) tree) live flive = some (a, b)) :
    ∃ o c, checkClashTree f tree live flive = some (o, c) ∧
      (∀ x y, sptDomain t x → sptDomain t y → f x = f y → x = y) := by
  unfold checkClashTree at hc
  cases h : checkClashTree f tree live flive with
  | none => rw [h] at hc; cases hc
  | some p =>
  obtain ⟨o, c⟩ := p
  rw [h] at hc
  dsimp only at hc
  obtain ⟨rfl, ia, -⟩ := checkSet f t o c a b hc
  exact ⟨o, c, rfl, ia⟩

/-- HOL `clash_tree_colouring_ok`, `Call` case, returning call with an exception
handler (`word_allocProofScript.sml:3253-3268`); the induction hypotheses are
those of the return handler and the handler program. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_CallHandler {width : Nat} [NeZero width] (vs : List Nat)
    (cutsets : WordLangCutsetsHOL) (rh : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (v' : Nat) (hp : WordLangProgHOL (BitVec width))
    (l1' l2' : Nat) (ihRet : clashTreeGoal rh) (ihHandler : clashTreeGoal hp) :
    clashTreeGoal (.call (some (vs, cutsets, rh, l1, l2)) dest args (some (v', hp, l1', l2')) :
      WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, hlt, hd, hi, hc⟩
  obtain ⟨hwn, hwr, hwh⟩ := hwc
  rw [getClashTree.eq_def] at hc
  dsimp only at hc
  unfold checkClashTree at hc
  cases hl : checkClashTree f (.seq (.set (numsetListInsert vs (sptUnion cutsets.1 cutsets.2)))
      (getClashTree rh lt)) live flive with
  | none => rw [hl] at hc; cases hc
  | some pl =>
  obtain ⟨lo, lc⟩ := pl
  rw [hl] at hc
  dsimp only at hc
  cases hr : checkClashTree f (.seq (.set (sptInsert v' () (sptUnion cutsets.1 cutsets.2)))
      (getClashTree hp lt)) live flive with
  | none => rw [hr] at hc; cases hc
  | some pr =>
  obtain ⟨ro, rc⟩ := pr
  rw [hr] at hc
  dsimp only at hc
  obtain ⟨rfl, il, dl⟩ := checkColInj f _ livein flivein hc
  obtain ⟨o1, c1, h1, iVs⟩ := setAfterTree f _ _ live flive lo lc hl
  obtain ⟨o2, c2, h2, iV⟩ := setAfterTree f _ _ live flive ro rc hr
  obtain ⟨-, -, coR, -, -⟩ := ihRet lt f live flive o1 c1 ⟨hwr, hw, hlt, hd, hi, h1⟩
  obtain ⟨-, -, coH, -, -⟩ := ihHandler lt f live flive o2 c2 ⟨hwh, hw, hlt, hd, hi, h2⟩
  have hwu : sptWf (sptUnion cutsets.1 cutsets.2) = true := sptWfUnion _ _ ⟨hwn.1, hwn.2⟩
  have hcomm : ∀ k, sptDomain (sptUnion cutsets.1 cutsets.2) k ↔
      sptDomain (sptUnion cutsets.2 cutsets.1) k := by
    intro k; rw [sptDomain_sptUnion, sptDomain_sptUnion]; exact Or.comm
  refine ⟨sptWfUnion _ _ ⟨hwu, sptWf_numsetListInsert _ rfl args⟩, il, ⟨?_, ?_, coR, ?_, coH⟩,
    by rw [getLive], dl⟩
  · refine inj_of_domain_iff f _ _ (fun k => ?_) il
    simp only [sptDomain_sptUnion]
    exact or_congr Or.comm Iff.rfl
  · refine inj_of_domain_iff f _ _ (fun k => ?_) iVs
    rw [domainNumsetListInsert, domainNumsetListInsert]
    exact or_congr (hcomm k) Iff.rfl
  · refine inj_of_domain_iff f _ _ (fun k => ?_) iV
    rw [sptDomain_sptInsert_iff, sptDomain_sptInsert_iff]
    exact or_congr Iff.rfl (hcomm k)

end Flapjack.WordAlloc
