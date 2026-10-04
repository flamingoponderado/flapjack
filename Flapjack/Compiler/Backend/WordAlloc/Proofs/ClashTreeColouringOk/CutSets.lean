import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashTreeColouringOk.Leaves

/-!
# `clash_tree_colouring_ok` `Alloc`, `Install` and `FFI` cases

The cut-set cases of `word_allocProofScript.sml:2813-3309`
`clash_tree_colouring_ok` (proof `word_allocProofScript.sml:3030-3088`): the cut
sets are checked as a fixed `Set` by `check_col_INJ` (`wf_names` gives `wf` of
their union), followed by the read registers. The untagged helpers are Flapjack
proof infrastructure for the tagged cases.
-/

namespace Flapjack.WordAlloc

open Flapjack.RegAlloc

/-- A checked `Set` returns the fixed set (HOL `check_col_INJ`; Flapjack
infrastructure). -/
theorem checkSet (f : Nat → Nat) (t live flive a b : NumSet)
    (hc : checkClashTree f (.set t) live flive = some (a, b)) :
    a = t ∧ (∀ x y, sptDomain a x → sptDomain a y → f x = f y → x = y) ∧
      sptDomain b = (fun y => ∃ x, sptDomain a x ∧ f x = y) := by
  unfold checkClashTree at hc
  exact checkColInj f t a b hc

/-- The checked `Seq (Delta [] R) (Set t)` tree of `Alloc`/`FFI` (Flapjack
infrastructure). -/
theorem readsAfterSet (f : Nat → Nat) (R : List Nat) (t live flive livein flivein : NumSet)
    (ht : sptWf t = true)
    (hc : checkClashTree f (.seq (.delta [] R) (.set t)) live flive = some (livein, flivein)) :
    sptWf livein = true ∧ livein = numsetListInsert R t ∧
      (∀ a b, sptDomain livein a → sptDomain livein b → f a = f b → a = b) ∧
      sptDomain flivein = (fun y => ∃ x, sptDomain livein x ∧ f x = y) := by
  unfold checkClashTree at hc
  cases hs : checkClashTree f (.set t) live flive with
  | none => rw [hs] at hc; cases hc
  | some p =>
  obtain ⟨a, b⟩ := p
  rw [hs] at hc
  dsimp only at hc
  obtain ⟨rfl, ia, da⟩ := checkSet f t live flive a b hs
  obtain ⟨-, wl, el, il, dl⟩ := checkDelta f [] R a b livein flivein ht da ia hc
  exact ⟨wl, el, il, dl⟩

/-- HOL `clash_tree_colouring_ok`, `Alloc` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_Alloc {width : Nat} [NeZero width] (n : Nat)
    (names : WordLangCutsetsHOL) :
    clashTreeGoal (.alloc n names : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  have hu : sptWf (sptUnion names.1 names.2) = true := sptWfUnion _ _ ⟨hwc.1, hwc.2⟩
  obtain ⟨wl, el, il, dl⟩ := readsAfterSet f [n] _ live flive livein flivein hu hc
  have hl : livein = getLive (.alloc n names : WordLangProgHOL (BitVec width)) live lt := by
    rw [getLive, el]; rfl
  refine ⟨wl, il, ⟨by rw [← hl]; exact il, fun a b ha hb hab => ?_⟩, hl, dl⟩
  rw [sptDomain_sptUnion] at ha hb
  exact hi a b (ha.resolve_left (by simp [getWrites, sptDomain]))
    (hb.resolve_left (by simp [getWrites, sptDomain])) hab

/-- HOL `clash_tree_colouring_ok`, `FFI` case. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_FFI {width : Nat} [NeZero width]
    (fi : Flapjack.Basis.Pure.MlString.MlString) (cptr clen ptr len : Nat)
    (names : WordLangCutsetsHOL) :
    clashTreeGoal (.ffi fi cptr clen ptr len names : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  have hu : sptWf (sptUnion names.1 names.2) = true := sptWfUnion _ _ ⟨hwc.1, hwc.2⟩
  obtain ⟨wl, el, il, dl⟩ :=
    readsAfterSet f [cptr, clen, ptr, len] _ live flive livein flivein hu hc
  have hl : livein =
      getLive (.ffi fi cptr clen ptr len names : WordLangProgHOL (BitVec width)) live lt := by
    rw [getLive, el]; rfl
  refine ⟨wl, il, ⟨by rw [← hl]; exact il, fun a b ha hb hab => ?_⟩, hl, dl⟩
  rw [sptDomain_sptUnion] at ha hb
  exact hi a b (ha.resolve_left (by simp [getWrites, sptDomain]))
    (hb.resolve_left (by simp [getWrites, sptDomain])) hab

/-- HOL `clash_tree_colouring_ok`, `Install` case: the written `r1` is checked
against the incoming live set, then the cut sets, then the four read
registers. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem clashTreeColouringOk_Install {width : Nat} [NeZero width] (r1 r2 r3 r4 : Nat)
    (names : WordLangCutsetsHOL) :
    clashTreeGoal (.install r1 r2 r3 r4 names : WordLangProgHOL (BitVec width)) := by
  rintro lt f live flive livein flivein ⟨hwc, hw, -, hd, hi, hc⟩
  rw [getClashTree] at hc
  have hu : sptWf (sptUnion names.1 names.2) = true := sptWfUnion _ _ ⟨hwc.1, hwc.2⟩
  unfold checkClashTree at hc
  cases hr : checkClashTree f (.seq (.set (sptUnion names.1 names.2)) (.delta [r1] []))
      live flive with
  | none => rw [hr] at hc; cases hc
  | some p =>
  obtain ⟨a, b⟩ := p
  rw [hr] at hc
  dsimp only at hc
  unfold checkClashTree at hr
  cases hw1 : checkClashTree f (.delta [r1] []) live flive with
  | none => rw [hw1] at hr; cases hr
  | some p1 =>
  obtain ⟨o1, c1⟩ := p1
  rw [hw1] at hr
  dsimp only at hr
  obtain ⟨hinjW, -, -, -, -⟩ := checkDelta f [r1] [] live flive o1 c1 hw hd hi hw1
  obtain ⟨rfl, ia, da⟩ := checkSet f _ o1 c1 a b hr
  obtain ⟨-, wl, el, il, dl⟩ := checkDelta f [] [r4, r3, r2, r1] _ b livein flivein hu da ia hc
  have hl : livein =
      getLive (.install r1 r2 r3 r4 names : WordLangProgHOL (BitVec width)) live lt := by
    rw [getLive, el]; rfl
  refine ⟨wl, il, ⟨by rw [← hl]; exact il, fun x y hx hy hxy => ?_⟩, hl, dl⟩
  rw [sptDomain_sptUnion] at hx hy
  have hW : ∀ k, sptDomain (getWrites (.install r1 r2 r3 r4 names :
      WordLangProgHOL (BitVec width))) k → k ∈ [r1] := fun k hk => (writesSingle r1 k).mp hk
  refine hinjW x y ?_ ?_ hxy
  · rcases hx with hx | hx
    · exact Or.inr (hW x hx)
    · exact Or.inl hx
  · rcases hy with hy | hy
    · exact Or.inr (hW y hy)
    · exact Or.inl hy

end Flapjack.WordAlloc
