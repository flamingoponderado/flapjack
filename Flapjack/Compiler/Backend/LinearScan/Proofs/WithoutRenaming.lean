import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.IntervalsCorrect
import Flapjack.Compiler.Backend.LinearScan.Proofs.IntervalMonad
import Flapjack.Compiler.Backend.LinearScan.Proofs.LiveTree

/-!
# linear_scanProof: `linear_reg_alloc_without_renaming_correct`

Port of `linear_scanProofScript.sml:5471-5564`: computing the intervals of a
clash tree and running the interval allocator yields a colouring accepted by
`check_clash_tree`. Renderings as in `IntervalsCorrect`; HOL `THE` is the
tagged `holThe`, `the 0` the tagged `miscThe`, and the monadic sequence
`do m1; m2 od` is `ignoreBind m1 m2`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `linear_reg_alloc_without_renaming_correct`
(`linear_scanProofScript.sml:5471-5564`); `sth` and `reglist_unsorted` are
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_without_renaming_correct"]
theorem linearRegAllocWithoutRenamingCorrect (reglist_unsorted : List Nat)
    (sth : LinearScanHiddenState) :
    ∀ (k : Nat) (moves : List (Nat × (Nat × Nat))) (ct : ClashTree) (forced : List (Nat × Nat)),
      (∀ i, i < sth.int_beg.length → 0 < holEl i sth.int_beg) ∧
      (∀ i, i < sth.int_end.length → 0 < holEl i sth.int_end) ∧
      sth.int_end.length = sth.int_beg.length ∧
      (∀ r, r ∈ reglist_unsorted ↔ inClashTree ct r) ∧
      (∀ r, inClashTree ct r → r < sth.int_beg.length) ∧
      (∀ x, x ∈ forced → inClashTree ct x.1 ∧ inClashTree ct x.2) ∧
      (∀ x, x ∈ moves.map Prod.snd → x.1 < sth.colors.length ∧ x.2 < sth.colors.length) ∧
      reglist_unsorted.length ≤ sth.sorted_regs.length ∧
      moves.length ≤ sth.sorted_moves.length ∧
      sth.colors.length = sth.int_beg.length ∧
      sth.int_end.length = sth.int_beg.length ∧
      reglist_unsorted.Nodup →
      ∃ sthout livein flivein,
        ignoreBind (getIntervalsCtMonad ct)
          (linearRegAllocIntervals k forced moves reglist_unsorted) sth = (.success (), sthout) ∧
        checkClashTree (fun r => holEl r sthout.colors) ct .ln .ln = some (livein, flivein) ∧
        (∀ r, inClashTree ct r →
          if isPhyVar r then holEl r sthout.colors = r / 2
          else if isStackVar r then k ≤ holEl r sthout.colors
          else True) ∧
        (∀ x, x ∈ forced → holEl x.1 sthout.colors = holEl x.2 sthout.colors → x.1 = x.2) ∧
        sthout.colors.length = sth.colors.length := by
  intro k moves ct forced
    ⟨hpb, hpe, hlen, hmem, hct, hfct, hmvb, hlrs, hlms, hlcb, _, hnd⟩
  -- the interval monad
  rcases hgi : getIntervalsCt ct with ⟨n, ib, ie⟩
  obtain ⟨sthint, hrun1, hqb, hqe, hlb1, hle1, hrec1⟩ :=
    getIntervalsCtMonadCorrect ct sth n ib ie ⟨hpb, hpe, hgi, hlen, hct⟩
  have hc1 : sthint.colors = sth.colors := by
    have h := congrArg LinearScanHiddenState.colors hrec1; exact h
  have hr1 : sthint.sorted_regs = sth.sorted_regs := by
    have h := congrArg LinearScanHiddenState.sorted_regs hrec1; exact h
  have hm1 : sthint.sorted_moves = sth.sorted_moves := by
    have h := congrArg LinearScanHiddenState.sorted_moves hrec1; exact h
  -- the same intervals through the live tree
  rcases hgl : getIntervals (fixDomination (getLiveTree ct)) 0 .ln .ln with ⟨n', ib', ie'⟩
  obtain ⟨heqb, heqe⟩ := getIntervalsCtEq ct ib ib' ie ie' n n' ⟨hgi.symm, hgl.symm⟩
  obtain ⟨hble, _⟩ := getIntervalsBegLessEnd (fixDomination (getLiveTree ct)) 0 .ln .ln n' ib' ie'
    ⟨fun r h => by simp [sptDomain] at h, fun x h => by simp [sptDomain] at h, hgl.symm⟩
  obtain ⟨hdb, hde⟩ := getIntervalsDomainEqLiveTreeRegisters (getLiveTree ct) n' ib' ie' hgl.symm
  have hregs : ∀ r, liveTreeRegisters (fixDomination (getLiveTree ct)) r ↔ inClashTree ct r := by
    intro r
    rw [fixDominationLiveTreeRegisters, ← inClashTreeEqLiveTreeRegisters]
  have hdomb : ∀ r, sptDomain ib' r ↔ inClashTree ct r := fun r => by rw [hdb]; exact hregs r
  have hdome : ∀ r, sptDomain ie' r ↔ inClashTree ct r := fun r => by rw [hde]; exact hregs r
  -- the hidden arrays agree with the interval maps on the clash-tree registers
  have hlook : ∀ r, inClashTree ct r →
      sptLookup r ib' = some (holEl r sthint.int_beg) ∧
      sptLookup r ie' = some (holEl r sthint.int_end) := by
    intro r hr
    have hrb : r < sthint.int_beg.length := by rw [hlb1]; exact hct r hr
    have hre : r < sthint.int_end.length := by rw [hle1, hlen]; exact hct r hr
    have hsb : (sptLookup r ib').isSome := (hdomb r).mpr hr
    have hse : (sptLookup r ie').isSome := (hdome r).mpr hr
    obtain ⟨hb1, hb2⟩ := hqb r hrb
    obtain ⟨he1, he2⟩ := hqe r hre
    rw [heqb r] at hb1 hb2
    rw [heqe r] at he1 he2
    refine ⟨hb2.mp ?_, he2.mp ?_⟩
    · refine Int.not_lt.mp fun h => ?_
      rw [hb1.mp h] at hsb; cases hsb
    · refine Int.not_lt.mp fun h => ?_
      rw [he1.mp h] at hse; cases hse
  -- run the interval allocator
  obtain ⟨sthout, hrun2, hinter, hconv, hforced, hlout⟩ :=
    linearRegAllocIntervalsCorrect k forced moves reglist_unsorted sthint
      ⟨fun x hx => ⟨(hmem _).mpr (hfct x hx).1, (hmem _).mpr (hfct x hx).2⟩,
        fun x hx => by rw [hc1]; exact hmvb x hx,
        fun r hr => by rw [hc1, hlcb]; exact hct r ((hmem r).mp hr),
        fun r hr => by
          obtain ⟨h1, h2⟩ := hlook r ((hmem r).mp hr)
          have := hble r ((hdomb r).mpr ((hmem r).mp hr))
          rw [h1, h2] at this
          exact this,
        hnd,
        fun r hr => by rw [hlb1]; exact hct r ((hmem r).mp hr),
        by rw [hc1, hlb1]; exact hlcb,
        by rw [hle1, hlb1]; exact hlen,
        by rw [hr1]; exact hlrs,
        by rw [hm1]; exact hlms⟩
  -- the colouring passes the interval and tree checkers
  have hci : checkIntervals (fun r => holEl r sthout.colors) ib' ie' := by
    intro r1 r2 ⟨h1, h2, hi, he⟩
    have c1 := (hdomb r1).mp h1
    have c2 := (hdomb r2).mp h2
    obtain ⟨b1, e1⟩ := hlook r1 c1
    obtain ⟨b2, e2⟩ := hlook r2 c2
    rw [b1, e1, b2, e2] at hi
    exact hinter r1 r2 ⟨(hmem r1).mpr c1, (hmem r2).mpr c2, hi, he⟩
  obtain ⟨lo, flo, hclt⟩ :=
    checkIntervalsCheckLiveTree (getLiveTree ct) n' ib' ie' _ ⟨hgl.symm, hci⟩
  obtain ⟨lo', flo', hclt'⟩ := fixDominationCheckLiveTree _ (getLiveTree ct) lo flo hclt
  obtain ⟨livein, flivein, hcct⟩ := getLiveTreeCorrectLN _ ct lo' flo' hclt'
  refine ⟨sthout, livein, flivein, ?_, hcct, fun r hr => hconv r ((hmem r).mpr hr), hforced,
    by rw [hlout, hc1]⟩
  simp only [ignoreBind, hrun1, hrun2]
