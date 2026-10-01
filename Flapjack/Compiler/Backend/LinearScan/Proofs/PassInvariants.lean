import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.ColorRegister
import Flapjack.Misc.Sptree.ToAList

/-!
# linear_scanProof: the two allocation passes

Ports of `linear_scanProofScript.sml:3550-3709`: the stack placement of
high physical registers `phystack_on_stack`, preservation of
`good_linear_scan_state` by one step of each allocation pass, and the
interval-beginning order `intbeg_less`. Renderings as in `GoodState` and
`ColorRegister`; HOL `fromAList` is `sptFromAList`, `union` `sptUnion`, and
`the [] (lookup r m)` is `miscThe [] (sptLookup r m)`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `phystack_on_stack` (`linear_scanProofScript.sml:3550-3553`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "phystack_on_stack_def"]
def phystackOnStack (l : List Nat) (st : LinearScanState) (sth : LinearScanHiddenState) :
    Prop :=
  ∀ r, r ∈ l ∧ isPhyVar r ∧ 2 * st.colormax ≤ r → st.colormax ≤ holEl r sth.colors

/-- The forced-forbidden set built from the colours of the forced partners. -/
private theorem forcedForbidden_domain (sth : LinearScanHiddenState) (fl : List Nat) (c : Nat) :
    sptDomain (sptFromAList ((fl.map (fun r => holEl r sth.colors)).map (fun c => (c, ())))) c ↔
      ∃ r, r ∈ fl ∧ c = holEl r sth.colors := by
  rw [sptDomainFromAList]
  simp only [List.map_map]
  show c ∈ fl.map ((Prod.fst ∘ fun c => (c, ())) ∘ fun r => holEl r sth.colors) ↔ _
  simp only [List.mem_map, Function.comp]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

/-- The shared part of both pass steps: after releasing inactive intervals, the
colouring step for a non-stack register with forced-forbidden colours. -/
private theorem passStepAux (st0 : LinearScanState) (sth : LinearScanHiddenState)
    (l preferred : List Nat) (forced_adj : Spt (List Nat)) (forced : List (Nat × Nat))
    (reg : Nat) (force : Bool) (mincol : Nat) (usePhy : Bool)
    (hnl : reg ∉ l)
    (hg0 : goodLinearScanState st0 sth l (holEl reg sth.int_beg) forced mincol)
    (hreg : reg < sth.colors.length)
    (hfl : forbiddenIsFromForcedList forced l reg (miscThe [] (sptLookup reg forced_adj)))
    (hfm : ∀ r, r ∈ miscThe [] (sptLookup reg forced_adj) → r ∈ l)
    (hbe : holEl reg sth.int_beg ≤ holEl reg sth.int_end)
    (hphy : isPhyVar reg = usePhy) :
    let ff := sptFromAList (((miscThe [] (sptLookup reg forced_adj)).map
      (fun r => holEl r sth.colors)).map (fun c => (c, ())))
    ∃ stout sthout, (.success stout, sthout) =
        linearRegAllocStepAux st0 (if usePhy then sptUnion st0.phyregs ff else ff)
          preferred reg (holEl reg sth.int_end) force sth ∧
      goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
      sthout.colors.length = sth.colors.length ∧
      sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
      (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
      (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
      stout.colormax = st0.colormax := by
  intro ff
  have g0 := goodLinearScanState_iff.mp hg0
  have hffdom := forcedForbidden_domain sth (miscThe [] (sptLookup reg forced_adj))
  have hff : forbiddenIsFromMapColorForced forced l sth.colors reg ff := by
    intro reg2 ⟨h2, hf⟩
    exact (hffdom _).mpr ⟨reg2, hfl reg2 ⟨h2, hf⟩, rfl⟩
  have hffsub : ∀ c, sptDomain ff c → ∃ r, c = holEl r sth.colors ∧ r ∈ l := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := (hffdom c).mp hc
    exact ⟨r, rfl, hfm r hr⟩
  cases usePhy with
  | true =>
    simp only [if_true]
    refine linearRegAllocStepAuxInvariants st0 sth l preferred _ forced reg force mincol
      ⟨hnl, hg0, hreg, ?_, ?_, ?_, hbe⟩
    · intro reg2 h
      rw [sptDomain_sptUnion]; exact Or.inr (hff reg2 h)
    · intro _ x hx
      rw [sptDomain_sptUnion]; exact Or.inl hx
    · intro c hc
      rw [sptDomain_sptUnion] at hc
      rcases hc with hc | hc
      · rw [g0.phy] at hc
        obtain ⟨r, h1, h2, _⟩ := hc
        exact ⟨r, h1, h2⟩
      · exact hffsub c hc
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact linearRegAllocStepAuxInvariants st0 sth l preferred _ forced reg force mincol
      ⟨hnl, hg0, hreg, hff, fun h => absurd (hphy ▸ h) (by simp), hffsub, hbe⟩

/-- Exact HOL `linear_reg_alloc_step_pass1_invariants`
(`linear_scanProofScript.sml:3555-3634`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_step_pass1_invariants"]
theorem linearRegAllocStepPass1Invariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
      (moves forced_adj : Spt (List Nat)) (forced : List (Nat × Nat)) (reg : Nat)
      (pos : Int) (mincol : Nat),
      reg ∉ l ∧ goodLinearScanState st sth l pos forced mincol ∧
      pos ≤ holEl reg sth.int_beg ∧ reg < sth.colors.length ∧
      forbiddenIsFromForcedList forced l reg (miscThe [] (sptLookup reg forced_adj)) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg forced_adj) → r ∈ l) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg forced_adj) → r < sth.colors.length) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg moves) → r < sth.colors.length) ∧
      holEl reg sth.int_beg ≤ holEl reg sth.int_end →
      ∃ stout sthout, (.success stout, sthout) =
          linearRegAllocStepPass1 forced_adj moves st reg sth ∧
        goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
        (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
        (phystackOnStack l st sth → phystackOnStack (reg :: l) stout sthout) ∧
        stout.colormax = st.colormax := by
  intro st sth l moves forced_adj forced reg pos mincol
    ⟨hnl, hg, hpos, hreg, hfl, hfm, hfb, hmb, hbe⟩
  have g := goodLinearScanState_iff.mp hg
  obtain ⟨st0, hrun0, hg0, hmax0⟩ :=
    removeInactiveIntervalsInvariants (holEl reg sth.int_beg) st sth l pos forced mincol
      ⟨hg, hpos⟩
  have g0 := goodLinearScanState_iff.mp hg0
  have hrb : reg < sth.int_beg.length := by rw [g.lenBeg]; exact hreg
  have hre : reg < sth.int_end.length := by rw [g.lenEnd]; exact hreg
  have hnact : ∀ e : Int, (e, reg) ∉ st0.active := fun e he => hnl (g0.activeMem _ he)
  -- spilling `reg` itself
  have spillCase : ∃ stout sthout, (.success stout, sthout) = spillRegister st0 reg sth ∧
      goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
      sthout.colors.length = sth.colors.length ∧
      sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
      (∀ r, r ≠ reg → holEl r sth.colors = holEl r sthout.colors) ∧
      stout.colormax = st.colormax ∧ st.colormax ≤ holEl reg sthout.colors := by
    obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hcol, hmax, hle⟩ :=
      spillRegisterInvariants st0 sth l _ forced reg mincol
        ⟨hnact, Or.inr hnl, hg0, hreg, Int.le_refl _⟩
    exact ⟨stout, sthout, hrun, hgood, hl, hb, he, hcol, by rw [hmax, hmax0],
      by rw [← hmax0]; exact hle⟩
  simp only [linearRegAllocStepPass1, Translator.Monadic.MonadBase.bind, intBegSubEqn,
    if_pos hrb, intEndSubEqn, if_pos hre, ← hrun0]
  by_cases hstack : isStackVar reg = true
  · rw [if_pos hstack]
    have hnphy : isPhyVar reg = false := by
      simp only [isStackVar, isPhyVar, decide_eq_true_eq] at hstack ⊢
      exact decide_eq_false (by omega)
    obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hcol, hmax, _⟩ := spillCase
    refine ⟨stout, sthout, hrun, hgood, hl, hb, he,
      fun r hr => (hcol r fun e => hr (e ▸ List.mem_cons_self)).symm,
      fun r ⟨hr, _⟩ => (hcol r fun e => hnl (e ▸ hr)).symm, ?_, hmax⟩
    intro hps r ⟨hr, hp, hle⟩
    have e : r ≠ reg := fun e => by rw [e, hnphy] at hp; cases hp
    have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left e
    rw [hmax] at hle ⊢
    rw [← hcol r e]
    exact hps r ⟨hrl, hp, hle⟩
  · rw [if_neg hstack]
    simp only [Translator.Monadic.MonadBase.bind, stExMapColorsSub _ sth hfb]
    by_cases hp : isPhyVar reg = true
    · rw [if_pos hp]
      by_cases hlt : reg < 2 * st0.colormax
      · rw [if_pos hlt]
        obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, hmax⟩ :=
          passStepAux st0 sth l [] forced_adj forced reg true mincol true hnl hg0 hreg hfl hfm
            hbe hp
        refine ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, ?_, by rw [hmax, hmax0]⟩
        intro hps r ⟨hr, hrp, hle⟩
        have e : r ≠ reg := fun e => by rw [e, hmax, hmax0] at hle; rw [← hmax0] at hle; omega
        have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left e
        rw [hmax, hmax0] at hle ⊢
        rw [hc2 r ⟨hrl, hrp⟩]
        exact hps r ⟨hrl, hrp, hle⟩
      · rw [if_neg hlt]
        obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hcol, hmax, hle⟩ := spillCase
        refine ⟨stout, sthout, hrun, hgood, hl, hb, he,
          fun r hr => (hcol r fun e => hr (e ▸ List.mem_cons_self)).symm,
          fun r ⟨hr, _⟩ => (hcol r fun e => hnl (e ▸ hr)).symm, ?_, hmax⟩
        intro hps r ⟨hr, hrp, hle'⟩
        rw [hmax]
        by_cases e : r = reg
        · rw [e]; exact hle
        · have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left e
          rw [hmax] at hle'
          rw [← hcol r e]
          exact hps r ⟨hrl, hrp, hle'⟩
    · rw [if_neg hp]
      simp only [Translator.Monadic.MonadBase.bind, stExMapColorsSub _ sth hmb]
      obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, hmax⟩ :=
        passStepAux st0 sth l _ forced_adj forced reg false mincol false hnl hg0 hreg hfl hfm
          hbe (by simpa using hp)
      refine ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, ?_, by rw [hmax, hmax0]⟩
      intro hps r ⟨hr, hrp, hle⟩
      have e : r ≠ reg := fun e => hp (e ▸ hrp)
      have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left e
      rw [hmax, hmax0] at hle ⊢
      rw [hc2 r ⟨hrl, hrp⟩]
      exact hps r ⟨hrl, hrp, hle⟩

/-- Exact HOL `linear_reg_alloc_step_pass2_invariants`
(`linear_scanProofScript.sml:3636-3690`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_step_pass2_invariants"]
theorem linearRegAllocStepPass2Invariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
      (moves forced_adj : Spt (List Nat)) (forced : List (Nat × Nat)) (reg : Nat)
      (pos : Int) (mincol : Nat),
      reg ∉ l ∧ goodLinearScanState st sth l pos forced mincol ∧
      pos ≤ holEl reg sth.int_beg ∧ reg < sth.colors.length ∧
      forbiddenIsFromForcedList forced l reg (miscThe [] (sptLookup reg forced_adj)) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg forced_adj) → r ∈ l) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg forced_adj) → r < sth.colors.length) ∧
      (∀ r, r ∈ miscThe [] (sptLookup reg moves) → r < sth.colors.length) ∧
      holEl reg sth.int_beg ≤ holEl reg sth.int_end →
      ∃ stout sthout, (.success stout, sthout) =
          linearRegAllocStepPass2 forced_adj moves st reg sth ∧
        goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
        (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
        stout.colormax = st.colormax := by
  intro st sth l moves forced_adj forced reg pos mincol
    ⟨hnl, hg, hpos, hreg, hfl, hfm, hfb, hmb, hbe⟩
  have g := goodLinearScanState_iff.mp hg
  obtain ⟨st0, hrun0, hg0, hmax0⟩ :=
    removeInactiveIntervalsInvariants (holEl reg sth.int_beg) st sth l pos forced mincol
      ⟨hg, hpos⟩
  have hrb : reg < sth.int_beg.length := by rw [g.lenBeg]; exact hreg
  have hre : reg < sth.int_end.length := by rw [g.lenEnd]; exact hreg
  simp only [linearRegAllocStepPass2, Translator.Monadic.MonadBase.bind, intBegSubEqn,
    if_pos hrb, intEndSubEqn, if_pos hre, ← hrun0, stExMapColorsSub _ sth hfb,
    stExMapColorsSub _ sth hmb, ret]
  by_cases hp : isPhyVar reg = true
  · rw [if_pos hp]
    obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, hmax⟩ :=
      passStepAux st0 sth l [] forced_adj forced reg false mincol true hnl hg0 hreg hfl hfm
        hbe hp
    exact ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, by rw [hmax, hmax0]⟩
  · rw [if_neg hp]
    obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, hmax⟩ :=
      passStepAux st0 sth l _ forced_adj forced reg false mincol false hnl hg0 hreg hfl hfm
        hbe (by simpa using hp)
    exact ⟨stout, sthout, hrun, hgood, hl, hb, he, hc1, hc2, by rw [hmax, hmax0]⟩

/-- Exact HOL `intbeg_less` (`linear_scanProofScript.sml:3692-3694`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "intbeg_less_def"]
def intbegLess (int_beg : List Int) (r1 r2 : Nat) : Prop :=
  holLex (· < ·) (· ≤ ·) (holEl r1 int_beg, r1) (holEl r2 int_beg, r2)

/-- Exact HOL `intbeg_less_transitive` (`linear_scanProofScript.sml:3696-3701`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "intbeg_less_transitive"]
theorem intbegLessTransitive : ∀ (int_beg : List Int), holTransitive (intbegLess int_beg) := by
  intro int_beg x y z ⟨h1, h2⟩
  simp only [intbegLess, holLex] at h1 h2 ⊢
  omega

/-- Exact HOL `intbeg_less_total` (`linear_scanProofScript.sml:3703-3708`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "intbeg_less_total"]
theorem intbegLessTotal : ∀ (int_beg : List Int), holTotal (intbegLess int_beg) := by
  intro int_beg x y
  simp only [intbegLess, holLex]
  omega

/-- `intbeg_less` holds in both directions only between equal registers. -/
private theorem intbegLess_antisymm {int_beg : List Int} {r1 r2 : Nat}
    (h1 : intbegLess int_beg r1 r2) (h2 : intbegLess int_beg r2 r1) : r1 = r2 := by
  simp only [intbegLess, holLex] at h1 h2
  omega

/-- Exact HOL `st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma`
(`linear_scanProofScript.sml:3710-3793`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma"]
theorem stExFoldlLinearRegAllocStepPassnInvariantsLemma :
    ∀ (regl : List Nat) (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
      (pos : Int) (b : Bool) (moves forced_adj : Spt (List Nat)) (forced : List (Nat × Nat))
      (mincol : Nat),
      holSorted (intbegLess sth.int_beg) regl ∧
      (∀ r1 r2, r1 ∈ l ∧ r2 ∈ regl → intbegLess sth.int_beg r1 r2) ∧
      regl.Nodup ∧ (∀ r, r ∈ l → r ∉ regl) ∧
      goodLinearScanState st sth l pos forced mincol ∧
      (∀ r, r ∈ regl → pos ≤ holEl r sth.int_beg) ∧
      (∀ r, r ∈ regl → r < sth.colors.length) ∧
      (∀ r, forbiddenIsFromForcedSublist (l ++ regl) forced sth.int_beg r
        (miscThe [] (sptLookup r forced_adj))) ∧
      (∀ x, x ∈ forced → x.1 ∈ l ++ regl ∧ x.2 ∈ l ++ regl) ∧
      (∀ r1, ∀ r2, r2 ∈ miscThe [] (sptLookup r1 forced_adj) → r2 < sth.colors.length) ∧
      (∀ r1, ∀ r2, r2 ∈ miscThe [] (sptLookup r1 moves) → r2 < sth.colors.length) ∧
      (∀ r, r ∈ regl → holEl r sth.int_beg ≤ holEl r sth.int_end) →
      ∃ stout sthout posout, (.success stout, sthout) =
          stExFoldl ((if b then linearRegAllocStepPass1 else linearRegAllocStepPass2)
            forced_adj moves) st regl sth ∧
        goodLinearScanState stout sthout (regl.reverse ++ l) posout forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ l ++ regl → holEl r sthout.colors = holEl r sth.colors) ∧
        (b → phystackOnStack l st sth → phystackOnStack (regl.reverse ++ l) stout sthout) ∧
        stout.colormax = st.colormax := by
  intro regl
  induction regl with
  | nil =>
      intro st sth l pos b moves forced_adj forced mincol ⟨_, _, _, _, hg, _⟩
      exact ⟨st, sth, pos, rfl, by simpa using hg, rfl, rfl, rfl, fun _ _ => rfl,
        fun _ h => by simpa using h, rfl⟩
  | cons h t ih =>
      intro st sth l pos b moves forced_adj forced mincol
        ⟨hs, hless, hnd, hnot, hg, hpos, hlen, hsub, hfp, hfb, hmb, hbe⟩
      have htr := intbegLessTransitive sth.int_beg
      obtain ⟨hst, hht⟩ := (holSortedEq _ t h htr).mp hs
      have hhl : h ∉ l := fun hm => hnot h hm List.mem_cons_self
      obtain ⟨hht', hndt⟩ := List.nodup_cons.mp hnd
      -- the forced partners recorded for `h` are already allocated
      have hfm : ∀ r, r ∈ miscThe [] (sptLookup h forced_adj) → r ∈ l := by
        intro r hr
        obtain ⟨hne, hpair, hlt⟩ := (hsub h r).mpr ⟨hr, by simp⟩
        have hrm : r ∈ l ++ h :: t := by
          rcases hpair with hp | hp
          · exact (hfp _ hp).1
          · exact (hfp _ hp).2
        rcases List.mem_append.mp hrm with hrl | hrt
        · exact hrl
        · rcases List.mem_cons.mp hrt with rfl | hrt
          · exact absurd rfl hne
          · exact absurd (intbegLess_antisymm hlt (hht r hrt)) (fun e => hne e.symm)
      have hfl : forbiddenIsFromForcedList forced l h (miscThe [] (sptLookup h forced_adj)) := by
        intro reg2 ⟨h2, hpair⟩
        have hne : h ≠ reg2 := fun e => hhl (e ▸ h2)
        exact ((hsub h reg2).mp ⟨hne, hpair, hless reg2 h ⟨h2, List.mem_cons_self⟩⟩).1
      -- one pass step on `h`
      obtain ⟨stmid, sthmid, hrun, hgmid, hlmid, hbmid, hemid, hcmid, hpmid, hmmid⟩ :
          ∃ stmid sthmid, (.success stmid, sthmid) =
              (if b then linearRegAllocStepPass1 else linearRegAllocStepPass2)
                forced_adj moves st h sth ∧
            goodLinearScanState stmid sthmid (h :: l) (holEl h sth.int_beg) forced mincol ∧
            sthmid.colors.length = sth.colors.length ∧
            sthmid.int_beg = sth.int_beg ∧ sthmid.int_end = sth.int_end ∧
            (∀ r, r ∉ h :: l → holEl r sthmid.colors = holEl r sth.colors) ∧
            (b → phystackOnStack l st sth → phystackOnStack (h :: l) stmid sthmid) ∧
            stmid.colormax = st.colormax := by
        have hyps := And.intro hhl (And.intro hg (And.intro (hpos h List.mem_cons_self)
          (And.intro (hlen h List.mem_cons_self) (And.intro hfl (And.intro hfm
            (And.intro (hfb h) (And.intro (hmb h) (hbe h List.mem_cons_self))))))))
        cases b with
        | true =>
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
            linearRegAllocStepPass1Invariants st sth l moves forced_adj forced h pos mincol hyps
          exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun _ => a10.1, a10.2⟩
        | false =>
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
            linearRegAllocStepPass2Invariants st sth l moves forced_adj forced h pos mincol hyps
          exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun hb => absurd hb (by simp), a10⟩
      have hmemEq : ∀ r, r ∈ (h :: l) ++ t ↔ r ∈ l ++ h :: t := by
        intro r
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro ((h1 | h1) | h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
        · rintro (h1 | h1 | h1)
          · exact Or.inl (Or.inr h1)
          · exact Or.inl (Or.inl h1)
          · exact Or.inr h1
      obtain ⟨stout, sthout, posout, hrun', hgood, hl, hb, he, hc, hp, hm⟩ :=
        ih stmid sthmid (h :: l) (holEl h sth.int_beg) b moves forced_adj forced mincol
          ⟨by rw [hbmid]; exact hst,
            fun r1 r2 ⟨h1, h2⟩ => by
              rw [hbmid]
              rcases List.mem_cons.mp h1 with rfl | h1
              · exact hht r2 h2
              · exact hless r1 r2 ⟨h1, List.mem_cons_of_mem _ h2⟩,
            hndt,
            fun r hr => by
              rcases List.mem_cons.mp hr with rfl | hr
              · exact hht'
              · exact fun h' => hnot r hr (List.mem_cons_of_mem _ h'),
            hgmid,
            fun r hr => by
              rw [hbmid]
              have := hht r hr
              simp only [intbegLess, holLex] at this
              omega,
            fun r hr => by rw [hlmid]; exact hlen r (List.mem_cons_of_mem _ hr),
            fun r reg2 => by
              rw [hbmid, hmemEq r]
              exact hsub r reg2,
            fun x hx => ⟨(hmemEq _).mpr (hfp x hx).1, (hmemEq _).mpr (hfp x hx).2⟩,
            fun r1 r2 hr => by rw [hlmid]; exact hfb r1 r2 hr,
            fun r1 r2 hr => by rw [hlmid]; exact hmb r1 r2 hr,
            fun r hr => by rw [hbmid, hemid]; exact hbe r (List.mem_cons_of_mem _ hr)⟩
      refine ⟨stout, sthout, posout, ?_, ?_, by rw [hl, hlmid], by rw [hb, hbmid],
        by rw [he, hemid], fun r hr => ?_, fun hbt hps => ?_, by rw [hm, hmmid]⟩
      · simp only [stExFoldl, Translator.Monadic.MonadBase.bind, ← hrun]
        exact hrun'
      · simpa [List.reverse_cons, List.append_assoc] using hgood
      · have h1 : r ∉ (h :: l) ++ t := fun h' => hr ((hmemEq r).mp h')
        have h2 : r ∉ h :: l := fun h' => h1 (List.mem_append_left _ h')
        rw [hc r h1, hcmid r h2]
      · have := hp hbt (hpmid hbt hps)
        simpa [List.reverse_cons, List.append_assoc] using this

/-- Exact HOL `st_ex_FOLDL_linear_reg_alloc_step_passn_invariants`
(`linear_scanProofScript.sml:3795-3820`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "st_ex_FOLDL_linear_reg_alloc_step_passn_invariants"]
theorem stExFoldlLinearRegAllocStepPassnInvariants :
    ∀ (regl : List Nat) (st : LinearScanState) (sth : LinearScanHiddenState) (pos : Int)
      (b : Bool) (moves forced_adj : Spt (List Nat)) (forced : List (Nat × Nat))
      (mincol : Nat),
      holSorted (intbegLess sth.int_beg) regl ∧ regl.Nodup ∧
      goodLinearScanState st sth [] pos forced mincol ∧
      (∀ r, r ∈ regl → pos ≤ holEl r sth.int_beg) ∧
      (∀ r, r ∈ regl → r < sth.colors.length) ∧
      (∀ r, forbiddenIsFromForcedSublist regl forced sth.int_beg r
        (miscThe [] (sptLookup r forced_adj))) ∧
      (∀ x, x ∈ forced → x.1 ∈ regl ∧ x.2 ∈ regl) ∧
      (∀ r1, ∀ r2, r2 ∈ miscThe [] (sptLookup r1 forced_adj) → r2 < sth.colors.length) ∧
      (∀ r1, ∀ r2, r2 ∈ miscThe [] (sptLookup r1 moves) → r2 < sth.colors.length) ∧
      (∀ r, r ∈ regl → holEl r sth.int_beg ≤ holEl r sth.int_end) →
      ∃ stout sthout posout, (.success stout, sthout) =
          stExFoldl ((if b then linearRegAllocStepPass1 else linearRegAllocStepPass2)
            forced_adj moves) st regl sth ∧
        goodLinearScanState stout sthout regl.reverse posout forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ regl → holEl r sthout.colors = holEl r sth.colors) ∧
        (b → phystackOnStack regl.reverse stout sthout) ∧
        stout.colormax = st.colormax := by
  intro regl st sth pos b moves forced_adj forced mincol
    ⟨hs, hnd, hg, hpos, hlen, hsub, hfp, hfb, hmb, hbe⟩
  obtain ⟨stout, sthout, posout, hrun, hgood, hl, hb, he, hc, hp, hm⟩ :=
    stExFoldlLinearRegAllocStepPassnInvariantsLemma regl st sth [] pos b moves forced_adj
      forced mincol
      ⟨hs, fun _ _ hh => absurd hh.1 (List.not_mem_nil), hnd, fun _ hh => absurd hh List.not_mem_nil, hg, hpos, hlen,
        (by simpa using hsub), (by simpa using hfp), hfb, hmb, hbe⟩
  refine ⟨stout, sthout, posout, hrun, (by simpa using hgood), hl, hb, he,
    fun r hr => hc r (by simpa using hr), fun hbt => ?_, hm⟩
  have := hp hbt (fun _ hh => absurd hh.1 List.not_mem_nil)
  simpa using this

end Flapjack.LinearScan
