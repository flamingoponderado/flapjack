import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.SpillRegister
import Flapjack.Compiler.Backend.LinearScan.Proofs.EdgesToAdjlist

/-!
# linear_scanProof: stealing, colouring and the allocation step

Ports of `linear_scanProofScript.sml:3073-3547`: dropping a duplicated head
register from `good_linear_scan_state`, the shape of `find_last_stealable`,
`color_register` and its preservation of the invariant, and the colouring step
`linear_reg_alloc_step_aux` through `find_spill`. Renderings as in `GoodState`
and `SpillRegister`; HOL `st with active updated_by f` is
`{ st with active := f st.active }`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `state_invariants_remove_head` (`linear_scanProofScript.sml:3073-3084`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "state_invariants_remove_head"]
theorem stateInvariantsRemoveHead :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (reg : Nat) (l : List Nat)
      (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat),
      reg ∈ l ∧ goodLinearScanState st sth (reg :: l) pos forced mincol →
      goodLinearScanState st sth l pos forced mincol := by
  intro st sth reg l pos forced mincol ⟨hrl, hg⟩
  have g := goodLinearScanState_iff.mp hg
  have hm : ∀ r, r ∈ reg :: l ↔ r ∈ l := fun r => by
    constructor
    · intro h; rcases List.mem_cons.mp h with rfl | h
      · exact hrl
      · exact h
    · exact List.mem_cons_of_mem _
  have hsub : (l.filter isPhyVar).Sublist ((reg :: l).filter isPhyVar) := by
    rw [List.filter_cons]
    split
    · exact List.sublist_cons_self _ _
    · exact List.Sublist.refl _
  exact goodLinearScanState_iff.mpr {
    lenBeg := g.lenBeg
    lenEnd := g.lenEnd
    distinct := g.distinct
    bound := fun r hr => g.bound r ((hm r).mpr hr)
    stack := fun r hr => g.stack r ((hm r).mpr hr)
    phy := by
      rw [g.phy]; funext c; apply propext
      exact ⟨fun ⟨r, h1, h2, h3⟩ => ⟨r, h1, (hm r).mp h2, h3⟩,
        fun ⟨r, h1, h2, h3⟩ => ⟨r, h1, (hm r).mpr h2, h3⟩⟩
    phyDistinct := g.phyDistinct.sublist (hsub.map _)
    pool := g.pool
    active := g.active
    numMax := g.numMax
    maxStack := g.maxStack
    colMax := fun r hr => g.colMax r ((hm r).mpr hr)
    beg := fun r hr => g.beg r ((hm r).mpr hr)
    live := fun r hr => g.live r ((hm r).mpr hr)
    ends := fun r hr => g.ends r ((hm r).mpr hr)
    inter := fun r1 r2 ⟨h1, h2, h⟩ => g.inter r1 r2 ⟨(hm r1).mpr h1, (hm r2).mpr h2, h⟩
    sorted := g.sorted
    activeEnd := g.activeEnd
    activeMem := fun x hx => (hm _).mp (g.activeMem x hx)
    forcedOk := fun x hx ⟨h1, h2, h⟩ => g.forcedOk x hx ⟨(hm _).mpr h1, (hm _).mpr h2, h⟩
    minNum := g.minNum
    minAll := fun c hc => by
      apply g.minAll c
      rcases List.mem_append.mp hc with hc | hc
      · exact List.mem_append_left _ hc
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc) }

/-- Exact HOL `find_last_stealable_success` (`linear_scanProofScript.sml:3086-3098`);
polymorphic in the interval-end carrier as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_last_stealable_success"]
theorem findLastStealableSuccess {α : Type} :
    ∀ (forbidden : NumSet) (sth : LinearScanHiddenState) (active : List (α × Nat)),
      (∀ x, x ∈ active → x.2 < sth.colors.length) →
      ∃ optout, findLastStealable active forbidden sth = (.success optout, sth) := by
  intro forbidden sth active
  induction active with
  | nil => intro _; exact ⟨none, rfl⟩
  | cons x xs ih =>
      intro hb
      obtain ⟨o, ho⟩ := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
      have hx := hb x List.mem_cons_self
      simp only [findLastStealable, Translator.Monadic.MonadBase.bind, ho]
      cases o with
      | some p => exact ⟨_, rfl⟩
      | none =>
          simp only [Translator.Monadic.MonadBase.bind, colorsSubEqn, if_pos hx]
          split <;> exact ⟨_, rfl⟩

/-- Exact HOL `find_last_stealable_output` (`linear_scanProofScript.sml:3100-3130`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_last_stealable_output"]
theorem findLastStealableOutput {α : Type} :
    ∀ (forbidden : NumSet) (sth : LinearScanHiddenState) (active : List (α × Nat))
      (steal : α × Nat) (rest : List (α × Nat)),
      findLastStealable active forbidden sth = (.success (some (steal, rest)), sth) →
      ¬ isPhyVar steal.2 ∧ sptLookup (holEl steal.2 sth.colors) forbidden = none ∧
        ∃ l1 l2, rest = l1 ++ l2 ∧ active = l1 ++ steal :: l2 := by
  intro forbidden sth active
  induction active with
  | nil => intro steal rest h; cases h
  | cons x xs ih =>
      intro steal rest h
      simp only [findLastStealable, Translator.Monadic.MonadBase.bind] at h
      rcases hrec : findLastStealable xs forbidden sth with ⟨r, s'⟩
      rw [hrec] at h
      cases r with
      | failure e => cases h
      | success o =>
          cases o with
          | some p =>
              obtain ⟨st', rs⟩ := p
              simp only [ret, Prod.mk.injEq, Exc.success.injEq, Option.some.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              obtain ⟨hp, hl, l1, l2, hr, ha⟩ := ih st' rs hrec
              exact ⟨hp, hl, x :: l1, l2, by rw [hr]; rfl, by rw [ha]; rfl⟩
          | none =>
              simp only [Translator.Monadic.MonadBase.bind, colorsSubEqn] at h
              by_cases hx : x.2 < s'.colors.length
              · rw [if_pos hx] at h
                simp only at h
                split at h
                · next hc =>
                  simp only [ret, Prod.mk.injEq, Exc.success.injEq, Option.some.injEq] at h
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
                  exact ⟨hc.1, hc.2, [], xs, rfl, rfl⟩
                · simp only [ret, Prod.mk.injEq, Exc.success.injEq] at h
                  cases h.1
              · rw [if_neg hx] at h
                cases h

/-- Exact HOL `good_linear_scan_state_active_length_colors`
(`linear_scanProofScript.sml:3132-3140`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "good_linear_scan_state_active_length_colors"]
theorem goodLinearScanStateActiveLengthColors :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (mincol : Nat),
      goodLinearScanState st sth l pos forced mincol →
      ∀ x, x ∈ st.active → x.2 < sth.colors.length := by
  intro st sth l pos forced mincol hg x hx
  have g := goodLinearScanState_iff.mp hg
  exact g.bound _ (g.activeMem x hx)

/-- Exact HOL `color_register_eq` (`linear_scanProofScript.sml:3142-3159`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "color_register_eq"]
theorem colorRegisterEq :
    ∀ (st : LinearScanState) (reg col : Nat) (rend : Int),
      colorRegister st reg col rend =
        ignoreBind (updateColors reg col)
          (ret { st with
            active := addActiveInterval (rend, reg) st.active
            phyregs := (if isPhyVar reg then sptInsert col () st.phyregs else st.phyregs) }) := by
  intro st reg col rend
  simp only [colorRegister]
  split <;> rfl

/-- Exact HOL `color_register_invariants` (`linear_scanProofScript.sml:3161-3360`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "color_register_invariants"]
theorem colorRegisterInvariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (reg col : Nat) (forbidden : NumSet) (mincol : Nat),
      goodLinearScanState st sth l pos forced mincol ∧
      forbiddenIsFromMapColorForced forced l sth.colors reg forbidden ∧
      ¬ sptDomain forbidden col ∧
      (isPhyVar reg → ∀ x, sptDomain st.phyregs x → sptDomain forbidden x) ∧
      col ∉ st.colorpool ++ st.active.map (fun x => holEl x.2 sth.colors) ∧
      holEl reg sth.int_beg = pos ∧
      holEl reg sth.int_beg ≤ holEl reg sth.int_end ∧
      col < st.colornum ∧ mincol ≤ col ∧ reg < sth.colors.length ∧ reg ∉ l →
      ∃ stout sthout, (.success stout, sthout) =
          colorRegister st reg col (holEl reg sth.int_end) sth ∧
        goodLinearScanState stout sthout (reg :: l) pos forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ≠ reg → holEl r sth.colors = holEl r sthout.colors) ∧
        stout.colormax = st.colormax := by
  intro st sth l pos forced reg col forbidden mincol
    ⟨hg, hforb, hcol, hphyS, hnm, hb, hbe, hcn, hmin, hreg, hnl⟩
  have g := goodLinearScanState_iff.mp hg
  let c' := sth.colors.set reg col
  let aNew := addActiveInterval (holEl reg sth.int_end, reg) st.active
  have hcreg : holEl reg c' = col := by
    simp only [c']; rw [holEl_set _ _ _ _ hreg, if_pos rfl]
  have hcne : ∀ r, r ≠ reg → holEl r c' = holEl r sth.colors := fun r h => by
    simp only [c']; rw [holEl_set _ _ _ _ hreg, if_neg (Ne.symm h)]
  have hnact : ∀ x, x ∈ st.active → x.2 ≠ reg := fun x hx e =>
    hnl (e ▸ g.activeMem x hx)
  obtain ⟨hsortA, l1, l2, hact, hA⟩ :=
    addActiveIntervalOutput (β := Unit) (holEl reg sth.int_end) reg st.active () aNew
      ⟨g.sorted, rfl⟩
  have hmemA : ∀ x, x ∈ aNew ↔ x = (holEl reg sth.int_end, reg) ∨ x ∈ st.active := by
    intro x
    rw [hA, hact]
    simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have hcl : ∀ r, r ∈ reg :: l → r ≠ reg → r ∈ l ∧ holEl r c' = holEl r sth.colors :=
    fun r hr hne => ⟨(List.mem_cons.mp hr).resolve_left hne, hcne r hne⟩
  -- a register of `l` coloured `col` cannot be live at `pos`
  have hnotlive : ∀ r, r ∈ l → holEl r sth.colors = col → holEl r sth.int_end < pos := by
    intro r hr he
    refine Int.lt_of_not_ge fun hle => hnm ?_
    have hm := g.live r hr ⟨hle, by
      rw [he]; have := g.numMax; omega⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, by simp only; exact he⟩)
  -- a forced partner of `reg` in `l` is not coloured `col`
  have hforced : ∀ r, r ∈ l → ((r, reg) ∈ forced ∨ (reg, r) ∈ forced) →
      holEl r sth.colors ≠ col := by
    intro r hr hf he
    exact hcol (he ▸ hforb r ⟨hr, hf⟩)
  let stout : LinearScanState := { st with
    active := aNew
    phyregs := (if isPhyVar reg then sptInsert col () st.phyregs else st.phyregs) }
  refine ⟨stout, { sth with colors := c' }, ?run, goodLinearScanState_iff.mpr ?good, List.length_set,
    rfl, rfl, fun r h => (hcne r h).symm, rfl⟩
  case run =>
    rw [colorRegisterEq]
    simp only [ignoreBind, updateColorsEqn, if_pos hreg, ret]
    rfl
  case good =>
  exact {
    lenBeg := by rw [List.length_set]; exact g.lenBeg
    lenEnd := by rw [List.length_set]; exact g.lenEnd
    distinct := by
      show (st.colorpool ++ aNew.map (fun x => holEl x.2 c')).Nodup
      have hmap : ∀ m : List (Int × Nat), (∀ x, x ∈ m → x ∈ st.active) →
          m.map (fun x => holEl x.2 c') = m.map (fun x => holEl x.2 sth.colors) :=
        fun m hm => List.map_congr_left fun x hx => hcne _ (hnact x (hm x hx))
      have h1 : ∀ x, x ∈ l1 → x ∈ st.active := fun x hx => by
        rw [hact]; exact List.mem_append_left _ hx
      have h2 : ∀ x, x ∈ l2 → x ∈ st.active := fun x hx => by
        rw [hact]; exact List.mem_append_right _ hx
      rw [hA, List.map_append, List.map_cons, hmap l1 h1, hmap l2 h2, hcreg,
        ← List.append_assoc]
      refine List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, ?_⟩)
      · rw [List.append_assoc, ← List.map_append, ← hact]; exact hnm
      · rw [List.append_assoc, ← List.map_append, ← hact]; exact g.distinct
    bound := fun r hr => by
      rw [List.length_set]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hreg
      · exact g.bound r hr
    stack := fun r hr => by
      show holEl r c' < st.stacknum
      by_cases e : r = reg
      · rw [e, hcreg]; have := g.numMax; have := g.maxStack; omega
      · rw [(hcl r hr e).2]; exact g.stack r (hcl r hr e).1
    phy := by
      show sptDomain (if isPhyVar reg then sptInsert col () st.phyregs else st.phyregs) =
        fun c => ∃ r, c = holEl r c' ∧ (r ∈ reg :: l ∧ isPhyVar r ∧ holEl r c' < st.colormax)
      funext c; apply propext
      have old := congrFun g.phy c
      split
      · next hp =>
        show sptMem c (sptInsert col () st.phyregs) ↔ _
        rw [sptMem_sptInsert]
        show c = col ∨ sptDomain st.phyregs c ↔ _
        rw [old]
        constructor
        · rintro (rfl | ⟨r, h1, h2, h3, h4⟩)
          · exact ⟨reg, hcreg.symm, List.mem_cons_self, hp,
              by rw [hcreg]; have := g.numMax; omega⟩
          · have e : r ≠ reg := fun e => hnl (e ▸ h2)
            exact ⟨r, by rw [hcne r e]; exact h1, List.mem_cons_of_mem _ h2, h3,
              by rw [hcne r e]; exact h4⟩
        · rintro ⟨r, h1, h2, h3, h4⟩
          by_cases e : r = reg
          · left; rw [h1, e, hcreg]
          · obtain ⟨hrl, hc⟩ := hcl r h2 e
            right; exact ⟨r, by rw [← hc]; exact h1, hrl, h3, by rw [← hc]; exact h4⟩
      · next hp =>
        rw [old]
        constructor
        · rintro ⟨r, h1, h2, h3, h4⟩
          have e : r ≠ reg := fun e => hnl (e ▸ h2)
          exact ⟨r, by rw [hcne r e]; exact h1, List.mem_cons_of_mem _ h2, h3,
            by rw [hcne r e]; exact h4⟩
        · rintro ⟨r, h1, h2, h3, h4⟩
          have e : r ≠ reg := fun e => hp (e ▸ h3)
          obtain ⟨hrl, hc⟩ := hcl r h2 e
          exact ⟨r, by rw [← hc]; exact h1, hrl, h3, by rw [← hc]; exact h4⟩
    phyDistinct := by
      show (((reg :: l).filter isPhyVar).map (fun r => holEl r c')).Nodup
      have hmap : (l.filter isPhyVar).map (fun r => holEl r c') =
          (l.filter isPhyVar).map (fun r => holEl r sth.colors) :=
        List.map_congr_left fun r hr => hcne r fun e => hnl (e ▸ (List.mem_filter.mp hr).1)
      rw [List.filter_cons]
      split
      · next hp =>
        rw [List.map_cons, hmap, hcreg]
        refine List.nodup_cons.mpr ⟨fun hm => ?_, g.phyDistinct⟩
        obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
        obtain ⟨hrl, hrp⟩ := List.mem_filter.mp hr
        have hd : sptDomain st.phyregs col := by
          rw [g.phy]
          exact ⟨r, he.symm, hrl, hrp, by rw [he]; have := g.numMax; omega⟩
        exact hcol (hphyS hp col hd)
      · rw [hmap]; exact g.phyDistinct
    pool := g.pool
    active := fun x hx => by
      show holEl x.2 c' < st.colornum
      rcases (hmemA x).mp hx with rfl | hx
      · simp only; rw [hcreg]; exact hcn
      · rw [hcne _ (hnact x hx)]; exact g.active x hx
    numMax := g.numMax
    maxStack := g.maxStack
    colMax := fun r hr h => by
      show holEl r c' < st.colornum
      by_cases e : r = reg
      · rw [e, hcreg]; exact hcn
      · have h' : holEl r c' < st.colormax := h
        rw [(hcl r hr e).2] at h' ⊢; exact g.colMax r (hcl r hr e).1 h'
    beg := fun r hr => by
      by_cases e : r = reg
      · rw [e, hb]; exact Int.le_refl _
      · exact g.beg r (hcl r hr e).1
    live := fun r hr ⟨h1, h2⟩ => by
      show (holEl r sth.int_end, r) ∈ aNew
      by_cases e : r = reg
      · subst e; exact (hmemA _).mpr (Or.inl rfl)
      · have h2' : holEl r c' < st.colormax := h2
        obtain ⟨hrl, hc⟩ := hcl r hr e
        rw [hc] at h2'
        exact (hmemA _).mpr (Or.inr (g.live r hrl ⟨h1, h2'⟩))
    ends := fun r hr hm => by
      show pos ≤ 1 + holEl r sth.int_end
      by_cases e : r = reg
      · rw [e]; omega
      · rcases (hmemA _).mp hm with h | h
        · simp only [Prod.mk.injEq] at h; exact absurd h.2 e
        · exact g.ends r (hcl r hr e).1 h
    inter := fun r1 r2 ⟨h1, h2, hi, heq⟩ => by
      have heq' : holEl r1 c' = holEl r2 c' := heq
      by_cases e1 : r1 = reg
      · by_cases e2 : r2 = reg
        · rw [e1, e2]
        · obtain ⟨hl2, hc2⟩ := hcl r2 h2 e2
          rw [e1, hcreg, hc2] at heq'
          have := hnotlive r2 hl2 heq'.symm
          have := g.beg r2 hl2
          subst e1
          simp only [intervalIntersect] at hi
          omega
      · by_cases e2 : r2 = reg
        · obtain ⟨hl1, hc1⟩ := hcl r1 h1 e1
          rw [e2, hcreg, hc1] at heq'
          have := hnotlive r1 hl1 heq'
          have := g.beg r1 hl1
          subst e2
          simp only [intervalIntersect] at hi
          omega
        · obtain ⟨hl1, hc1⟩ := hcl r1 h1 e1
          obtain ⟨hl2, hc2⟩ := hcl r2 h2 e2
          rw [hc1, hc2] at heq'
          exact g.inter r1 r2 ⟨hl1, hl2, hi, heq'⟩
    sorted := hsortA
    activeEnd := fun x hx => by
      rcases (hmemA x).mp hx with rfl | hx
      · rfl
      · exact g.activeEnd x hx
    activeMem := fun x hx => by
      rcases (hmemA x).mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (g.activeMem x hx)
    forcedOk := fun x hx ⟨h1, h2, heq⟩ => by
      have heq' : holEl x.1 c' = holEl x.2 c' := heq
      by_cases e1 : x.1 = reg
      · by_cases e2 : x.2 = reg
        · rw [e1, e2]
        · obtain ⟨hl2, hc2⟩ := hcl _ h2 e2
          rw [e1, hcreg, hc2] at heq'
          exact absurd heq'.symm (hforced _ hl2 (Or.inr (by rw [← e1]; exact hx)))
      · by_cases e2 : x.2 = reg
        · obtain ⟨hl1, hc1⟩ := hcl _ h1 e1
          rw [e2, hcreg, hc1] at heq'
          exact absurd heq' (hforced _ hl1 (Or.inl (by rw [← e2]; exact hx)))
        · obtain ⟨hl1, hc1⟩ := hcl _ h1 e1
          obtain ⟨hl2, hc2⟩ := hcl _ h2 e2
          rw [hc1, hc2] at heq'
          exact g.forcedOk x hx ⟨hl1, hl2, heq'⟩
    minNum := g.minNum
    minAll := fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact g.minAll c (List.mem_append_left _ hc)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
        show mincol ≤ holEl r c'
        by_cases e : r = reg
        · rw [e, hcreg]; exact hmin
        · obtain ⟨hrl, hc'⟩ := hcl r hr e
          rw [hc']
          exact g.minAll _ (List.mem_append_right _ (List.mem_map_of_mem hrl)) }

/-- Distinct active colours: an active list whose colours are distinct holds at
most one entry per register. -/
private theorem not_mem_of_map_nodup (colors : List Nat) (l1 l2 : List (Int × Nat))
    (x : Int × Nat) (h : ((l1 ++ x :: l2).map (fun y => holEl y.2 colors)).Nodup) :
    (∀ e : Int, (e, x.2) ∉ l1) ∧ (∀ e : Int, (e, x.2) ∉ l2) := by
  rw [List.map_append, List.map_cons] at h
  have h' := (List.perm_middle.nodup_iff).mp h
  have hx := (List.nodup_cons.mp h').1
  refine ⟨fun e he => hx ?_, fun e he => hx ?_⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨(e, x.2), he, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨(e, x.2), he, rfl⟩)

/-- Exact HOL `find_spill_invariants` (`linear_scanProofScript.sml:3362-3476`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_spill_invariants"]
theorem findSpillInvariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
      (forbidden : NumSet) (forced : List (Nat × Nat)) (reg : Nat) (force : Bool)
      (mincol : Nat),
      reg ∉ l ∧ goodLinearScanState st sth l (holEl reg sth.int_beg) forced mincol ∧
      reg < sth.colors.length ∧
      forbiddenIsFromMapColorForced forced l sth.colors reg forbidden ∧
      (isPhyVar reg → ∀ x, sptDomain st.phyregs x → sptDomain forbidden x) ∧
      holEl reg sth.int_beg ≤ holEl reg sth.int_end →
      ∃ stout sthout, (.success stout, sthout) =
          findSpill st forbidden reg (holEl reg sth.int_end) force sth ∧
        goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
        (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
        stout.colormax = st.colormax := by
  intro st sth l forbidden forced reg force mincol ⟨hnl, hg, hreg, hforb, hphyS, hbe⟩
  have g := goodLinearScanState_iff.mp hg
  have hnact : ∀ e : Int, (e, reg) ∉ st.active := fun e he => hnl (g.activeMem _ he)
  have hlen := goodLinearScanStateActiveLengthColors st sth l _ forced mincol hg
  obtain ⟨optsteal, hsteal⟩ := findLastStealableSuccess forbidden sth st.active hlen
  -- the plain spill of `reg`
  have spillCase : ∃ stout sthout, (.success stout, sthout) = spillRegister st reg sth ∧
      goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
      sthout.colors.length = sth.colors.length ∧
      sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
      (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
      (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
      stout.colormax = st.colormax := by
    obtain ⟨stout, sthout, hrun, hgood, hl, hb, he, hcol, hmax, _⟩ :=
      spillRegisterInvariants st sth l _ forced reg mincol
        ⟨hnact, Or.inr hnl, hg, hreg, Int.le_refl _⟩
    refine ⟨stout, sthout, hrun, hgood, hl, hb, he, fun r hr => ?_, fun r ⟨hr, _⟩ => ?_, hmax⟩
    · exact (hcol r fun e => hr (e ▸ List.mem_cons_self)).symm
    · exact (hcol r fun e => hnl (e ▸ hr)).symm
  simp only [findSpill, Translator.Monadic.MonadBase.bind, hsteal]
  cases optsteal with
  | none => exact spillCase
  | some p =>
    obtain ⟨⟨se, sr⟩, rest⟩ := p
    simp only
    split
    · next hforce =>
      obtain ⟨hnphy, hlk, l1, l2, hrest, hact⟩ :=
        findLastStealableOutput forbidden sth st.active (se, sr) rest hsteal
      simp only at hnphy hlk
      have hmem : (se, sr) ∈ st.active := by rw [hact]; simp
      have hsrl : sr ∈ l := g.activeMem _ hmem
      have hsr : sr < sth.colors.length := g.bound sr hsrl
      have hsrreg : sr ≠ reg := fun e => hnl (e ▸ hsrl)
      have hdist : ((l1 ++ (se, sr) :: l2).map (fun y => holEl y.2 sth.colors)).Nodup := by
        rw [← hact]; exact (List.nodup_append.mp g.distinct).2.1
      obtain ⟨hn1, hn2⟩ := not_mem_of_map_nodup sth.colors l1 l2 (se, sr) hdist
      have hfilt : st.active.filter (fun x => decide (x.2 ≠ sr)) = rest := by
        rw [hact, hrest, List.filter_append, List.filter_cons, filterMemActive sr l1 hn1,
          filterMemActive sr l2 hn2]
        simp
      simp only [Translator.Monadic.MonadBase.bind, colorsSubEqn, if_pos hsr]
      -- spill the stolen register
      obtain ⟨st1, sth1, hrun1, hgood1, hlen1, hcol1, hmax1, hb1, he1, _⟩ :=
        spillRegisterFilterInvariants st sth l _ forced sr mincol
          ⟨Or.inl hnphy, hg, hsr, g.beg sr hsrl⟩
      rw [hfilt] at hrun1
      rw [← hrun1]
      simp only
      have hgood1' := stateInvariantsRemoveHead st1 sth1 sr l _ forced mincol ⟨hsrl, hgood1⟩
      -- the state fields that spilling does not touch
      obtain ⟨hst1pool, hst1act, hst1phy, hst1num⟩ :
          st1.colorpool = st.colorpool ∧ st1.active = rest ∧ st1.phyregs = st.phyregs ∧
            st1.colornum = st.colornum := by
        simp only [spillRegister, ignoreBind, updateColorsEqn, if_pos hsr, ret,
          Prod.mk.injEq, Exc.success.injEq] at hrun1
        obtain ⟨rfl, rfl⟩ := hrun1
        exact ⟨rfl, rfl, rfl, rfl⟩
      have hsc : ¬ sptDomain forbidden (holEl sr sth.colors) := by
        intro hd; unfold sptDomain at hd; rw [hlk] at hd; cases hd
      have hforb1 : forbiddenIsFromMapColorForced forced l sth1.colors reg forbidden := by
        intro reg2 ⟨h2, hf⟩
        by_cases e : reg2 = sr
        · exact absurd (e ▸ hforb reg2 ⟨h2, hf⟩) hsc
        · rw [← hcol1 reg2 e]; exact hforb reg2 ⟨h2, hf⟩
      have hrestmem : ∀ x, x ∈ rest → x ∈ st.active ∧ x.2 ≠ sr := by
        intro x hx
        rw [hrest] at hx
        rw [hact]
        rcases List.mem_append.mp hx with hx | hx
        · refine ⟨List.mem_append_left _ hx, fun e => hn1 x.1 ?_⟩
          rw [← e]; exact hx
        · refine ⟨List.mem_append_right _ (List.mem_cons_of_mem _ hx), fun e => hn2 x.1 ?_⟩
          rw [← e]; exact hx
      have hnotin : holEl sr sth.colors ∉
          st1.colorpool ++ st1.active.map (fun x => holEl x.2 sth1.colors) := by
        rw [hst1pool, hst1act]
        have hmap : rest.map (fun x => holEl x.2 sth1.colors) =
            rest.map (fun x => holEl x.2 sth.colors) :=
          List.map_congr_left fun x hx => (hcol1 _ (hrestmem x hx).2).symm
        rw [hmap, hrest]
        have h := g.distinct
        rw [hact, List.map_append, List.map_cons, ← List.append_assoc] at h
        have h' := (List.perm_middle.nodup_iff).mp h
        rw [List.map_append, ← List.append_assoc]
        exact (List.nodup_cons.mp h').1
      obtain ⟨st2, sth2, hrun2, hgood2, hlen2, hb2, he2, hcol2, hmax2⟩ :=
        colorRegisterInvariants st1 sth1 l _ forced reg (holEl sr sth.colors) forbidden mincol
          ⟨hgood1', hforb1, hsc, by rw [hst1phy]; exact hphyS, hnotin, by rw [hb1],
            by rw [hb1, he1]; exact hbe, by rw [hst1num]; exact g.active _ hmem,
            g.minAll _ (List.mem_append_right _ (List.mem_map_of_mem hsrl)),
            by rw [hlen1]; exact hreg, hnl⟩
      rw [he1] at hrun2
      refine ⟨st2, sth2, hrun2, hgood2, by rw [hlen2, hlen1],
        by rw [hb2, hb1], by rw [he2, he1], fun r hr => ?_, fun r ⟨hr, hp⟩ => ?_,
        by rw [hmax2, hmax1]⟩
      · have e1 : r ≠ reg := fun e => hr (e ▸ List.mem_cons_self)
        have e2 : r ≠ sr := fun e => hr (e ▸ List.mem_cons_of_mem _ hsrl)
        rw [← hcol2 r e1, ← hcol1 r e2]
      · have e1 : r ≠ reg := fun e => hnl (e ▸ hr)
        have e2 : r ≠ sr := fun e => hnphy (e ▸ hp)
        rw [← hcol2 r e1, ← hcol1 r e2]
    · exact spillCase

/-- `good_linear_scan_state` survives replacing the colour pool by a sublist. -/
private theorem good_pool_sublist {st : LinearScanState} {sth : LinearScanHiddenState}
    {l : List Nat} {pos : Int} {forced : List (Nat × Nat)} {mincol : Nat} {p : List Nat}
    (g : GoodFields st sth l pos forced mincol) (hp : p.Sublist st.colorpool) :
    GoodFields { st with colorpool := p } sth l pos forced mincol :=
  { g with
    distinct := g.distinct.sublist (hp.append_right _)
    pool := fun c hc => g.pool c (hp.subset hc)
    minAll := fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact g.minAll c (List.mem_append_left _ (hp.subset hc))
      · exact g.minAll c (List.mem_append_right _ hc) }

/-- Exact HOL `linear_reg_alloc_step_aux_invariants`
(`linear_scanProofScript.sml:3478-3540`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_step_aux_invariants"]
theorem linearRegAllocStepAuxInvariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l preferred : List Nat)
      (forbidden : NumSet) (forced : List (Nat × Nat)) (reg : Nat) (force : Bool)
      (mincol : Nat),
      reg ∉ l ∧ goodLinearScanState st sth l (holEl reg sth.int_beg) forced mincol ∧
      reg < sth.colors.length ∧
      forbiddenIsFromMapColorForced forced l sth.colors reg forbidden ∧
      (isPhyVar reg → ∀ x, sptDomain st.phyregs x → sptDomain forbidden x) ∧
      (∀ c, sptDomain forbidden c → ∃ r, c = holEl r sth.colors ∧ r ∈ l) ∧
      holEl reg sth.int_beg ≤ holEl reg sth.int_end →
      ∃ stout sthout, (.success stout, sthout) =
          linearRegAllocStepAux st forbidden preferred reg (holEl reg sth.int_end) force sth ∧
        goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
        (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
        stout.colormax = st.colormax := by
  intro st sth l preferred forbidden forced reg force mincol
    ⟨hnl, hg, hreg, hforb, hphyS, hsub, hbe⟩
  have g := goodLinearScanState_iff.mp hg
  -- the colour-register finish shared by the two colouring branches
  have finish : ∀ (st' : LinearScanState) (col : Nat),
      GoodFields st' sth l (holEl reg sth.int_beg) forced mincol →
      st'.phyregs = st.phyregs → st'.colormax = st.colormax →
      ¬ sptDomain forbidden col →
      col ∉ st'.colorpool ++ st'.active.map (fun x => holEl x.2 sth.colors) →
      col < st'.colornum → mincol ≤ col →
      ∃ stout sthout, (.success stout, sthout) =
          colorRegister st' reg col (holEl reg sth.int_end) sth ∧
        goodLinearScanState stout sthout (reg :: l) (holEl reg sth.int_beg) forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ∉ reg :: l → holEl r sthout.colors = holEl r sth.colors) ∧
        (∀ r, r ∈ l ∧ isPhyVar r → holEl r sthout.colors = holEl r sth.colors) ∧
        stout.colormax = st.colormax := by
    intro st' col g' hphy hmax hcol hnm hcn hmin
    obtain ⟨stout, sthout, hrun, hgood, hlen, hb, he, hc, hm⟩ :=
      colorRegisterInvariants st' sth l _ forced reg col forbidden mincol
        ⟨goodLinearScanState_iff.mpr g', hforb, hcol, by rw [hphy]; exact hphyS, hnm, rfl,
          hbe, hcn, hmin, hreg, hnl⟩
    refine ⟨stout, sthout, hrun, hgood, hlen, hb, he, fun r hr => ?_, fun r ⟨hr, _⟩ => ?_,
      by rw [hm, hmax]⟩
    · exact (hc r fun e => hr (e ▸ List.mem_cons_self)).symm
    · exact (hc r fun e => hnl (e ▸ hr)).symm
  rcases hfl : findColorInList (preferred.filter (fun c => decide (c ∈ st.colorpool)))
      forbidden with _ | ⟨col, rest⟩
  · rcases hfc : findColor st forbidden with ⟨st', _ | col⟩
    · have hst : st' = st := by
        simp only [findColor] at hfc
        split at hfc
        · cases hfc
        · simp only [findColorInColornum] at hfc
          split at hfc
          · exact (Prod.mk.inj hfc).1.symm
          · cases hfc
      simp only [linearRegAllocStepAux, hfl, hfc, hst]
      exact findSpillInvariants st sth l forbidden forced reg force mincol
        ⟨hnl, hg, hreg, hforb, hphyS, hbe⟩
    · simp only [linearRegAllocStepAux, hfl, hfc]
      obtain ⟨hgood', hcn, hnd, heq⟩ :=
        findColorInvariants st forbidden st' col sth l _ forced mincol ⟨hg, hsub, hfc⟩
      have g'' := goodLinearScanState_iff.mp hgood'
      have g' : GoodFields st' sth l (holEl reg sth.int_beg) forced mincol :=
        good_pool_sublist (st := { st' with colorpool := col :: st'.colorpool }) g''
          (List.sublist_cons_self col st'.colorpool)
      have hphy : st'.phyregs = st.phyregs := by rw [heq]
      have hmax : st'.colormax = st.colormax := by rw [heq]
      exact finish st' col g' hphy hmax hnd (List.nodup_cons.mp g''.distinct).1 hcn
        (g''.minAll col (List.mem_append_left _ List.mem_cons_self))
  · simp only [linearRegAllocStepAux, hfl]
    obtain ⟨hm, hnd, _⟩ := findColorInListOutput forbidden col _ rest hfl
    have hpool : col ∈ st.colorpool := by simpa using (List.mem_filter.mp hm).2
    refine finish _ col (good_pool_sublist g List.filter_sublist) rfl rfl hnd ?_
      (g.pool col hpool) (g.minAll col (List.mem_append_left _ hpool))
    intro hin
    rcases List.mem_append.mp hin with h | h
    · simp at h
    · exact (List.nodup_append.mp g.distinct).2.2 col hpool col h rfl

/-- Exact HOL `st_ex_MAP_colors_sub` (`linear_scanProofScript.sml:3542-3548`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "st_ex_MAP_colors_sub"]
theorem stExMapColorsSub :
    ∀ (l : List Nat) (sth : LinearScanHiddenState),
      (∀ r, r ∈ l → r < sth.colors.length) →
      stExMap colorsSub l sth = (.success (l.map (fun r => holEl r sth.colors)), sth) := by
  intro l sth
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hb
      have hx := hb x List.mem_cons_self
      simp only [stExMap, Translator.Monadic.MonadBase.bind, colorsSubEqn, if_pos hx,
        ih (fun r hr => hb r (List.mem_cons_of_mem _ hr)), ret, List.map_cons]

end Flapjack.LinearScan
