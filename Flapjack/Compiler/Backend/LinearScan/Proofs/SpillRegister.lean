import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.GoodState

/-!
# linear_scanProof: sparse sublists and `spill_register`

Ports of `linear_scanProofScript.sml:2697-2946`: colour updates seen through a
filtered active list, the `IS_SPARSE_SUBLIST` order and its closure lemmas, and
preservation of `good_linear_scan_state` by `spill_register`. Renderings as in
`GoodState`; HOL `LUPDATE v n l` is `l.set n v` and `FILTER (\e,r. r <> reg)`
keeps the entries `x` with `x.2 ≠ reg`. HOL types are inhabited, so a
polymorphic list element read by `EL` carries `[Nonempty γ]`.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- `holEl` after `List.set`, without a bound on the updated index (an
out-of-range `set` is the identity). -/
private theorem holEl_set_any {γ : Type} [Nonempty γ] (l : List γ) (i j : Nat) (v : γ)
    (hij : i ≠ j) : holEl j (l.set i v) = holEl j l := by
  by_cases hi : i < l.length
  · rw [holEl_set l i j v hi, if_neg hij]
  · rw [List.set_eq_of_length_le (by omega)]

/-- Exact HOL `update_color_active_colors_same`
(`linear_scanProofScript.sml:2697-2706`); the HOL statement is polymorphic in
the unused `e : α`, the active entries' first component `β` and the colour
carrier `γ`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "update_color_active_colors_same"]
theorem updateColorActiveColorsSame {α β γ : Type} [Nonempty γ] :
    ∀ (_e : α) (reg : Nat) (active : List (β × Nat)) (regcol : γ) (colors : List γ),
      (active.filter (fun x => decide (x.2 ≠ reg))).map
          (fun x => holEl x.2 (colors.set reg regcol)) =
        (active.filter (fun x => decide (x.2 ≠ reg))).map (fun x => holEl x.2 colors) := by
  intro _ reg active regcol colors
  apply List.map_congr_left
  intro x hx
  have : x.2 ≠ reg := by simpa using (List.mem_filter.mp hx).2
  exact holEl_set_any colors reg x.2 regcol (Ne.symm this)

/-- Exact HOL `forced_update_stack_color_lemma`
(`linear_scanProofScript.sml:2708-2725`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forced_update_stack_color_lemma"]
theorem forcedUpdateStackColorLemma :
    ∀ (colors : List Nat) (stacknum : Nat) (l : List Nat) (r2 r1 : Nat),
      (∀ r, r ∈ l → holEl r colors < stacknum) ∧ r2 ∈ l ∧ r1 < colors.length ∧
      holEl r1 (colors.set r1 stacknum) = holEl r2 (colors.set r1 stacknum) → r1 = r2 := by
  intro colors stacknum l r2 r1 ⟨hl, hr2, hr1, heq⟩
  refine Classical.byContradiction fun hne => ?_
  rw [holEl_set colors r1 r1 stacknum hr1, if_pos rfl,
    holEl_set colors r1 r2 stacknum hr1, if_neg hne] at heq
  have := hl r2 hr2
  omega

/-- Exact HOL `IS_SPARSE_SUBLIST` (`linear_scanProofScript.sml:2727-2736`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "IS_SPARSE_SUBLIST_def"]
def isSparseSublist {α : Type} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => (x = y ∧ isSparseSublist xs ys) ∨ isSparseSublist (x :: xs) ys

/-- `IS_SPARSE_SUBLIST` is the core `List.Sublist` order. Flapjack
infrastructure for the closure lemmas below; not a HOL theorem. -/
theorem isSparseSublist_iff {α : Type} :
    ∀ (l1 l2 : List α), isSparseSublist l1 l2 ↔ l1.Sublist l2
  | [], _ => by simp [isSparseSublist]
  | _ :: _, [] => by simp [isSparseSublist]
  | x :: xs, y :: ys => by
      rw [isSparseSublist, isSparseSublist_iff xs ys, isSparseSublist_iff (x :: xs) ys,
        List.sublist_cons_iff]
      constructor
      · rintro (⟨rfl, h⟩ | h)
        · exact Or.inr ⟨xs, rfl, h⟩
        · exact Or.inl h
      · rintro (h | ⟨r, hr, h⟩)
        · exact Or.inr h
        · simp only [List.cons.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact Or.inl ⟨rfl, h⟩

/-- Exact HOL `FILTER_IS_SPARSE_SUBLIST` (`linear_scanProofScript.sml:2738-2745`);
`P` is free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "FILTER_IS_SPARSE_SUBLIST"]
theorem filterIsSparseSublist {α : Type} (P : α → Bool) :
    ∀ (l : List α), isSparseSublist (l.filter P) l := by
  intro l
  rw [isSparseSublist_iff]
  exact List.filter_sublist

/-- Exact HOL `MEM_SPARSE_SUBLIST` (`linear_scanProofScript.sml:2747-2755`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "MEM_SPARSE_SUBLIST"]
theorem memSparseSublist {α : Type} :
    ∀ (l1 l2 : List α) (x : α), isSparseSublist l1 l2 ∧ x ∈ l1 → x ∈ l2 := by
  intro l1 l2 x ⟨h, hx⟩
  exact ((isSparseSublist_iff l1 l2).mp h).subset hx

/-- Exact HOL `IS_SPARSE_SUBLIST_APPEND_LEFT` (`linear_scanProofScript.sml:2757-2762`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "IS_SPARSE_SUBLIST_APPEND_LEFT"]
theorem isSparseSublistAppendLeft {α : Type} :
    ∀ (l1 l2 l : List α), isSparseSublist l1 l2 → isSparseSublist (l ++ l1) (l ++ l2) := by
  intro l1 l2 l h
  rw [isSparseSublist_iff] at h ⊢
  exact h.append_left l

/-- Exact HOL `IS_SPARSE_SUBLIST_APPEND_RIGHT` (`linear_scanProofScript.sml:2764-2773`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "IS_SPARSE_SUBLIST_APPEND_RIGHT"]
theorem isSparseSublistAppendRight {α : Type} :
    ∀ (l1 l2 l : List α), isSparseSublist l1 l2 → isSparseSublist (l1 ++ l) (l2 ++ l) := by
  intro l1 l2 l h
  rw [isSparseSublist_iff] at h ⊢
  exact h.append_right l

/-- Exact HOL `MAP_IS_SPARSE_SUBLIST` (`linear_scanProofScript.sml:2775-2782`);
`f` is free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "MAP_IS_SPARSE_SUBLIST"]
theorem mapIsSparseSublist {α β : Type} (f : α → β) :
    ∀ (l1 l2 : List α), isSparseSublist l1 l2 → isSparseSublist (l1.map f) (l2.map f) := by
  intro l1 l2 h
  rw [isSparseSublist_iff] at h ⊢
  exact h.map f

/-- Exact HOL `ALL_DISTINCT_IS_SPARSE_SUBLIST` (`linear_scanProofScript.sml:2784-2801`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "ALL_DISTINCT_IS_SPARSE_SUBLIST"]
theorem allDistinctIsSparseSublist {α : Type} :
    ∀ (l1 l2 : List α), l2.Nodup ∧ isSparseSublist l1 l2 → l1.Nodup := by
  intro l1 l2 ⟨hd, h⟩
  exact hd.sublist ((isSparseSublist_iff l1 l2).mp h)

/-- A sorted list stays sorted under `FILTER` for a transitive order. -/
theorem holSorted_filter {α : Type} (R : α → α → Prop) (hR : holTransitive R)
    (p : α → Bool) : ∀ (l : List α), holSorted R l → holSorted R (l.filter p)
  | [], _ => trivial
  | h :: t, hs => by
      have ⟨hst, hall⟩ := (holSortedEq R t h hR).mp hs
      rw [List.filter_cons]
      split
      · exact (holSortedEq R _ h hR).mpr
          ⟨holSorted_filter R hR p t hst, fun y hy => hall y (List.mem_filter.mp hy).1⟩
      · exact holSorted_filter R hR p t hst

/-- Exact HOL `spill_register_FILTER_invariants_hidden`
(`linear_scanProofScript.sml:2803-2912`), including HOL's `id` wrapper. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "spill_register_FILTER_invariants_hidden"]
theorem spillRegisterFilterInvariantsHidden :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (reg mincol : Nat),
      id (¬ isPhyVar reg ∨ reg ∉ l) ∧ goodLinearScanState st sth l pos forced mincol ∧
      reg < sth.colors.length ∧ holEl reg sth.int_beg ≤ pos →
      ∃ stout sthout, (.success stout, sthout) =
          spillRegister { st with active := st.active.filter (fun x => decide (x.2 ≠ reg)) }
            reg sth ∧
        goodLinearScanState stout sthout (reg :: l) pos forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        (∀ r, r ≠ reg → holEl r sth.colors = holEl r sthout.colors) ∧
        stout.colormax = st.colormax ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        st.colormax ≤ holEl reg sthout.colors := by
  intro st sth l pos forced reg mincol ⟨hphy, hg, hreg, hbeg⟩
  have g := goodLinearScanState_iff.mp hg
  let c' := sth.colors.set reg st.stacknum
  have hcreg : holEl reg c' = st.stacknum := by
    simp only [c']; rw [holEl_set _ _ _ _ hreg, if_pos rfl]
  have hcne : ∀ r, r ≠ reg → holEl r c' = holEl r sth.colors := fun r h =>
    holEl_set_any sth.colors reg r _ (Ne.symm h)
  have hcl : ∀ r, r ∈ reg :: l → r ≠ reg →
      r ∈ l ∧ holEl r c' = holEl r sth.colors ∧ holEl r sth.colors < st.stacknum := by
    intro r hr hne
    have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left hne
    exact ⟨hrl, hcne r hne, g.stack r hrl⟩
  -- one register at the fresh stack colour is never coloured like another
  have hinj : ∀ r1 r2, r1 ∈ reg :: l → r2 ∈ reg :: l → holEl r1 c' = holEl r2 c' →
      (r1 = reg ∨ r2 = reg) → r1 = r2 := by
    intro r1 r2 h1 h2 heq hor
    by_cases e1 : r1 = reg
    · by_cases e2 : r2 = reg
      · rw [e1, e2]
      · obtain ⟨_, hc2, hlt⟩ := hcl r2 h2 e2
        rw [e1, hcreg, hc2] at heq; omega
    · have e2 : r2 = reg := hor.resolve_left e1
      obtain ⟨_, hc1, hlt⟩ := hcl r1 h1 e1
      rw [e2, hcreg, hc1] at heq; omega
  have hfmem : ∀ x, x ∈ st.active.filter (fun x => decide (x.2 ≠ reg)) →
      x ∈ st.active ∧ x.2 ≠ reg := by
    intro x hx
    have := List.mem_filter.mp hx
    exact ⟨this.1, by simpa using this.2⟩
  refine ⟨{ { st with active := st.active.filter (fun x => decide (x.2 ≠ reg)) } with
      stacknum := st.stacknum + 1 }, { sth with colors := c' }, ?run,
    goodLinearScanState_iff.mpr ?good, List.length_set,
    fun r h => (hcne r h).symm, rfl, rfl, rfl, by rw [hcreg]; exact g.maxStack⟩
  case run =>
    simp only [spillRegister, ignoreBind, updateColorsEqn, if_pos hreg, ret]; rfl
  case good =>
  exact {
    lenBeg := by rw [List.length_set]; exact g.lenBeg
    lenEnd := by rw [List.length_set]; exact g.lenEnd
    distinct := by
      show (st.colorpool ++ (st.active.filter (fun x => decide (x.2 ≠ reg))).map
        (fun x => holEl x.2 c')).Nodup
      rw [updateColorActiveColorsSame () reg st.active st.stacknum sth.colors]
      exact g.distinct.sublist (((List.filter_sublist).map _).append_left _)
    bound := fun r hr => by
      rw [List.length_set]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hreg
      · exact g.bound r hr
    stack := fun r hr => by
      show holEl r c' < st.stacknum + 1
      by_cases e : r = reg
      · rw [e, hcreg]; omega
      · have := (hcl r hr e).2; rw [this.1]; omega
    phy := by
      show sptDomain st.phyregs = fun c => ∃ r, c = holEl r c' ∧
        (r ∈ reg :: l ∧ isPhyVar r ∧ holEl r c' < st.colormax)
      rw [g.phy]
      funext c
      apply propext
      constructor
      · rintro ⟨r, hc, hrl, hp, hlt⟩
        have hne : r ≠ reg := by
          rintro rfl
          rcases hphy with h | h
          · exact h hp
          · exact h hrl
        exact ⟨r, by rw [hcne r hne]; exact hc, List.mem_cons_of_mem _ hrl, hp,
          by rw [hcne r hne]; exact hlt⟩
      · rintro ⟨r, hc, hrl, hp, hlt⟩
        by_cases e : r = reg
        · rw [e, hcreg] at hlt; have := g.maxStack; omega
        · obtain ⟨hrl', hc', _⟩ := hcl r hrl e
          exact ⟨r, by rw [← hc']; exact hc, hrl', hp, by rw [← hc']; exact hlt⟩
    phyDistinct := by
      show (((reg :: l).filter isPhyVar).map (fun r => holEl r c')).Nodup
      have hmap : ∀ m : List Nat, (∀ r, r ∈ m → r ≠ reg) →
          m.map (fun r => holEl r c') = m.map (fun r => holEl r sth.colors) :=
        fun m hm => List.map_congr_left (fun r hr => hcne r (hm r hr))
      rw [List.filter_cons]
      split
      · next hp =>
        have hnl : reg ∉ l := by
          rcases hphy with h | h
          · exact absurd hp h
          · exact h
        have hne : ∀ r, r ∈ l.filter isPhyVar → r ≠ reg := by
          intro r hr e; subst e; exact hnl (List.mem_filter.mp hr).1
        rw [List.map_cons, hmap _ hne, hcreg]
        refine List.nodup_cons.mpr ⟨fun hm => ?_, g.phyDistinct⟩
        obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
        have := g.stack r (List.mem_filter.mp hr).1
        omega
      · next hp =>
        have hne : ∀ r, r ∈ l.filter isPhyVar → r ≠ reg := by
          intro r hr e; subst e; exact hp (List.mem_filter.mp hr).2
        rw [hmap _ hne]
        exact g.phyDistinct
    pool := g.pool
    active := fun x hx => by
      obtain ⟨hx, hne⟩ := hfmem x hx
      show holEl x.2 c' < st.colornum
      rw [hcne _ hne]; exact g.active x hx
    numMax := g.numMax
    maxStack := by show st.colormax ≤ st.stacknum + 1; have := g.maxStack; omega
    colMax := fun r hr h => by
      show holEl r c' < st.colornum
      by_cases e : r = reg
      · have h' : holEl r c' < st.colormax := h
        rw [e, hcreg] at h'; have := g.maxStack; omega
      · obtain ⟨hrl, hc', _⟩ := hcl r hr e
        have h' : holEl r c' < st.colormax := h
        rw [hc'] at h' ⊢; exact g.colMax r hrl h'
    beg := fun r hr => by
      by_cases e : r = reg
      · rw [e]; exact hbeg
      · exact g.beg r (hcl r hr e).1
    live := fun r hr ⟨h1, h2⟩ => by
      have h2' : holEl r c' < st.colormax := h2
      by_cases e : r = reg
      · rw [e, hcreg] at h2'; have := g.maxStack; omega
      · obtain ⟨hrl, hc', _⟩ := hcl r hr e
        rw [hc'] at h2'
        exact List.mem_filter.mpr ⟨g.live r hrl ⟨h1, h2'⟩, by simpa using e⟩
    ends := fun r hr hm => by
      obtain ⟨hm, hne⟩ := hfmem _ hm
      exact g.ends r (hcl r hr hne).1 hm
    inter := fun r1 r2 ⟨h1, h2, hi, heq⟩ => by
      by_cases e : r1 = reg ∨ r2 = reg
      · exact hinj r1 r2 h1 h2 heq e
      · have e1 : r1 ≠ reg := fun h => e (Or.inl h)
        have e2 : r2 ≠ reg := fun h => e (Or.inr h)
        obtain ⟨hl1, hc1, _⟩ := hcl r1 h1 e1
        obtain ⟨hl2, hc2, _⟩ := hcl r2 h2 e2
        have heq' : holEl r1 c' = holEl r2 c' := heq
        rw [hc1, hc2] at heq'
        exact g.inter r1 r2 ⟨hl1, hl2, hi, heq'⟩
    sorted := holSorted_filter _ transitiveLessFst _ _ g.sorted
    activeEnd := fun x hx => g.activeEnd x (hfmem x hx).1
    activeMem := fun x hx => List.mem_cons_of_mem _ (g.activeMem x (hfmem x hx).1)
    forcedOk := fun x hx ⟨h1, h2, heq⟩ => by
      by_cases e : x.1 = reg ∨ x.2 = reg
      · exact hinj _ _ h1 h2 heq e
      · have e1 : x.1 ≠ reg := fun h => e (Or.inl h)
        have e2 : x.2 ≠ reg := fun h => e (Or.inr h)
        obtain ⟨hl1, hc1, _⟩ := hcl _ h1 e1
        obtain ⟨hl2, hc2, _⟩ := hcl _ h2 e2
        have heq' : holEl x.1 c' = holEl x.2 c' := heq
        rw [hc1, hc2] at heq'
        exact g.forcedOk x hx ⟨hl1, hl2, heq'⟩
    minNum := g.minNum
    minAll := fun c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact g.minAll c (List.mem_append_left _ hc)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
        show mincol ≤ holEl r c'
        by_cases e : r = reg
        · rw [e, hcreg]
          have := g.minNum; have := g.numMax; have := g.maxStack; omega
        · obtain ⟨hrl, hc', _⟩ := hcl r hr e
          rw [hc']
          exact g.minAll _ (List.mem_append_right _ (List.mem_map_of_mem hrl)) }

/-- Exact HOL `spill_register_FILTER_invariants`
(`linear_scanProofScript.sml:2914-2916`): the hidden form with `id` removed. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "spill_register_FILTER_invariants"]
theorem spillRegisterFilterInvariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (reg mincol : Nat),
      (¬ isPhyVar reg ∨ reg ∉ l) ∧ goodLinearScanState st sth l pos forced mincol ∧
      reg < sth.colors.length ∧ holEl reg sth.int_beg ≤ pos →
      ∃ stout sthout, (.success stout, sthout) =
          spillRegister { st with active := st.active.filter (fun x => decide (x.2 ≠ reg)) }
            reg sth ∧
        goodLinearScanState stout sthout (reg :: l) pos forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        (∀ r, r ≠ reg → holEl r sth.colors = holEl r sthout.colors) ∧
        stout.colormax = st.colormax ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        st.colormax ≤ holEl reg sthout.colors :=
  spillRegisterFilterInvariantsHidden

/-- Exact HOL `FILTER_MEM_active` (`linear_scanProofScript.sml:2918-2924`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "FILTER_MEM_active"]
theorem filterMemActive :
    ∀ (reg : Nat) (l : List (Int × Nat)), (∀ e : Int, (e, reg) ∉ l) →
      l.filter (fun x => decide (x.2 ≠ reg)) = l := by
  intro reg l h
  rw [List.filter_eq_self]
  intro x hx
  have : x.2 ≠ reg := by
    intro e
    exact h x.1 (by rw [← e]; exact hx)
  simpa using this

/-- Exact HOL `spill_register_invariants` (`linear_scanProofScript.sml:2926-2945`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "spill_register_invariants"]
theorem spillRegisterInvariants :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (reg mincol : Nat),
      (∀ e : Int, (e, reg) ∉ st.active) ∧ (¬ isPhyVar reg ∨ reg ∉ l) ∧
      goodLinearScanState st sth l pos forced mincol ∧
      reg < sth.colors.length ∧ holEl reg sth.int_beg ≤ pos →
      ∃ stout sthout, (.success stout, sthout) = spillRegister st reg sth ∧
        goodLinearScanState stout sthout (reg :: l) pos forced mincol ∧
        sthout.colors.length = sth.colors.length ∧
        sthout.int_beg = sth.int_beg ∧ sthout.int_end = sth.int_end ∧
        (∀ r, r ≠ reg → holEl r sth.colors = holEl r sthout.colors) ∧
        stout.colormax = st.colormax ∧
        st.colormax ≤ holEl reg sthout.colors := by
  intro st sth l pos forced reg mincol ⟨hnm, hphy, hg, hreg, hbeg⟩
  obtain ⟨stout, sthout, hrun, hgood, hlen, hcol, hmax, hb, he, hle⟩ :=
    spillRegisterFilterInvariantsHidden st sth l pos forced reg mincol ⟨hphy, hg, hreg, hbeg⟩
  have hst : { st with active := st.active.filter (fun x => decide (x.2 ≠ reg)) } = st := by
    rw [filterMemActive reg st.active hnm]
  rw [hst] at hrun
  exact ⟨stout, sthout, hrun, hgood, hlen, hb, he, hcol, hmax, hle⟩

end Flapjack.LinearScan
