import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.SortCorrect
import Flapjack.Compiler.Backend.LinearScan.TopLevel
import Flapjack.Misc.Sptree.Map

/-!
# linear_scanProof: `linear_reg_alloc_intervals_correct`

Ports of `linear_scanProofScript.sml:4332-4996`: the initial states of the two
allocation passes, the array/list conversions of the sorted registers and
moves, the bookkeeping lemmas about filters and reversal, and the correctness
of the interval allocator `linear_reg_alloc_intervals`. Renderings as in
`GoodState` and `SortCorrect`; HOL `DROP` is `List.drop`, `fromAList`
`sptFromAList`, and a HOL `FILTER` predicate is the corresponding Boolean
test (`MEM` decided classically where its element type has no decidable
equality).
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `list_minimum` (`linear_scanProofScript.sml:4332-4348`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "list_minimum"]
theorem listMinimum : ∀ (f : Nat → Int) (l : List Nat), ∃ x, ∀ y, y ∈ l → x ≤ f y := by
  intro f l
  induction l with
  | nil => exact ⟨0, fun _ h => by cases h⟩
  | cons h t ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨min x (f h), fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Int.min_le_right _ _
      · exact Int.le_trans (Int.min_le_left _ _) (hx y hy)

/-- The empty allocation state satisfies `good_linear_scan_state`. -/
private theorem good_initial (st : LinearScanState) (sth : LinearScanHiddenState) (pos : Int)
    (forced : List (Nat × Nat)) (mincol : Nat)
    (hlb : sth.int_beg.length = sth.colors.length) (hle : sth.int_end.length = sth.colors.length)
    (hact : st.active = []) (hpool : st.colorpool = []) (hphy : st.phyregs = .ln)
    (h1 : st.colornum ≤ st.colormax) (h2 : st.colormax ≤ st.stacknum)
    (h3 : mincol ≤ st.colornum) :
    goodLinearScanState st sth [] pos forced mincol := by
  refine goodLinearScanState_iff.mpr
    { lenBeg := hlb, lenEnd := hle
      distinct := by simp [hact, hpool]
      bound := fun _ h => absurd h List.not_mem_nil
      stack := fun _ h => absurd h List.not_mem_nil
      phy := ?_
      phyDistinct := by simp
      pool := fun _ h => absurd (hpool ▸ h) List.not_mem_nil
      active := fun _ h => absurd (hact ▸ h) List.not_mem_nil
      numMax := h1, maxStack := h2
      colMax := fun _ h => absurd h List.not_mem_nil
      beg := fun _ h => absurd h List.not_mem_nil
      live := fun _ h => absurd h List.not_mem_nil
      ends := fun _ h => absurd h List.not_mem_nil
      inter := fun _ _ h => absurd h.1 List.not_mem_nil
      sorted := by rw [hact]; trivial
      activeEnd := fun _ h => absurd (hact ▸ h) List.not_mem_nil
      activeMem := fun _ h => absurd (hact ▸ h) List.not_mem_nil
      forcedOk := fun _ _ h => absurd h.1 List.not_mem_nil
      minNum := h3
      minAll := fun _ h => by simp [hpool] at h }
  rw [hphy]
  funext c
  apply propext
  constructor
  · intro h; simp [sptDomain] at h
  · rintro ⟨_, _, h, _⟩; cases h

/-- Exact HOL `linear_reg_alloc_pass1_initial_state_invariants`
(`linear_scanProofScript.sml:4350-4363`); the unused `st` keeps its polymorphic
HOL type. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_pass1_initial_state_invariants"]
theorem linearRegAllocPass1InitialStateInvariants {α : Type} :
    ∀ (sth : LinearScanHiddenState) (reglist : List Nat) (forced : List (Nat × Nat)) (k : Nat)
      (_st : α),
      sth.int_beg.length = sth.colors.length ∧ sth.int_end.length = sth.colors.length →
      ∃ pos, goodLinearScanState (linearRegAllocPass1InitialState k) sth [] pos forced 0 ∧
        ∀ r, r ∈ reglist → pos ≤ holEl r sth.int_beg := by
  intro sth reglist forced k _ ⟨hlb, hle⟩
  obtain ⟨pos, hpos⟩ := listMinimum (fun r => holEl r sth.int_beg) reglist
  exact ⟨pos, good_initial _ sth pos forced 0 hlb hle rfl rfl rfl (Nat.zero_le _)
    (Nat.le_refl _) (Nat.le_refl _), hpos⟩

/-- Exact HOL `linear_reg_alloc_pass2_initial_state_invariants`
(`linear_scanProofScript.sml:4365-4378`); the unused `st` keeps its polymorphic
HOL type. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_pass2_initial_state_invariants"]
theorem linearRegAllocPass2InitialStateInvariants {α : Type} :
    ∀ (sth : LinearScanHiddenState) (reglist : List Nat) (forced : List (Nat × Nat))
      (k nreg : Nat) (_st : α),
      sth.int_beg.length = sth.colors.length ∧ sth.int_end.length = sth.colors.length →
      ∃ pos, goodLinearScanState (linearRegAllocPass2InitialState k nreg) sth [] pos forced k ∧
        ∀ r, r ∈ reglist → pos ≤ holEl r sth.int_beg := by
  intro sth reglist forced k nreg _ ⟨hlb, hle⟩
  obtain ⟨pos, hpos⟩ := listMinimum (fun r => holEl r sth.int_beg) reglist
  exact ⟨pos, good_initial _ sth pos forced k hlb hle rfl rfl rfl (Nat.le_add_right _ _)
    (Nat.le_refl _) (Nat.le_refl _), hpos⟩

/-- Exact HOL `st_ex_FILTER_good_stack` (`linear_scanProofScript.sml:4380-4394`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "st_ex_FILTER_good_stack"]
theorem stExFilterGoodStack :
    ∀ (reglist : List Nat) (sth : LinearScanHiddenState) (k : Nat),
      (∀ r, r ∈ reglist → r < sth.colors.length) →
      stExFilterGood (fun r =>
          bind (colorsSub r) fun col => ret (decide (isStackVar r = true ∨ k ≤ col)))
        reglist sth =
        (.success (reglist.filter
          (fun r => decide (isStackVar r = true ∨ k ≤ holEl r sth.colors))), sth) := by
  intro reglist sth k
  induction reglist with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hb
      have hx := hb x List.mem_cons_self
      have ih' := ih (fun r hr => hb r (List.mem_cons_of_mem _ hr))
      simp only [stExFilterGood, Translator.Monadic.MonadBase.bind, colorsSubEqn, if_pos hx, ret,
        List.filter_cons]
      split
      · simp only [Translator.Monadic.MonadBase.bind, ih', ret]
      · exact ih'

/-- Exact HOL `lookup_fromAList_MAP_not_NONE` (`linear_scanProofScript.sml:4396-4406`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "lookup_fromAList_MAP_not_NONE"]
theorem lookupFromAListMapNotNone :
    ∀ (r : Nat) (l : List Nat),
      sptLookup r (sptFromAList (l.map (fun r => (r, ())))) ≠ none ↔ r ∈ l := by
  intro r l
  have h := congrFun (sptDomainFromAList (l.map (fun r => (r, ())))) r
  simp only [sptDomain, List.map_map] at h
  rw [Option.ne_none_iff_isSome, h]
  simp

/-- Exact HOL `PERM_PARTITION` (`linear_scanProofScript.sml:4408-4416`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "PERM_PARTITION"]
theorem permPartition {α : Type} :
    ∀ (P : α → Bool) (l : List α),
      holPerm l (l.filter (fun x => P x) ++ l.filter (fun x => decide (¬ P x = true))) := by
  intro P l
  rw [holPerm_iff]
  have : (fun x => decide (¬ P x = true)) = (fun x => !P x) := by
    funext x; cases P x <;> rfl
  rw [this]
  exact (List.filter_append_perm P l).symm

/-- Exact HOL `forbidden_is_from_forced_take_sublist`
(`linear_scanProofScript.sml:4418-4425`); `l`, `forced`, `int_beg` and
`forced_adj` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "forbidden_is_from_forced_take_sublist"]
theorem forbiddenIsFromForcedTakeSublist (l : List Nat) (forced : List (Nat × Nat))
    (int_beg : List Int) (forced_adj : Spt (List Nat)) :
    (∀ x, x ∈ forced → x.1 ∈ l ∧ x.2 ∈ l) ∧
    (∀ r, forbiddenIsFromForced forced int_beg r (miscThe [] (sptLookup r forced_adj))) →
    ∀ r, forbiddenIsFromForcedSublist l forced int_beg r (miscThe [] (sptLookup r forced_adj)) := by
  intro ⟨hfp, hff⟩ r reg2
  rw [← hff r reg2]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rcases h.2.1 with hp | hp
    · exact (hfp _ hp).2
    · exact (hfp _ hp).1
  · exact fun h => h.1

/-- Exact HOL `good_linear_scan_state_REVERSE` (`linear_scanProofScript.sml:4427-4435`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "good_linear_scan_state_REVERSE"]
theorem goodLinearScanStateReverse :
    ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat) (pos : Int)
      (forced : List (Nat × Nat)) (mincol : Nat),
      goodLinearScanState st sth l.reverse pos forced mincol ↔
        goodLinearScanState st sth l pos forced mincol := by
  -- the invariant only depends on membership in `l`, except the distinctness of
  -- the physical colours, which reversal preserves
  have key : ∀ (st : LinearScanState) (sth : LinearScanHiddenState) (l l' : List Nat)
      (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat),
      (∀ r, r ∈ l ↔ r ∈ l') →
      (((l.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup ↔
        ((l'.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup) →
      goodLinearScanState st sth l pos forced mincol →
      goodLinearScanState st sth l' pos forced mincol := by
    intro st sth l l' pos forced mincol hm hnd hg
    have g := goodLinearScanState_iff.mp hg
    exact goodLinearScanState_iff.mpr {
      lenBeg := g.lenBeg, lenEnd := g.lenEnd, distinct := g.distinct,
      bound := fun r hr => g.bound r ((hm r).mpr hr),
      stack := fun r hr => g.stack r ((hm r).mpr hr),
      phy := by
        rw [g.phy]; funext c; apply propext
        exact ⟨fun ⟨r, h1, h2, h3⟩ => ⟨r, h1, (hm r).mp h2, h3⟩,
          fun ⟨r, h1, h2, h3⟩ => ⟨r, h1, (hm r).mpr h2, h3⟩⟩
      phyDistinct := hnd.mp g.phyDistinct,
      pool := g.pool, active := g.active, numMax := g.numMax, maxStack := g.maxStack,
      colMax := fun r hr => g.colMax r ((hm r).mpr hr),
      beg := fun r hr => g.beg r ((hm r).mpr hr),
      live := fun r hr => g.live r ((hm r).mpr hr),
      ends := fun r hr => g.ends r ((hm r).mpr hr),
      inter := fun r1 r2 ⟨h1, h2, h⟩ => g.inter r1 r2 ⟨(hm r1).mpr h1, (hm r2).mpr h2, h⟩,
      sorted := g.sorted, activeEnd := g.activeEnd,
      activeMem := fun x hx => (hm _).mp (g.activeMem x hx),
      forcedOk := fun x hx ⟨h1, h2, h⟩ => g.forcedOk x hx ⟨(hm _).mpr h1, (hm _).mpr h2, h⟩,
      minNum := g.minNum,
      minAll := fun c hc => by
        apply g.minAll c
        rcases List.mem_append.mp hc with hc | hc
        · exact List.mem_append_left _ hc
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
          exact List.mem_append_right _ (List.mem_map_of_mem ((hm r).mpr hr)) }
  intro st sth l pos forced mincol
  have hnd : ((l.reverse.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup ↔
      ((l.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup := by
    rw [List.filter_reverse, List.map_reverse]
    exact (List.reverse_perm _).nodup_iff
  exact ⟨key st sth l.reverse l pos forced mincol (fun r => List.mem_reverse) hnd,
    key st sth l l.reverse pos forced mincol (fun r => List.mem_reverse.symm) hnd.symm⟩

/-- Exact HOL `phystack_on_stack_REVERSE` (`linear_scanProofScript.sml:4437-4441`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "phystack_on_stack_REVERSE"]
theorem phystackOnStackReverse :
    ∀ (l : List Nat) (st : LinearScanState) (sth : LinearScanHiddenState),
      phystackOnStack l.reverse st sth ↔ phystackOnStack l st sth := by
  intro l st sth
  simp only [phystackOnStack, List.mem_reverse]

open Classical in
/-- Exact HOL `FILTER_remove_MEM_l` (`linear_scanProofScript.sml:4443-4450`);
`MEM x l` is decided classically. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "FILTER_remove_MEM_l"]
theorem filterRemoveMemL {α : Type} :
    ∀ (P : α → Bool) (l : List α),
      l.filter (fun x => decide (P x = true ∧ x ∈ l)) = l.filter (fun x => P x) := by
  intro P l
  apply List.filter_congr
  intro x hx
  simp [hx]

/-- Exact HOL `le_div_2` (`linear_scanProofScript.sml:4452-4456`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "le_div_2"]
theorem leDiv2 : ∀ (k r : Nat), k ≤ r / 2 ↔ 2 * k ≤ r := by
  intro k r; omega

/-- Exact HOL `lt_div_2` (`linear_scanProofScript.sml:4458-4462`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "lt_div_2"]
theorem ltDiv2 : ∀ (k r : Nat), r / 2 < k ↔ r < 2 * k := by
  intro k r; omega

/-- Exact HOL `list_to_sorted_regs_correct` (`linear_scanProofScript.sml:4464-4500`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "list_to_sorted_regs_correct"]
theorem listToSortedRegsCorrect :
    ∀ (l : List Nat) (n : Nat) (sth : LinearScanHiddenState),
      n + l.length ≤ sth.sorted_regs.length →
      ∃ sthout, (.success (), sthout) = listToSortedRegs l n sth ∧
        sthout.sorted_regs.length = sth.sorted_regs.length ∧
        sthout = { sth with sorted_regs := sthout.sorted_regs } ∧
        sthout.sorted_regs.take n = sth.sorted_regs.take n ∧
        (sthout.sorted_regs.drop n).take l.length = l := by
  intro l
  induction l with
  | nil => intro n sth _; exact ⟨sth, rfl, rfl, rfl, rfl, by simp⟩
  | cons x xs ih =>
      intro n sth hb
      have hn : n < sth.sorted_regs.length := by simp at hb; omega
      let s1 : LinearScanHiddenState := { sth with sorted_regs := sth.sorted_regs.set n x }
      obtain ⟨sthout, hrun, hlen, hst, htake, hdrop⟩ :=
        ih (n + 1) s1 (by simp [s1]; simp at hb; omega)
      have hs1 : s1.sorted_regs.length = sth.sorted_regs.length := by simp [s1]
      refine ⟨sthout, ?_, by rw [hlen, hs1], by rw [hst], ?_, ?_⟩
      · simp only [listToSortedRegs, ignoreBind, updateSortedRegsEqn, if_pos hn]
        exact hrun
      · have := congrArg (List.take n) htake
        rw [List.take_take, List.take_take, Nat.min_eq_left (by omega)] at this
        rw [this]
        simp [s1, List.take_set_of_le]
      · have hcell : holEl n sthout.sorted_regs = x := by
          have h1 : holEl n (sthout.sorted_regs.take (n + 1)) =
              holEl n (s1.sorted_regs.take (n + 1)) := by rw [htake]
          rw [holEl_take _ _ _ (by omega), holEl_take _ _ _ (by omega)] at h1
          rw [h1]
          show holEl n (sth.sorted_regs.set n x) = x
          rw [holEl_set _ _ _ _ hn, if_pos rfl]
        have hlen' : n < sthout.sorted_regs.length := by rw [hlen, hs1]; exact hn
        rw [List.drop_eq_getElem_cons hlen', List.length_cons, List.take_succ_cons]
        rw [← holEl_eq_getElem _ _ hlen', hcell]
        congr 1


/-- Exact HOL `sorted_regs_to_list_correct` (`linear_scanProofScript.sml:4502-4517`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "sorted_regs_to_list_correct"]
theorem sortedRegsToListCorrect :
    ∀ (n last : Nat) (sth : LinearScanHiddenState), last ≤ sth.sorted_regs.length →
      sortedRegsToList n last sth =
        (.success ((sth.sorted_regs.drop n).take (last - n)), sth) := by
  intro n last sth hl
  induction h : last - n using Nat.strongRecOn generalizing n with
  | ind k ih =>
  rw [sortedRegsToList]
  by_cases hln : last ≤ n
  · rw [dif_pos hln]
    have : k = 0 := by omega
    subst this
    simp [ret]
  · rw [dif_neg hln]
    have hn : n < sth.sorted_regs.length := by omega
    simp only [Translator.Monadic.MonadBase.bind, sortedRegsSubEqn, if_pos hn,
      ih (last - (n + 1)) (by omega) (n + 1) rfl, ret]
    rw [List.drop_eq_getElem_cons hn, show k = (last - (n + 1)) + 1 by omega,
      List.take_succ_cons, holEl_eq_getElem _ _ hn]

/-- Exact HOL `list_to_sorted_moves_correct` (`linear_scanProofScript.sml:4519-4555`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "list_to_sorted_moves_correct"]
theorem listToSortedMovesCorrect :
    ∀ (l : List (Nat × (Nat × Nat))) (n : Nat) (sth : LinearScanHiddenState),
      n + l.length ≤ sth.sorted_moves.length →
      ∃ sthout, (.success (), sthout) = listToSortedMoves l n sth ∧
        sthout.sorted_moves.length = sth.sorted_moves.length ∧
        sthout = { sth with sorted_moves := sthout.sorted_moves } ∧
        sthout.sorted_moves.take n = sth.sorted_moves.take n ∧
        (sthout.sorted_moves.drop n).take l.length = l := by
  intro l
  induction l with
  | nil => intro n sth _; exact ⟨sth, rfl, rfl, rfl, rfl, by simp⟩
  | cons x xs ih =>
      intro n sth hb
      have hn : n < sth.sorted_moves.length := by simp at hb; omega
      let s1 : LinearScanHiddenState := { sth with sorted_moves := sth.sorted_moves.set n x }
      obtain ⟨sthout, hrun, hlen, hst, htake, hdrop⟩ :=
        ih (n + 1) s1 (by simp [s1]; simp at hb; omega)
      have hs1 : s1.sorted_moves.length = sth.sorted_moves.length := by simp [s1]
      refine ⟨sthout, ?_, by rw [hlen, hs1], by rw [hst], ?_, ?_⟩
      · simp only [listToSortedMoves, ignoreBind, updateSortedMovesEqn, if_pos hn]
        exact hrun
      · have := congrArg (List.take n) htake
        rw [List.take_take, List.take_take, Nat.min_eq_left (by omega)] at this
        rw [this]
        simp [s1, List.take_set_of_le]
      · have hcell : holEl n sthout.sorted_moves = x := by
          have h1 : holEl n (sthout.sorted_moves.take (n + 1)) =
              holEl n (s1.sorted_moves.take (n + 1)) := by rw [htake]
          rw [holEl_take _ _ _ (by omega), holEl_take _ _ _ (by omega)] at h1
          rw [h1]
          show holEl n (sth.sorted_moves.set n x) = x
          rw [holEl_set _ _ _ _ hn, if_pos rfl]
        have hlen' : n < sthout.sorted_moves.length := by rw [hlen, hs1]; exact hn
        rw [List.drop_eq_getElem_cons hlen', List.length_cons, List.take_succ_cons]
        rw [← holEl_eq_getElem _ _ hlen', hcell]
        congr 1

/-- Exact HOL `sorted_moves_to_list_correct` (`linear_scanProofScript.sml:4557-4572`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "sorted_moves_to_list_correct"]
theorem sortedMovesToListCorrect :
    ∀ (n last : Nat) (sth : LinearScanHiddenState), last ≤ sth.sorted_moves.length →
      sortedMovesToList n last sth =
        (.success ((sth.sorted_moves.drop n).take (last - n)), sth) := by
  intro n last sth hl
  induction h : last - n using Nat.strongRecOn generalizing n with
  | ind k ih =>
  rw [sortedMovesToList]
  by_cases hln : last ≤ n
  · rw [dif_pos hln]
    have : k = 0 := by omega
    subst this
    simp [ret]
  · rw [dif_neg hln]
    have hn : n < sth.sorted_moves.length := by omega
    simp only [Translator.Monadic.MonadBase.bind, sortedMovesSubEqn, if_pos hn,
      ih (last - (n + 1)) (by omega) (n + 1) rfl, ret]
    rw [List.drop_eq_getElem_cons hn, show k = (last - (n + 1)) + 1 by omega,
      List.take_succ_cons, holEl_eq_getElem _ _ hn]

/-! ### `linear_reg_alloc_intervals_correct` -/

/-- A list whose cells are pairwise ordered is `SORTED`. -/
private theorem holSorted_of_pairwise {R : Nat → Nat → Prop} :
    ∀ (l : List Nat), (∀ i1 i2, i1 ≤ i2 → i2 < l.length → R (holEl i1 l) (holEl i2 l)) →
      holSorted R l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h => by
      refine ⟨h 0 1 (by omega) (by simp), holSorted_of_pairwise (b :: rest) ?_⟩
      intro i1 i2 h12 h2
      have := h (i1 + 1) (i2 + 1) (by omega) (by simp at h2 ⊢; omega)
      simpa only [holEl_cons_succ] using this

private theorem injOn_of_nodup_map {f : Nat → Nat} :
    ∀ (l : List Nat), (l.map f).Nodup → ∀ a, a ∈ l → ∀ b, b ∈ l → f a = f b → a = b
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | x :: xs, h => by
      rw [List.map_cons, List.nodup_cons] at h
      intro a ha b hb he
      rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
      · rw [ha', hb']
      · subst ha'; exact absurd (List.mem_map.mpr ⟨b, hb', he.symm⟩) h.1
      · subst hb'; exact absurd (List.mem_map.mpr ⟨a, ha', he⟩) h.1
      · exact injOn_of_nodup_map xs h.2 a ha' b hb' he

private theorem nodup_map_of_injOn {f : Nat → Nat} :
    ∀ (l : List Nat), l.Nodup → (∀ a, a ∈ l → ∀ b, b ∈ l → f a = f b → a = b) →
      (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hn, hi => by
      rw [List.nodup_cons] at hn
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_of_injOn xs hn.2
        (fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      exact hn.1 (hi y (List.mem_cons_of_mem _ hy) x List.mem_cons_self he ▸ hy)

/-- Looking up a filtered adjacency list. -/
private theorem miscThe_lookup_map_filter (p : Nat → Bool) (t : Spt (List Nat)) (r : Nat) :
    miscThe [] (sptLookup r (sptMap (List.filter p) t)) =
      (miscThe [] (sptLookup r t)).filter p := by
  rw [sptLookup_sptMap]
  cases sptLookup r t <;> rfl

private theorem stack_not_phy (r : Nat) (h : isStackVar r = true) : isPhyVar r = false := by
  simp only [isStackVar, isPhyVar, decide_eq_true_eq] at h ⊢
  exact decide_eq_false (by omega)

/-- Exact HOL `linear_reg_alloc_intervals_correct` (`linear_scanProofScript.sml:4574-4996`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "linear_reg_alloc_intervals_correct"]
theorem linearRegAllocIntervalsCorrect :
    ∀ (k : Nat) (forced : List (Nat × Nat)) (moves : List (Nat × (Nat × Nat)))
      (reglist_unsorted : List Nat) (sth : LinearScanHiddenState),
      (∀ x, x ∈ forced → x.1 ∈ reglist_unsorted ∧ x.2 ∈ reglist_unsorted) ∧
      (∀ x, x ∈ moves.map Prod.snd → x.1 < sth.colors.length ∧ x.2 < sth.colors.length) ∧
      (∀ r, r ∈ reglist_unsorted → r < sth.colors.length) ∧
      (∀ r, r ∈ reglist_unsorted → holEl r sth.int_beg ≤ holEl r sth.int_end) ∧
      reglist_unsorted.Nodup ∧
      (∀ r, r ∈ reglist_unsorted → r < sth.int_beg.length) ∧
      sth.colors.length = sth.int_beg.length ∧ sth.int_end.length = sth.int_beg.length ∧
      reglist_unsorted.length ≤ sth.sorted_regs.length ∧
      moves.length ≤ sth.sorted_moves.length →
      ∃ sthout, linearRegAllocIntervals k forced moves reglist_unsorted sth = (.success (), sthout) ∧
        (∀ r1 r2, r1 ∈ reglist_unsorted ∧ r2 ∈ reglist_unsorted ∧
          intervalIntersect (holEl r1 sth.int_beg, holEl r1 sth.int_end)
            (holEl r2 sth.int_beg, holEl r2 sth.int_end) ∧
          holEl r1 sthout.colors = holEl r2 sthout.colors → r1 = r2) ∧
        (∀ r, r ∈ reglist_unsorted →
          if isPhyVar r then holEl r sthout.colors = r / 2
          else if isStackVar r then k ≤ holEl r sthout.colors
          else True) ∧
        (∀ x, x ∈ forced → holEl x.1 sthout.colors = holEl x.2 sthout.colors → x.1 = x.2) ∧
        sthout.colors.length = sth.colors.length := by
  intro k forced moves ru sth
    ⟨hfru, hmvb, hrub, hrube, hrund, hrubb, hlcb, hleb, hlrs, hlms⟩
  -- the register array: write, sort, read back
  obtain ⟨s1, hrun1, hlen1, hrec1, _, htake1⟩ := listToSortedRegsCorrect ru 0 sth (by simpa)
  simp only [List.drop_zero] at htake1
  have hc1 : s1.colors = sth.colors := by have h := congrArg LinearScanHiddenState.colors hrec1; exact h
  have hb1 : s1.int_beg = sth.int_beg := by have h := congrArg LinearScanHiddenState.int_beg hrec1; exact h
  have he1 : s1.int_end = sth.int_end := by have h := congrArg LinearScanHiddenState.int_end hrec1; exact h
  have hm1 : s1.sorted_moves = sth.sorted_moves := by have h := congrArg LinearScanHiddenState.sorted_moves hrec1; exact h
  obtain ⟨s2, hrun2, hrec2, hlen2, hperm2, _, hsort2⟩ :=
    sortRegsCorrect 0 ru.length s1
      ⟨fun i ⟨_, hi⟩ => by
        rw [← holEl_take s1.sorted_regs ru.length i hi, htake1, hb1]
        exact hrubb _ (List.mem_iff_getElem.mpr ⟨i, hi, (holEl_eq_getElem _ _ hi).symm⟩ |>
          fun h => by rw [holEl_eq_getElem _ _ hi]; exact List.getElem_mem hi),
        Nat.zero_le _, by rw [hlen1]; exact hlrs⟩
  have hb2 : s2.int_beg = sth.int_beg := by have h := congrArg LinearScanHiddenState.int_beg hrec2; exact h.trans hb1
  have hc2 : s2.colors = sth.colors := by have h := congrArg LinearScanHiddenState.colors hrec2; exact h.trans hc1
  have he2 : s2.int_end = sth.int_end := by have h := congrArg LinearScanHiddenState.int_end hrec2; exact h.trans he1
  have hm2 : s2.sorted_moves = sth.sorted_moves := by
    have h := congrArg LinearScanHiddenState.sorted_moves hrec2; exact h.trans hm1
  let reglist := s2.sorted_regs.take ru.length
  have hlist : sortedRegsToList 0 ru.length s2 = (.success reglist, s2) := by
    rw [sortedRegsToListCorrect 0 ru.length s2 (by rw [hlen2, hlen1]; exact hlrs)]
    simp [reglist]
  have hpermr : ru.Perm reglist := by
    have := (holPerm_iff _ _).mp (hperm2 ru.length ⟨Nat.zero_le _, Nat.le_refl _,
      by rw [hlen1]; exact hlrs⟩)
    rwa [htake1] at this
  have hmemr : ∀ r, r ∈ reglist ↔ r ∈ ru := fun r => hpermr.mem_iff.symm
  have hsortr : holSorted (intbegLess sth.int_beg) reglist := by
    apply holSorted_of_pairwise
    intro i1 i2 h12 h2
    have hl : reglist.length = ru.length := hpermr.length_eq.symm
    rw [hl] at h2
    rw [holEl_take _ _ _ (by omega), holEl_take _ _ _ h2, ← hb1]
    exact hsort2 i1 i2 ⟨Nat.zero_le _, h12, h2⟩
  have hndr : reglist.Nodup := hpermr.nodup_iff.mp hrund
  -- the move array
  obtain ⟨s3, hrun3, hlen3, hrec3, _, htake3⟩ :=
    listToSortedMovesCorrect moves 0 s2 (by rw [hm2]; simpa)
  simp only [List.drop_zero] at htake3
  obtain ⟨s4, hrun4, hrec4, hlen4, hperm4⟩ :=
    sortMovesCorrect 0 moves.length s3 ⟨Nat.zero_le _, by rw [hlen3, hm2]; exact hlms⟩
  have hb4 : s4.int_beg = sth.int_beg := by
    have h4 := congrArg LinearScanHiddenState.int_beg hrec4
    have h3 := congrArg LinearScanHiddenState.int_beg hrec3
    exact h4.trans (h3.trans hb2)
  have hc4 : s4.colors = sth.colors := by
    have h4 := congrArg LinearScanHiddenState.colors hrec4
    have h3 := congrArg LinearScanHiddenState.colors hrec3
    exact h4.trans (h3.trans hc2)
  have he4 : s4.int_end = sth.int_end := by
    have h4 := congrArg LinearScanHiddenState.int_end hrec4
    have h3 := congrArg LinearScanHiddenState.int_end hrec3
    exact h4.trans (h3.trans he2)
  let smoves := s4.sorted_moves.take moves.length
  have hmlist : sortedMovesToList 0 moves.length s4 = (.success smoves, s4) := by
    rw [sortedMovesToListCorrect 0 moves.length s4 (by rw [hlen4, hlen3, hm2]; exact hlms)]
    simp [smoves]
  have hpermm : moves.Perm smoves := by
    have := (holPerm_iff _ _).mp (hperm4 moves.length ⟨Nat.zero_le _, Nat.le_refl _,
      by rw [hlen3, hm2]; exact hlms⟩)
    rwa [htake3] at this
  -- adjacency lists
  have hlbc : sth.int_beg.length = sth.colors.length := hlcb.symm
  obtain ⟨madj, hmadj, hmf⟩ := edgesToAdjlistOutput (smoves.map Prod.snd) s4 (by
    intro x hx
    have hx' : x ∈ moves.map Prod.snd := ((hpermm.map Prod.snd).mem_iff).mpr hx
    rw [hb4, hlbc]; exact hmvb x hx')
  obtain ⟨fadj, hfadj, hff⟩ := edgesToAdjlistOutput forced s4 (by
    intro x hx
    rw [hb4]
    exact ⟨hrubb _ (hfru x hx).1, hrubb _ (hfru x hx).2⟩)
  rw [hb4] at hmf hff
  have hfadjb : ∀ r1 r2, r2 ∈ miscThe [] (sptLookup r1 fadj) → r2 < s4.colors.length := by
    intro r1 r2 hr
    obtain ⟨_, hp, _⟩ := (hff r1 r2).mpr hr
    rw [hc4]
    rcases hp with hp | hp
    · exact hrub _ (hfru _ hp).1
    · exact hrub _ (hfru _ hp).2
  have hmadjb : ∀ r1 r2, r2 ∈ miscThe [] (sptLookup r1 madj) → r2 < s4.colors.length := by
    intro r1 r2 hr
    obtain ⟨_, hp, _⟩ := (hmf r1 r2).mpr hr
    rw [hc4]
    rcases hp with hp | hp
    · exact (hmvb _ (((hpermm.map Prod.snd).mem_iff).mpr hp)).1
    · exact (hmvb _ (((hpermm.map Prod.snd).mem_iff).mpr hp)).2
  -- pass 1
  obtain ⟨pos, hg0, hpos⟩ := linearRegAllocPass1InitialStateInvariants (α := Unit) s4 reglist
    forced k () ⟨by rw [hb4, hc4]; exact hlcb.symm, by rw [he4, hc4, hleb, hlcb]⟩
  obtain ⟨st1, sth1, pos1, hrunp1, hg1, hl1, hbb1, hee1, _, hps1, hmax1⟩ :=
    stExFoldlLinearRegAllocStepPassnInvariants reglist _ s4 pos true madj fadj forced 0
      ⟨by rw [hb4]; exact hsortr, hndr, hg0, hpos,
        fun r hr => by rw [hc4]; exact hrub r ((hmemr r).mp hr),
        fun r => by
          rw [hb4]
          exact forbiddenIsFromForcedTakeSublist reglist forced sth.int_beg fadj
            ⟨fun x hx => ⟨(hmemr _).mpr (hfru x hx).1, (hmemr _).mpr (hfru x hx).2⟩, hff⟩ r,
        fun x hx => ⟨(hmemr _).mpr (hfru x hx).1, (hmemr _).mpr (hfru x hx).2⟩,
        hfadjb, hmadjb,
        fun r hr => by rw [hb4, he4]; exact hrube r ((hmemr r).mp hr)⟩
  have g1 := goodLinearScanState_iff.mp hg1
  have hcl1 : sth1.colors.length = sth.colors.length := by rw [hl1, hc4]
  have hbeg1 : sth1.int_beg = sth.int_beg := by rw [hbb1, hb4]
  have hend1 : sth1.int_end = sth.int_end := by rw [hee1, he4]
  have hmx1 : st1.colormax = k := hmax1
  -- physical registers
  let phyregs := reglist.filter isPhyVar
  let phyphyregs := phyregs.filter (fun r => decide (r < 2 * k))
  let stackphyregs := phyregs.filter (fun r => decide (2 * k ≤ r))
  have hmemphy : ∀ r, r ∈ phyregs ↔ r ∈ reglist ∧ isPhyVar r = true := fun r => by
    simp [phyregs, List.mem_filter]
  have hndphy : phyregs.Nodup := hndr.filter _
  have hinj1 : ∀ a, a ∈ phyregs → ∀ b, b ∈ phyregs →
      holEl a sth1.colors = holEl b sth1.colors → a = b := by
    have h := g1.phyDistinct
    rw [List.filter_reverse, List.map_reverse] at h
    exact injOn_of_nodup_map _ ((List.reverse_perm _).nodup_iff.mp h)
  -- apply the first register exchange
  obtain ⟨sth2, hrune1, hl2, hbb2, hee2, hinj2, hval2, _, hge2, _⟩ :=
    applyRegExchangeCorrect phyphyregs sth1 k
      ⟨nodup_map_of_injOn _ (hndphy.filter _) (fun a ha b hb =>
          hinj1 a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1),
        fun r hr => ((hmemphy r).mp (List.mem_filter.mp hr).1).2,
        fun r hr => by
          rw [hcl1]; exact hrub r ((hmemr r).mp ((hmemphy r).mp (List.mem_filter.mp hr).1).1)⟩
  have hcl2 : sth2.colors.length = sth.colors.length := by rw [hl2, hcl1]
  have hbeg2 : sth2.int_beg = sth.int_beg := by rw [hbb2, hbeg1]
  have hend2 : sth2.int_end = sth.int_end := by rw [hee2, hend1]
  have hbr : ∀ r, r ∈ reglist → r < sth.colors.length := fun r hr => hrub r ((hmemr r).mp hr)
  -- the stack list
  let stacklist := reglist.filter
    (fun r => decide (isStackVar r = true ∨ k ≤ holEl r sth2.colors))
  have hfg := stExFilterGoodStack reglist sth2 k (fun r hr => by rw [hcl2]; exact hbr r hr)
  have hmemst : ∀ r, r ∈ stacklist ↔ r ∈ reglist ∧ (isStackVar r = true ∨ k ≤ holEl r sth2.colors) :=
    fun r => by simp [stacklist, List.mem_filter]
  let stackset := sptFromAList (stacklist.map (fun r => (r, ())))
  have hset : ∀ r, sptLookup r stackset ≠ none ↔ r ∈ stacklist :=
    fun r => lookupFromAListMapNotNone r stacklist
  let fadj' := sptMap (List.filter (fun r => decide (sptLookup r stackset ≠ none))) fadj
  let madj' := sptMap (List.filter (fun r => decide (sptLookup r stackset ≠ none))) madj
  let forced' := forced.filter (fun x => decide (x.1 ∈ stacklist ∧ x.2 ∈ stacklist))
  have hmemf' : ∀ x, x ∈ forced' ↔ x ∈ forced ∧ x.1 ∈ stacklist ∧ x.2 ∈ stacklist :=
    fun x => by simp [forced', List.mem_filter]
  -- pass 2
  obtain ⟨pos2, hg20, hpos2⟩ := linearRegAllocPass2InitialStateInvariants (α := Unit) sth2
    stacklist forced' k stacklist.length ()
    ⟨by rw [hbeg2, hcl2]; exact hlcb.symm, by rw [hend2, hcl2, hleb, hlcb]⟩
  have hthe : ∀ (t : Spt (List Nat)) r,
      miscThe [] (sptLookup r (sptMap (List.filter
        (fun r => decide (sptLookup r stackset ≠ none))) t)) =
      (miscThe [] (sptLookup r t)).filter (fun r => decide (sptLookup r stackset ≠ none)) :=
    fun t r => miscThe_lookup_map_filter _ t r
  obtain ⟨st3, sth3, pos3, hrunp2, hg3, hl3, hbb3, hee3, hc3, _, _⟩ :=
    stExFoldlLinearRegAllocStepPassnInvariants stacklist _ sth2 pos2 false madj' fadj' forced' k
      ⟨by rw [hbeg2]; exact holSorted_filter _ (intbegLessTransitive _) _ _ hsortr,
        hndr.filter _, hg20, hpos2,
        fun r hr => by rw [hcl2]; exact hbr r ((hmemst r).mp hr).1,
        fun r reg2 => by
          rw [hbeg2, hthe]
          have h := hff r reg2
          constructor
          · rintro ⟨hne, hp, hlex⟩
            have hp' : (reg2, r) ∈ forced ∨ (r, reg2) ∈ forced := by
              rcases hp with hp | hp
              · exact Or.inl ((hmemf' _).mp hp).1
              · exact Or.inr ((hmemf' _).mp hp).1
            have hin : reg2 ∈ stacklist ∧ r ∈ stacklist := by
              rcases hp with hp | hp
              · exact ⟨((hmemf' _).mp hp).2.1, ((hmemf' _).mp hp).2.2⟩
              · exact ⟨((hmemf' _).mp hp).2.2, ((hmemf' _).mp hp).2.1⟩
            exact ⟨List.mem_filter.mpr ⟨h.mp ⟨hne, hp', hlex⟩,
              decide_eq_true ((hset reg2).mpr hin.1)⟩, hin.2⟩
          · rintro ⟨hm, hr⟩
            obtain ⟨hm1, hm2⟩ := List.mem_filter.mp hm
            have hin2 : reg2 ∈ stacklist := (hset reg2).mp (of_decide_eq_true hm2)
            obtain ⟨hne, hp, hlex⟩ := h.mpr hm1
            refine ⟨hne, ?_, hlex⟩
            rcases hp with hp | hp
            · exact Or.inl ((hmemf' _).mpr ⟨hp, hin2, hr⟩)
            · exact Or.inr ((hmemf' _).mpr ⟨hp, hr, hin2⟩),
        fun x hx => ⟨((hmemf' x).mp hx).2.1, ((hmemf' x).mp hx).2.2⟩,
        fun r1 r2 hr => by
          rw [hthe] at hr
          rw [hcl2, ← hc4]; exact hfadjb r1 r2 (List.mem_filter.mp hr).1,
        fun r1 r2 hr => by
          rw [hthe] at hr
          rw [hcl2, ← hc4]; exact hmadjb r1 r2 (List.mem_filter.mp hr).1,
        fun r hr => by
          rw [hbeg2, hend2]; exact hrube r ((hmemr r).mp ((hmemst r).mp hr).1)⟩
  have g3 := goodLinearScanState_iff.mp hg3
  have hcl3 : sth3.colors.length = sth.colors.length := by rw [hl3, hcl2]
  have hbeg3 : sth3.int_beg = sth.int_beg := by rw [hbb3, hbeg2]
  have hend3 : sth3.int_end = sth.int_end := by rw [hee3, hend2]
  -- colour facts after pass 2
  have F1 : ∀ r, r ∈ stacklist → k ≤ holEl r sth3.colors := fun r hr =>
    g3.minAll _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_reverse.mpr hr)))
  have F2 : ∀ r, r ∈ reglist → r ∉ stacklist → holEl r sth3.colors < k := by
    intro r hr hn
    rw [hc3 r hn]
    have : ¬ (isStackVar r = true ∨ k ≤ holEl r sth2.colors) := fun h => hn ((hmemst r).mpr ⟨hr, h⟩)
    omega
  have hinj2' : ∀ a, a ∈ phyregs → ∀ b, b ∈ phyregs →
      holEl a sth2.colors = holEl b sth2.colors → a = b := by
    intro a ha b hb he
    have hab := hbr a ((hmemphy a).mp ha).1
    have hbb := hbr b ((hmemphy b).mp hb).1
    exact hinj1 a ha b hb (hinj2 a b ⟨by rw [hcl1]; exact hab, by rw [hcl1]; exact hbb⟩ he)
  have hinj3 : ∀ a, a ∈ phyregs → ∀ b, b ∈ phyregs →
      holEl a sth3.colors = holEl b sth3.colors → a = b := by
    intro a ha b hb he
    have har := ((hmemphy a).mp ha).1
    have hbr' := ((hmemphy b).mp hb).1
    by_cases ea : a ∈ stacklist <;> by_cases eb : b ∈ stacklist
    · have h := g3.phyDistinct
      rw [List.filter_reverse, List.map_reverse] at h
      exact injOn_of_nodup_map _ ((List.reverse_perm _).nodup_iff.mp h) a
        (List.mem_filter.mpr ⟨ea, ((hmemphy a).mp ha).2⟩) b
        (List.mem_filter.mpr ⟨eb, ((hmemphy b).mp hb).2⟩) he
    · have := F1 a ea; have := F2 b hbr' eb; omega
    · have := F2 a har ea; have := F1 b eb; omega
    · rw [hc3 a ea, hc3 b eb] at he
      exact hinj2' a ha b hb he
  -- the high physical registers were all put on the stack
  have F5 : ∀ r, r ∈ stackphyregs → k ≤ holEl r sth3.colors ∧ k ≤ r / 2 := by
    intro r hr
    obtain ⟨hrp, h2k⟩ := List.mem_filter.mp hr
    have h2k' : 2 * k ≤ r := of_decide_eq_true h2k
    refine ⟨F1 r ?_, by omega⟩
    obtain ⟨hrl, hphy⟩ := (hmemphy r).mp hrp
    have hk1 : k ≤ holEl r sth1.colors := by
      have := hps1 rfl r ⟨List.mem_reverse.mpr hrl, hphy, by rw [hmx1]; exact h2k'⟩
      rwa [hmx1] at this
    have hk2 : k ≤ holEl r sth2.colors :=
      hge2 (fun r' hr' => by
          have := of_decide_eq_true (List.mem_filter.mp hr').2; omega)
        r ⟨by rw [hcl1]; exact hbr r hrl, hk1, fun r' hr' he => by
          have hr'p := (List.mem_filter.mp hr').1
          have hlt := of_decide_eq_true (List.mem_filter.mp hr').2
          have := hinj1 r hrp r' hr'p he
          omega⟩
    exact (hmemst r).mpr ⟨hrl, Or.inr hk2⟩
  -- apply the second register exchange
  obtain ⟨sth4, hrune2, hl4, _, _, hinj4, hval4, hiff4, _, hfix4⟩ :=
    applyRegExchangeCorrect stackphyregs sth3 k
      ⟨nodup_map_of_injOn _ (hndphy.filter _) (fun a ha b hb =>
          hinj3 a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1),
        fun r hr => ((hmemphy r).mp (List.mem_filter.mp hr).1).2,
        fun r hr => by
          rw [hcl3]; exact hbr r ((hmemphy r).mp (List.mem_filter.mp hr).1).1⟩
  have hcl4 : sth4.colors.length = sth.colors.length := by rw [hl4, hcl3]
  -- equal final colours come from equal pass-2 colours
  have hback : ∀ r1 r2, r1 ∈ ru → r2 ∈ ru → holEl r1 sth4.colors = holEl r2 sth4.colors →
      holEl r1 sth3.colors = holEl r2 sth3.colors := fun r1 r2 h1 h2 he =>
    hinj4 r1 r2 ⟨by rw [hcl3]; exact hrub r1 h1, by rw [hcl3]; exact hrub r2 h2⟩ he
  refine ⟨sth4, ?run, ?inter, ?conv, ?forced, hcl4⟩
  case run =>
    have hp1 : stExFoldl (linearRegAllocStepPass1 fadj madj) (linearRegAllocPass1InitialState k)
        reglist s4 = (.success st1, sth1) := by simpa using hrunp1.symm
    have hp2 : stExFoldl (linearRegAllocStepPass2 fadj' madj')
        (linearRegAllocPass2InitialState k stacklist.length) stacklist sth2 =
        (.success st3, sth3) := by simpa using hrunp2.symm
    have e1 : applyRegExchange (List.filter (fun r => decide (r < 2 * k))
        (List.filter isPhyVar reglist)) sth1 = (.success (), sth2) := hrune1.symm
    have e3 : stExFoldl (linearRegAllocStepPass2
        (sptMap (List.filter fun r => decide (sptLookup r (sptFromAList
          (List.map (fun r => (r, ())) stacklist)) ≠ none)) fadj)
        (sptMap (List.filter fun r => decide (sptLookup r (sptFromAList
          (List.map (fun r => (r, ())) stacklist)) ≠ none)) madj))
        (linearRegAllocPass2InitialState k stacklist.length) stacklist sth2 =
        (.success st3, sth3) := hp2
    have e4 : applyRegExchange (List.filter (fun r => decide (2 * k ≤ r))
        (List.filter isPhyVar reglist)) sth3 = (.success (), sth4) := hrune2.symm
    simp only [linearRegAllocIntervals, ignoreBind, Translator.Monadic.MonadBase.bind, ret,
      ← hrun1, hrun2, hlist, ← hrun3, hrun4, hmlist, hmadj, hfadj, hp1]
    rw [e1]
    simp only
    rw [hfg]
    simp only
    rw [e3]
    exact e4
  case inter =>
    intro r1 r2 ⟨h1, h2, hi, he⟩
    have he3 := hback r1 r2 h1 h2 he
    have hr1 := (hmemr r1).mpr h1
    have hr2 := (hmemr r2).mpr h2
    by_cases e1 : r1 ∈ stacklist <;> by_cases e2 : r2 ∈ stacklist
    · exact g3.inter r1 r2 ⟨List.mem_reverse.mpr e1, List.mem_reverse.mpr e2,
        by rw [hbeg3, hend3]; exact hi, he3⟩
    · have := F1 r1 e1; have := F2 r2 hr2 e2; omega
    · have := F2 r1 hr1 e1; have := F1 r2 e2; omega
    · rw [hc3 r1 e1, hc3 r2 e2] at he3
      have he1 := hinj2 r1 r2 ⟨by rw [hcl1]; exact hrub r1 h1, by rw [hcl1]; exact hrub r2 h2⟩ he3
      exact g1.inter r1 r2 ⟨List.mem_reverse.mpr hr1, List.mem_reverse.mpr hr2,
        by rw [hbeg1, hend1]; exact hi, he1⟩
  case conv =>
    intro r hr
    have hrl := (hmemr r).mpr hr
    have hrb := hrub r hr
    split
    · next hphy =>
      by_cases hlt : r < 2 * k
      · have hpp : r ∈ phyphyregs :=
          List.mem_filter.mpr ⟨(hmemphy r).mpr ⟨hrl, hphy⟩, decide_eq_true hlt⟩
        have h2 := hval2 r hpp
        have hns : r ∉ stacklist := by
          intro hm
          rcases ((hmemst r).mp hm).2 with hs | hs
          · rw [stack_not_phy r hs] at hphy; cases hphy
          · rw [h2] at hs; omega
        have h3 : holEl r sth3.colors = r / 2 := by rw [hc3 r hns, h2]
        rw [hfix4 (fun r' hr' => F5 r' hr') r ⟨by rw [hcl3]; exact hrb, by rw [h3]; omega⟩, h3]
      · exact hval4 r (List.mem_filter.mpr ⟨(hmemphy r).mpr ⟨hrl, hphy⟩,
          decide_eq_true (by omega)⟩)
    · split
      · next _ hst =>
        have hin : r ∈ stacklist := (hmemst r).mpr ⟨hrl, Or.inl hst⟩
        exact (hiff4 (fun r' hr' => ⟨fun _ => (F5 r' hr').2, fun _ => (F5 r' hr').1⟩)
          r (by rw [hcl3]; exact hrb)).mp (F1 r hin)
      · trivial
  case forced =>
    intro x hx he
    obtain ⟨h1, h2⟩ := hfru x hx
    have he3 := hback x.1 x.2 h1 h2 he
    have hr1 := (hmemr _).mpr h1
    have hr2 := (hmemr _).mpr h2
    by_cases e1 : x.1 ∈ stacklist <;> by_cases e2 : x.2 ∈ stacklist
    · exact g3.forcedOk x ((hmemf' x).mpr ⟨hx, e1, e2⟩)
        ⟨List.mem_reverse.mpr e1, List.mem_reverse.mpr e2, he3⟩
    · have := F1 _ e1; have := F2 _ hr2 e2; omega
    · have := F2 _ hr1 e1; have := F1 _ e2; omega
    · rw [hc3 _ e1, hc3 _ e2] at he3
      have he1 := hinj2 _ _ ⟨by rw [hcl1]; exact hrub _ h1, by rw [hcl1]; exact hrub _ h2⟩ he3
      exact g1.forcedOk x hx ⟨List.mem_reverse.mpr hr1, List.mem_reverse.mpr hr2, he1⟩

end Flapjack.LinearScan
