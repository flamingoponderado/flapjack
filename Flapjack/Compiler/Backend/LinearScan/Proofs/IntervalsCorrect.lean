import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan.Proofs.SortCorrect
import Flapjack.Compiler.Backend.LinearScan.TopLevel

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

end Flapjack.LinearScan
