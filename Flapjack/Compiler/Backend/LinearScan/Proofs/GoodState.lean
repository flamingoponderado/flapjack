import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan
import Flapjack.Compiler.Backend.LinearScan.Steps
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange
import Flapjack.Misc.ListEl
import Flapjack.Misc.Relation
import Flapjack.Misc.Sorting

/-!
# linear_scanProof: `good_linear_scan_state` and colour search

Ports of `linear_scanProofScript.sml:2404-2696`: the active-list order
`less_FST`, the colouring-state invariant `good_linear_scan_state`, and its
preservation by releasing inactive intervals and by finding a colour, plus the
shape of `add_active_interval` and `find_color_in_list`. HOL `EL` is the exact
`holEl`, `SORTED` the exact `holSorted`, `transitive` the exact
`holTransitive`, `ALL_DISTINCT` is `List.Nodup`, `EVERY P l` is
`∀ x, x ∈ l → P x` (a paired `\(e,r). P e r` reads the components `x.1`, `x.2`),
`domain t` is `sptDomain t`, the set `{f r | r | P r}` is the predicate
`fun c => ∃ r, c = f r ∧ P r`, and `s ⊆ t` is pointwise implication.
-/

namespace Flapjack.LinearScan

open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `less_FST` (`linear_scanProofScript.sml:2404-2406`); as in HOL
(`int # num -> int # α -> bool`), the second argument's register component is
an arbitrary carrier. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml" "less_FST_def"]
def lessFst {α : Type} (x : Int × Nat) (y : Int × α) : Prop := x.1 ≤ y.1

/-- Exact HOL `transitive_less_FST` (`linear_scanProofScript.sml:2408-2413`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "transitive_less_FST"]
theorem transitiveLessFst : holTransitive (lessFst (α := Nat)) := by
  intro x y z ⟨h1, h2⟩
  exact Int.le_trans h1 h2

/-- Exact HOL `good_linear_scan_state` (`linear_scanProofScript.sml:2415-2443`),
conjunct for conjunct. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "good_linear_scan_state_def"]
def goodLinearScanState (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
    (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat) : Prop :=
  sth.int_beg.length = sth.colors.length ∧ sth.int_end.length = sth.colors.length ∧
  (st.colorpool ++ st.active.map (fun x => holEl x.2 sth.colors)).Nodup ∧
  (∀ r, r ∈ l → r < sth.colors.length) ∧
  (∀ r, r ∈ l → holEl r sth.colors < st.stacknum) ∧
  sptDomain st.phyregs =
    (fun c => ∃ r, c = holEl r sth.colors ∧
      (r ∈ l ∧ isPhyVar r ∧ holEl r sth.colors < st.colormax)) ∧
  ((l.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup ∧
  (∀ c, c ∈ st.colorpool → c < st.colornum) ∧
  (∀ x, x ∈ st.active → holEl x.2 sth.colors < st.colornum) ∧
  st.colornum ≤ st.colormax ∧
  st.colormax ≤ st.stacknum ∧
  (∀ r, r ∈ l → holEl r sth.colors < st.colormax → holEl r sth.colors < st.colornum) ∧
  (∀ r, r ∈ l → holEl r sth.int_beg ≤ pos) ∧
  (∀ r, r ∈ l → pos ≤ holEl r sth.int_end ∧ holEl r sth.colors < st.colormax →
    (holEl r sth.int_end, r) ∈ st.active) ∧
  (∀ r, r ∈ l → (holEl r sth.int_end, r) ∈ st.active → pos ≤ 1 + holEl r sth.int_end) ∧
  (∀ r1 r2, r1 ∈ l ∧ r2 ∈ l ∧
    intervalIntersect (holEl r1 sth.int_beg, holEl r1 sth.int_end)
      (holEl r2 sth.int_beg, holEl r2 sth.int_end) ∧
    holEl r1 sth.colors = holEl r2 sth.colors → r1 = r2) ∧
  holSorted lessFst st.active ∧
  (∀ x, x ∈ st.active → x.1 = holEl x.2 sth.int_end) ∧
  (∀ x, x ∈ st.active → x.2 ∈ l) ∧
  (∀ x, x ∈ forced → x.1 ∈ l ∧ x.2 ∈ l ∧ holEl x.1 sth.colors = holEl x.2 sth.colors →
    x.1 = x.2) ∧
  mincol ≤ st.colornum ∧
  (∀ c, c ∈ st.colorpool ++ l.map (fun r => holEl r sth.colors) → mincol ≤ c)

/-- The conjuncts of `goodLinearScanState`, named for the proofs of this and
later linear_scanProof modules. Flapjack infrastructure with no HOL original:
`goodLinearScanState_iff` shows it is the same proposition. -/
structure GoodFields (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
    (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat) : Prop where
  lenBeg : sth.int_beg.length = sth.colors.length
  lenEnd : sth.int_end.length = sth.colors.length
  distinct : (st.colorpool ++ st.active.map (fun x => holEl x.2 sth.colors)).Nodup
  bound : ∀ r, r ∈ l → r < sth.colors.length
  stack : ∀ r, r ∈ l → holEl r sth.colors < st.stacknum
  phy : sptDomain st.phyregs =
    (fun c => ∃ r, c = holEl r sth.colors ∧
      (r ∈ l ∧ isPhyVar r ∧ holEl r sth.colors < st.colormax))
  phyDistinct : ((l.filter isPhyVar).map (fun r => holEl r sth.colors)).Nodup
  pool : ∀ c, c ∈ st.colorpool → c < st.colornum
  active : ∀ x, x ∈ st.active → holEl x.2 sth.colors < st.colornum
  numMax : st.colornum ≤ st.colormax
  maxStack : st.colormax ≤ st.stacknum
  colMax : ∀ r, r ∈ l → holEl r sth.colors < st.colormax → holEl r sth.colors < st.colornum
  beg : ∀ r, r ∈ l → holEl r sth.int_beg ≤ pos
  live : ∀ r, r ∈ l → pos ≤ holEl r sth.int_end ∧ holEl r sth.colors < st.colormax →
    (holEl r sth.int_end, r) ∈ st.active
  ends : ∀ r, r ∈ l → (holEl r sth.int_end, r) ∈ st.active → pos ≤ 1 + holEl r sth.int_end
  inter : ∀ r1 r2, r1 ∈ l ∧ r2 ∈ l ∧
    intervalIntersect (holEl r1 sth.int_beg, holEl r1 sth.int_end)
      (holEl r2 sth.int_beg, holEl r2 sth.int_end) ∧
    holEl r1 sth.colors = holEl r2 sth.colors → r1 = r2
  sorted : holSorted lessFst st.active
  activeEnd : ∀ x, x ∈ st.active → x.1 = holEl x.2 sth.int_end
  activeMem : ∀ x, x ∈ st.active → x.2 ∈ l
  forcedOk : ∀ x, x ∈ forced → x.1 ∈ l ∧ x.2 ∈ l ∧ holEl x.1 sth.colors = holEl x.2 sth.colors →
    x.1 = x.2
  minNum : mincol ≤ st.colornum
  minAll : ∀ c, c ∈ st.colorpool ++ l.map (fun r => holEl r sth.colors) → mincol ≤ c

/-- `goodLinearScanState` is the conjunction named by `GoodFields`. -/
theorem goodLinearScanState_iff {st sth l pos forced mincol} :
    goodLinearScanState st sth l pos forced mincol ↔ GoodFields st sth l pos forced mincol := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22⟩

/-- Every later interval of a `less_FST`-sorted active list ends no earlier than
its head. -/
private theorem sorted_head_le {e : Int} {r : Nat} {tail : List (Int × Nat)}
    (h : holSorted lessFst ((e, r) :: tail)) : ∀ x, x ∈ tail → e ≤ x.1 :=
  ((holSortedEq lessFst tail (e, r) transitiveLessFst).mp h).2

/-- `remove_inactive_intervals` unfolded once at a state, with a non-dependent
match on the active list. -/
private theorem removeInactiveIntervals_unfold (beg : Int) (st : LinearScanState)
    (s : LinearScanHiddenState) :
    removeInactiveIntervals beg st s =
      match st.active with
      | [] => (.success st, s)
      | (e, r) :: activetail =>
          if e < beg then
            bind (colorsSub r) (fun col =>
              removeInactiveIntervals beg
                { st with active := activetail, colorpool := col :: st.colorpool }) s
          else (.success st, s) := by
  rcases st with ⟨active, colorpool, phyregs, colornum, colormax, stacknum⟩
  cases active with
  | nil => rw [removeInactiveIntervals]; dsimp only [ret]
  | cons p t =>
    obtain ⟨e, r⟩ := p
    rw [removeInactiveIntervals]
    dsimp only
    split <;> rfl

/-- Exact HOL `remove_inactive_intervals_invariants`
(`linear_scanProofScript.sml:2453-2559`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "remove_inactive_intervals_invariants"]
theorem removeInactiveIntervalsInvariants :
    ∀ (beg : Int) (st : LinearScanState) (sth : LinearScanHiddenState) (l : List Nat)
      (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat),
      goodLinearScanState st sth l pos forced mincol ∧ pos ≤ beg →
      ∃ stout, (.success stout, sth) = removeInactiveIntervals beg st sth ∧
        goodLinearScanState stout sth l beg forced mincol ∧
        stout.colormax = st.colormax := by
  intro beg st
  -- induction on the length of the active list
  generalize hn : st.active.length = n
  induction n using Nat.strongRecOn generalizing st with
  | ind n ih =>
  intro sth l pos forced mincol ⟨hg, hpb⟩
  have g := goodLinearScanState_iff.mp hg
  rw [removeInactiveIntervals_unfold]
  split
  · next hact =>
    refine ⟨st, rfl, goodLinearScanState_iff.mpr { g with
      beg := fun r hr => Int.le_trans (g.beg r hr) hpb
      live := fun r hr ⟨h1, h2⟩ => g.live r hr ⟨Int.le_trans hpb h1, h2⟩
      ends := fun r _ hm => by rw [hact] at hm; cases hm }, rfl⟩
  · next e r activetail hact =>
    have hmem : (e, r) ∈ st.active := by rw [hact]; exact List.mem_cons_self
    have hrl : r ∈ l := g.activeMem _ hmem
    have hrc : r < sth.colors.length := g.bound r hrl
    have he : e = holEl r sth.int_end := g.activeEnd _ hmem
    have hsort : holSorted lessFst ((e, r) :: activetail) := hact ▸ g.sorted
    have hle := sorted_head_le hsort
    split
    · next hlt =>
      simp only [Translator.Monadic.MonadBase.bind, colorsSubEqn, if_pos hrc]
      let st' : LinearScanState :=
        { st with active := activetail, colorpool := holEl r sth.colors :: st.colorpool }
      have hpe : pos ≤ e + 1 := by
        have := g.ends r hrl (he ▸ hmem); omega
      have hd : (st'.colorpool ++ st'.active.map (fun x => holEl x.2 sth.colors)).Nodup := by
        have h := g.distinct
        rw [hact, List.map_cons] at h
        exact (List.perm_middle.nodup_iff).mp h
      have g' : GoodFields st' sth l (e + 1) forced mincol :=
        { g with
          distinct := hd
          pool := fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc
            · exact g.active _ hmem
            · exact g.pool c hc
          active := fun x hx => g.active x (by rw [hact]; exact List.mem_cons_of_mem _ hx)
          beg := fun r' hr' => Int.le_trans (g.beg r' hr') hpe
          live := fun r' hr' ⟨h1, h2⟩ => by
            have hm := g.live r' hr' ⟨Int.le_trans hpe h1, h2⟩
            rw [hact] at hm
            rcases List.mem_cons.mp hm with heq | hm
            · simp only [Prod.mk.injEq] at heq; omega
            · exact hm
          ends := fun r' _ hm => by
            have := hle _ hm; simp only at this; omega
          sorted := holSortedTl _ _ _ hsort
          activeEnd := fun x hx => g.activeEnd x (by rw [hact]; exact List.mem_cons_of_mem _ hx)
          activeMem := fun x hx => g.activeMem x (by rw [hact]; exact List.mem_cons_of_mem _ hx)
          minAll := fun c hc => by
            rcases List.mem_cons.mp hc with rfl | hc
            · exact g.minAll _ (List.mem_append_right _ (List.mem_map_of_mem hrl))
            · exact g.minAll c hc }
      have hlen : st'.active.length < n := by
        rw [← hn, hact]; simp [st']
      obtain ⟨stout, hrun, hgood, hmax⟩ :=
        ih _ hlen st' rfl sth l (e + 1) forced mincol ⟨goodLinearScanState_iff.mpr g', by omega⟩
      exact ⟨stout, hrun, hgood, hmax⟩
    · next hge =>
      have hall : ∀ x, x ∈ st.active → beg ≤ x.1 := by
        intro x hx
        rw [hact] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only; omega
        · have := hle x hx; omega
      refine ⟨st, rfl, goodLinearScanState_iff.mpr { g with
        beg := fun r' hr' => Int.le_trans (g.beg r' hr') hpb
        live := fun r' hr' ⟨h1, h2⟩ => g.live r' hr' ⟨Int.le_trans hpb h1, h2⟩
        ends := fun r' _ hm => by have := hall _ hm; simp only at this; omega }, rfl⟩

/-- Exact HOL `add_active_interval_output` (`linear_scanProofScript.sml:2561-2592`).
`e` and `r` are free in HOL; the unused binder `x` keeps its polymorphic HOL
type `α`. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "add_active_interval_output"]
theorem addActiveIntervalOutput {β : Type} (e : Int) (r : Nat) :
    ∀ (lin : List (Int × Nat)) (_x : β) (lout : List (Int × Nat)),
      holSorted lessFst lin ∧ lout = addActiveInterval (e, r) lin →
      holSorted lessFst lout ∧ ∃ l1 l2, lin = l1 ++ l2 ∧ lout = l1 ++ (e, r) :: l2 := by
  intro lin _ lout ⟨hs, hout⟩
  subst hout
  induction lin with
  | nil => exact ⟨trivial, [], [], rfl, rfl⟩
  | cons h t ih =>
      have hst := holSortedTl _ _ _ hs
      obtain ⟨ihs, l1, l2, ht, hadd⟩ := ih hst
      simp only [addActiveInterval]
      split
      · next hle =>
        exact ⟨⟨hle, hs⟩, [], h :: t, rfl, rfl⟩
      · next hgt =>
        refine ⟨?_, h :: l1, l2, by rw [ht]; rfl, by rw [hadd]; rfl⟩
        refine (holSortedEq lessFst _ h transitiveLessFst).mpr ⟨ihs, fun y hy => ?_⟩
        rw [hadd] at hy
        have hht := sorted_head_le (e := h.1) (r := h.2) (tail := t) hs
        rcases List.mem_append.mp hy with hy | hy
        · exact hht y (by rw [ht]; exact List.mem_append_left _ hy)
        · rcases List.mem_cons.mp hy with rfl | hy
          · show h.1 ≤ e; omega
          · exact hht y (by rw [ht]; exact List.mem_append_right _ hy)

/-- Exact HOL `find_color_in_list_output` (`linear_scanProofScript.sml:2594-2621`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_color_in_list_output"]
theorem findColorInListOutput :
    ∀ (forbidden : NumSet) (col : Nat) (l rest : List Nat),
      findColorInList l forbidden = some (col, rest) →
      col ∈ l ∧ ¬ sptDomain forbidden col ∧
        ∃ l1 l2, rest = l1 ++ l2 ∧ l = l1 ++ col :: l2 := by
  intro forbidden col l
  induction l generalizing col with
  | nil => intro rest h; simp [findColorInList] at h
  | cons h t ih =>
      intro rest hf
      simp only [findColorInList] at hf
      split at hf
      · next hn =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        refine ⟨List.mem_cons_self, by simp [sptDomain, hn], [], t, rfl, rfl⟩
      · split at hf
        · cases hf
        · next c rest' hrec =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          obtain ⟨hm, hnd, l1, l2, hr, ht⟩ := ih c rest' hrec
          exact ⟨List.mem_cons_of_mem _ hm, hnd, h :: l1, l2, by rw [hr]; rfl,
            by rw [ht]; rfl⟩

/-- Exact HOL `find_color_in_colornum_invariants`
(`linear_scanProofScript.sml:2623-2658`); `stout` and `col` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_color_in_colornum_invariants"]
theorem findColorInColornumInvariants (stout : LinearScanState) (col : Nat) :
    ∀ (st : LinearScanState) (forbidden : NumSet) (sth : LinearScanHiddenState)
      (l : List Nat) (pos : Int) (forced : List (Nat × Nat)) (mincol : Nat),
      goodLinearScanState st sth l pos forced mincol ∧
      (∀ c, sptDomain forbidden c → ∃ r, c = holEl r sth.colors ∧ r ∈ l) ∧
      findColorInColornum st forbidden = (stout, some col) →
      goodLinearScanState { stout with colorpool := col :: stout.colorpool } sth l pos forced
          mincol ∧
        st.colornum ≤ col ∧ col < stout.colornum ∧ st.colornum ≤ stout.colornum ∧
        ¬ sptDomain forbidden col ∧
        st = { stout with colorpool := st.colorpool, colornum := st.colornum } := by
  intro st forbidden sth l pos forced mincol ⟨hg, hsub, hf⟩
  have g := goodLinearScanState_iff.mp hg
  simp only [findColorInColornum] at hf
  split at hf
  · cases hf
  · next hlt =>
    simp only [Prod.mk.injEq, Option.some.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine ⟨goodLinearScanState_iff.mpr ?_, Nat.le_refl _, Nat.lt_succ_self _, Nat.le_succ _, ?_, rfl⟩
    · refine { g with
        distinct := ?_
        pool := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (g.pool c hc)
        active := fun x hx => Nat.lt_succ_of_lt (g.active x hx)
        numMax := by simp only; omega
        colMax := fun r hr h => Nat.lt_succ_of_lt (g.colMax r hr h)
        minNum := Nat.le_succ_of_le g.minNum
        minAll := fun c hc => by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact g.minNum
          · exact g.minAll c hc }
      refine List.nodup_cons.mpr ⟨fun hm => ?_, g.distinct⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact Nat.lt_irrefl _ (g.pool _ hm)
      · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        have := g.active x hx
        omega
    · intro hd
      obtain ⟨r, hc, hr⟩ := hsub _ hd
      have := g.colMax r hr (by rw [← hc]; omega)
      omega

/-- Exact HOL `find_color_invariants` (`linear_scanProofScript.sml:2660-2695`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml"
  "find_color_invariants"]
theorem findColorInvariants :
    ∀ (st : LinearScanState) (forbidden : NumSet) (stout : LinearScanState) (col : Nat)
      (sth : LinearScanHiddenState) (l : List Nat) (pos : Int) (forced : List (Nat × Nat))
      (mincol : Nat),
      goodLinearScanState st sth l pos forced mincol ∧
      (∀ c, sptDomain forbidden c → ∃ r, c = holEl r sth.colors ∧ r ∈ l) ∧
      findColor st forbidden = (stout, some col) →
      goodLinearScanState { stout with colorpool := col :: stout.colorpool } sth l pos forced
          mincol ∧
        col < stout.colornum ∧ ¬ sptDomain forbidden col ∧
        st = { stout with colorpool := st.colorpool, colornum := st.colornum } := by
  intro st forbidden stout col sth l pos forced mincol ⟨hg, hsub, hf⟩
  unfold findColor at hf
  split at hf
  · next c rest hfl =>
    simp only [Prod.mk.injEq, Option.some.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    obtain ⟨hm, hnd, l1, l2, hrest, hpool⟩ := findColorInListOutput forbidden c st.colorpool rest hfl
    have g := goodLinearScanState_iff.mp hg
    have hperm : (c :: rest).Perm st.colorpool := by
      rw [hrest, hpool]; exact List.perm_middle.symm
    have hmemEq : ∀ y, y ∈ c :: rest ↔ y ∈ st.colorpool := fun y => hperm.mem_iff
    refine ⟨goodLinearScanState_iff.mpr { g with
      distinct := (hperm.append_right _).nodup_iff.mpr g.distinct
      pool := fun y hy => g.pool y ((hmemEq y).mp hy)
      minAll := fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact g.minAll y (List.mem_append_left _ ((hmemEq y).mp hy))
        · exact g.minAll y (List.mem_append_right _ hy) },
      g.pool c hm, hnd, rfl⟩
  · next hnone =>
    obtain ⟨hgood, _, hlt, _, hnd, heq⟩ :=
      findColorInColornumInvariants stout col st forbidden sth l pos forced mincol ⟨hg, hsub, hf⟩
    exact ⟨hgood, hlt, hnd, heq⟩

end Flapjack.LinearScan
