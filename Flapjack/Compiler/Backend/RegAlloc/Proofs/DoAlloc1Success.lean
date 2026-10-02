import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs.FreezeSpillSuccess
import Flapjack.Basis.Pure.MlList.SortPerm

/-!
# reg_allocProof: success of the allocation step loop

Ports of `reg_allocProofScript.sml:2839-3022`: on a `good_ra_state` one `do_step`, the
bounded `rpt_do_step` loop, the move pre-check `full_consistency_ok` and its filter, and the
whole `do_alloc1` heuristic allocator succeed and preserve the state invariant, the graph,
the dimension and the node tags. Renderings as
in `PhaseSuccess`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- Exact HOL `do_step_success` (`reg_allocProofScript.sml:2839-2860`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_step_success"]
theorem doStepSuccess :
    ∀ (scost : Option (Spt Nat)) (k : Nat) (s : State),
      goodRaState s →
      ∃ (b : Bool) (s' : State), doStep scost k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro scost k s hg
  obtain ⟨s1, b1, h1, hg1, hs1, hd1, ht1⟩ := doSimplifySuccess k s hg
  cases b1 with
  | true =>
      exact ⟨true, s1, by simp only [doStep, Translator.Monadic.MonadBase.bind, h1, ↓reduceIte,
        ret], hg1, hs1, hd1, ht1⟩
  | false =>
  obtain ⟨s2, b2, h2, hg2, hs2, hd2, ht2⟩ := doCoalesceSuccess k s1 hg1
  have sub2 := isSubgraphTrans _ _ _ ⟨hs1, hs2⟩
  cases b2 with
  | true =>
      exact ⟨true, s2, by simp only [doStep, Translator.Monadic.MonadBase.bind, h1, h2,
        Bool.false_eq_true, ↓reduceIte, ret], hg2, sub2, hd1.trans hd2, ht1.trans ht2⟩
  | false =>
  obtain ⟨s3, b3, h3, hg3, hs3, hd3, ht3⟩ := doPrefreezeSuccess k s2 hg2
  have sub3 := isSubgraphTrans _ _ _ ⟨sub2, hs3⟩
  cases b3 with
  | true =>
      exact ⟨true, s3, by simp only [doStep, Translator.Monadic.MonadBase.bind, h1, h2, h3,
        Bool.false_eq_true, ↓reduceIte, ret], hg3, sub3, hd1.trans (hd2.trans hd3),
        ht1.trans (ht2.trans ht3)⟩
  | false =>
  obtain ⟨s4, b4, h4, hg4, hs4, hd4, ht4⟩ := doFreezeSuccess k s3 hg3
  have sub4 := isSubgraphTrans _ _ _ ⟨sub3, hs4⟩
  cases b4 with
  | true =>
      exact ⟨true, s4, by simp only [doStep, Translator.Monadic.MonadBase.bind, h1, h2, h3, h4,
        Bool.false_eq_true, ↓reduceIte, ret], hg4, sub4, hd1.trans (hd2.trans (hd3.trans hd4)),
        ht1.trans (ht2.trans (ht3.trans ht4))⟩
  | false =>
  obtain ⟨s5, b5, h5, hg5, hs5, hd5, ht5⟩ := doSpillSuccess scost k s4 hg4
  exact ⟨b5, s5, by simp only [doStep, Translator.Monadic.MonadBase.bind, h1, h2, h3, h4, h5,
      Bool.false_eq_true, ↓reduceIte, ret], hg5, isSubgraphTrans _ _ _ ⟨sub4, hs5⟩,
    hd1.trans (hd2.trans (hd3.trans (hd4.trans hd5))),
    ht1.trans (ht2.trans (ht3.trans (ht4.trans ht5)))⟩

/-- Exact HOL `rpt_do_step_success` (`reg_allocProofScript.sml:2863-2877`). `scost` is free
in HOL; HOL's universally bound `sc` occurs nowhere in the statement and is kept as an
unconstrained binder `(_sc : γ)` of a free type. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "rpt_do_step_success"]
theorem rptDoStepSuccess {γ : Type} (scost : Option (Spt Nat)) :
    ∀ (n : Nat) (s : State) (k : Nat) (_sc : γ),
      goodRaState s →
      ∃ s', rptDoStep scost k n s = (.success (), s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro n
  induction n with
  | zero => intro s k _ hg; exact ⟨s, rfl, hg, isSubgraphRefl _, rfl, rfl⟩
  | succ c ih =>
      intro s k sc hg
      obtain ⟨b, s1, h1, hg1, hs1, hd1, ht1⟩ := doStepSuccess scost k s hg
      cases b with
      | false =>
          exact ⟨s1, by simp only [rptDoStep, Translator.Monadic.MonadBase.bind, h1,
            Bool.false_eq_true, ↓reduceIte, ret], hg1, hs1, hd1, ht1⟩
      | true =>
          obtain ⟨s2, h2, hg2, hs2, hd2, ht2⟩ := ih s1 k sc hg1
          exact ⟨s2, by simp only [rptDoStep, Translator.Monadic.MonadBase.bind, h1, ↓reduceIte,
            h2], hg2, isSubgraphTrans _ _ _ ⟨hs1, hs2⟩, hd1.trans hd2, ht1.trans ht2⟩

private theorem isFixedK_ok {s : State} (hg : goodRaState s) (k : Nat) {x : Nat}
    (hx : x < s.dim) : ∃ b, isFixedK k x s = (.success b, s) := by
  have hl : x < s.node_tag.length := by rw [hg.2.1]; exact hx
  refine ⟨match holEl x s.node_tag with | .Fixed n => decide (n < k) | _ => false, ?_⟩
  simp only [isFixedK, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hl, ret]
  rfl

private theorem isAtemp_ok {s : State} (hg : goodRaState s) {x : Nat} (hx : x < s.dim) :
    ∃ b, isAtemp x s = (.success b, s) := by
  have hl : x < s.node_tag.length := by rw [hg.2.1]; exact hx
  exact ⟨decide (holEl x s.node_tag = .Atemp), by
    simp only [isAtemp, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hl, ret]⟩

/-- Exact HOL `full_consistency_ok_success` (`reg_allocProofScript.sml:2879-2891`); `k` is
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "full_consistency_ok_success"]
theorem fullConsistencyOkSuccess (k : Nat) :
    ∀ (x y : Nat) (s : State),
      goodRaState s →
      ∃ b, fullConsistencyOk k x y s = (.success b, s) ∧ (b = true → x < s.dim ∧ y < s.dim) := by
  intro x y s hg
  unfold fullConsistencyOk
  by_cases hxy : x = y
  · exact ⟨false, by rw [if_pos hxy]; rfl, fun h => by cases h⟩
  rw [if_neg hxy]
  by_cases hb : x ≥ s.dim ∨ y ≥ s.dim
  · exact ⟨false, by simp only [Translator.Monadic.MonadBase.bind, getDim, if_pos hb, ret],
      fun h => by cases h⟩
  have hx : x < s.dim := by omega
  have hy : y < s.dim := by omega
  have hyl : y < s.adj_ls.length := by rw [hg.1]; exact hy
  by_cases hm : sortedMem x (holEl y s.adj_ls) = true
  · exact ⟨false, by simp only [Translator.Monadic.MonadBase.bind, getDim, if_neg hb, adjLsSubEqn,
      if_pos hyl, if_pos hm, ret], fun h => by cases h⟩
  obtain ⟨bx, hbx⟩ := isFixedK_ok hg k hx
  obtain ⟨by_, hby⟩ := isFixedK_ok hg k hy
  obtain ⟨ax, hax⟩ := isAtemp_ok hg hx
  obtain ⟨ay, hay⟩ := isAtemp_ok hg hy
  exact ⟨(bx || ax) && (by_ || ay) && !(bx && by_), by
    simp only [Translator.Monadic.MonadBase.bind, getDim, if_neg hb, adjLsSubEqn, if_pos hyl,
      if_neg hm, hbx, hby, hax, hay, ret], fun _ => ⟨hx, hy⟩⟩

/-- Exact HOL `st_ex_FILTER_full_consistency_ok` (`reg_allocProofScript.sml:2893-2916`); `k`
is free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FILTER_full_consistency_ok"]
theorem stExFilterFullConsistencyOk (k : Nat) :
    ∀ (ls acc : List (Nat × (Nat × Nat))) (s : State),
      goodRaState s →
      ∃ ts, stExFilter (fun (m : Nat × (Nat × Nat)) => fullConsistencyOk k m.2.1 m.2.2) ls acc s =
          (.success ts, s) ∧
        ∀ m ∈ ts, (m.2.1 < s.dim ∧ m.2.2 < s.dim) ∨ m ∈ acc := by
  intro ls
  induction ls with
  | nil => intro acc s _; exact ⟨acc, rfl, fun m hm => Or.inr hm⟩
  | cons m ms ih =>
      intro acc s hg
      obtain ⟨b, hrun, hbd⟩ := fullConsistencyOkSuccess k m.2.1 m.2.2 s hg
      cases b with
      | true =>
          obtain ⟨ts, hts, hmem⟩ := ih (m :: acc) s hg
          refine ⟨ts, ?_, fun m' hm' => ?_⟩
          · simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun, if_true]
            exact hts
          rcases hmem m' hm' with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl (hbd rfl)
            · exact Or.inr h
      | false =>
          obtain ⟨ts, hts, hmem⟩ := ih acc s hg
          refine ⟨ts, ?_, hmem⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun]
          exact hts

/-! ### `do_alloc1` initialisation (Flapjack infrastructure) -/

private theorem filter_isAtemp (s : State) (hg : goodRaState s) :
    ∀ (ls acc : List Nat), (∀ v ∈ ls, v < s.dim) → (∀ v ∈ acc, v < s.dim) →
      ∃ ts, stExFilter isAtemp ls acc s = (.success ts, s) ∧ ∀ v ∈ ts, v < s.dim
  | [], acc, _, hacc => ⟨acc, rfl, hacc⟩
  | v :: vs, acc, hb, hacc => by
      have hv := hb v List.mem_cons_self
      have hvs : ∀ w ∈ vs, w < s.dim := fun w hw => hb w (List.mem_cons_of_mem _ hw)
      obtain ⟨b, hrun⟩ := isAtemp_ok hg hv
      cases b with
      | true =>
          obtain ⟨ts, hts, htb⟩ := filter_isAtemp s hg vs (v :: acc) hvs (fun w hw => by
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hv
            · exact hacc w hw)
          refine ⟨ts, ?_, htb⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun, if_true]
          exact hts
      | false =>
          obtain ⟨ts, hts, htb⟩ := filter_isAtemp s hg vs acc hvs hacc
          refine ⟨ts, ?_, htb⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun, Bool.false_eq_true,
            ↓reduceIte]
          exact hts

/-- The degree-initialisation traversal only rewrites the degree array. -/
private theorem foreach_init_degrees (k : Nat) :
    ∀ (ls : List Nat) (s : State), goodRaState s → (∀ v ∈ ls, v < s.dim) →
      ∃ d, stExForeach ls (fun i =>
          bind (adjLsSub i) fun adjls =>
            bind (stExFilter (fun v => consideredVar k v) adjls []) fun fills =>
              updateDegrees i fills.length) s = (.success (), { s with degrees := d }) ∧
        d.length = s.degrees.length
  | [], s, _, _ => ⟨s.degrees, rfl, rfl⟩
  | i :: is, s, hg, hb => by
      have hi := hb i List.mem_cons_self
      have hil : i < s.adj_ls.length := by rw [hg.1]; exact hi
      have hid : i < s.degrees.length := by rw [hg.2.2.1]; exact hi
      obtain ⟨fills, hf, _⟩ := stExFilterConsideredVar k (holEl i s.adj_ls) [] s
        ⟨fun v hv => by rw [hg.2.1]; exact good_adj hg hi v hv, fun _ h => by cases h⟩
      have hg' : goodRaState { s with degrees := s.degrees.set i fills.length } := by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
        exact ⟨g1, g2, (List.length_set ..).trans g3, g4, g5, g6, g7, g8, g9, g10, g11, g12,
          g13, g14⟩
      obtain ⟨d, hd, hdl⟩ := foreach_init_degrees k is _ hg'
        (fun v hv => hb v (List.mem_cons_of_mem _ hv))
      refine ⟨d, ?_, hdl.trans (List.length_set ..)⟩
      simp only [stExForeach, ignoreBind, Translator.Monadic.MonadBase.bind, adjLsSubEqn,
        if_pos hil, hf, updateDegreesEqn, if_pos hid]
      exact hd

private theorem good_coalesced' {s : State} {c : List Nat} (h : goodRaState s)
    (hl : c.length = s.dim) (hv : ∀ v ∈ c, v < s.dim) :
    goodRaState { s with coalesced := c } := by
  obtain ⟨h1, h2, h3, _, h5, _, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, hl, h5, hv, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The coalesce-pointer initialisation keeps every pointer in range. -/
private theorem foreach_upd_coalesce :
    ∀ (ls : List Nat) (s : State), goodRaState s → (∀ v ∈ ls, v < s.dim) →
      ∃ coal, stExForeach ls doUpdCoalesce s = (.success (), { s with coalesced := coal }) ∧
        goodRaState { s with coalesced := coal }
  | [], s, hg, _ => ⟨s.coalesced, rfl, hg⟩
  | i :: is, s, hg, hb => by
      have hi := hb i List.mem_cons_self
      have hic : i < s.coalesced.length := by rw [hg.2.2.2.1]; exact hi
      have hg' : goodRaState { s with coalesced := s.coalesced.set i (0 + i) } :=
        good_coalesced' hg (by rw [List.length_set]; exact hg.2.2.2.1) (fun v hv => by
          rcases List.mem_or_eq_of_mem_set hv with hv | rfl
          · exact hg.2.2.2.2.2.1 v hv
          · omega)
      obtain ⟨coal, hc, hgc⟩ := foreach_upd_coalesce is _ hg'
        (fun v hv => hb v (List.mem_cons_of_mem _ hv))
      refine ⟨coal, ?_, hgc⟩
      simp only [stExForeach, ignoreBind, doUpdCoalesce, updateCoalescedEqn, if_pos hic]
      exact hc

/-- Exact HOL `do_alloc1_success` (`reg_allocProofScript.sml:2918-3022`); `s`, `moves`,
`scost` and `k` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_alloc1_success"]
theorem doAlloc1Success (s : State) (moves : List (Nat × (Nat × Nat)))
    (scost : Option (Spt Nat)) (k : Nat) :
    goodRaState s ∧ (∀ m ∈ moves, m.2.1 < s.dim ∧ m.2.2 < s.dim) →
    ∃ ls s', doAlloc1 moves scost k s = (.success ls, s') ∧ goodRaState s' ∧
      isSubgraph s.adj_ls s'.adj_ls ∧ s'.dim = s.dim ∧ s'.node_tag = s.node_tag := by
  intro ⟨hg, hmv⟩
  have hds : ∀ v ∈ List.range s.dim, v < s.dim := fun v hv => List.mem_range.mp hv
  obtain ⟨atemps, h1, hat⟩ := filter_isAtemp s hg (List.range s.dim) [] hds (fun _ h => by cases h)
  obtain ⟨d, h2, hdl⟩ := foreach_init_degrees k (List.range s.dim) s hg hds
  have hg2 : goodRaState { s with degrees := d } := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
    exact ⟨g1, g2, hdl.trans g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
  obtain ⟨coal, h3, hg3⟩ := foreach_upd_coalesce (List.range s.dim) _ hg2 hds
  have hg4 : goodRaState { s with degrees := d, coalesced := coal,
                                  avail_moves_wl := sortMoves moves } := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, _, g13, g14⟩ := hg3
    exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11,
      fun m hm => hmv m ((Basis.Pure.MlList.sortMem m _ moves).mp hm), g13, g14⟩
  obtain ⟨mv, h5, hmvl⟩ := resetMoveRelatedSuccess moves _ ⟨hg4, hmv⟩
  have hg5 : goodRaState { s with degrees := d, coalesced := coal,
                                  avail_moves_wl := sortMoves moves, move_related := mv } := by
    obtain ⟨g1, g2, g3, g4, _, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg4
    exact ⟨g1, g2, g3, g4, hmvl, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
  obtain ⟨ltk, gtk, h6, hltk, hgtk⟩ := stExPartitionSplitDegree atemps k [] [] _ hg5
  obtain ⟨ltkf, ltks, h7, hltkf, hltks⟩ := stExPartitionMoveRelatedSub ltk [] []
    { s with degrees := d, coalesced := coal, avail_moves_wl := sortMoves moves,
             move_related := mv }
    (fun x hx => by
      show x < mv.length
      rw [hmvl]
      rcases hltk x hx with h | h
      · cases h
      · exact hat x h)
  have hsub : ∀ {l l0 : List Nat}, (∀ x ∈ l, x ∈ [] ∨ x ∈ l0) → (∀ x ∈ l0, x < s.dim) →
      ∀ x ∈ l, x < s.dim := fun h h0 x hx => by
    rcases h x hx with h | h
    · cases h
    · exact h0 x h
  have hltkd : ∀ x ∈ ltk, x < s.dim := hsub hltk hat
  have hg8 : goodRaState { s with degrees := d, coalesced := coal,
                                  avail_moves_wl := sortMoves moves, move_related := mv,
                                  spill_wl := gtk, simp_wl := ltks, freeze_wl := ltkf } := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _, _, _, g12, g13, g14⟩ := hg5
    exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, hsub hltks hltkd, hsub hgtk hat, hsub hltkf hltkd,
      g12, g13, g14⟩
  obtain ⟨s', h9, hg9, hs9, hd9, ht9⟩ := rptDoStepSuccess scost atemps.length _ k scost hg8
  refine ⟨s'.stack, s', ?_, hg9, hs9, hd9.symm, ht9.symm⟩
  simp only [doAlloc1, Translator.Monadic.MonadBase.bind, ignoreBind, getDim, initAlloc1Heu,
    ret, h1, h2, h3, setAvailMovesWl, h5, h6, h7, setSpillWl, setSimpWl, setFreezeWl, h9,
    getStack]

end Flapjack.RegAlloc
