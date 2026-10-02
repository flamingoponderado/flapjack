import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs.PhaseSuccess
import Flapjack.Compiler.Backend.RegAlloc.Proofs.EdgeInsertion
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ConsideredVarFilter
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MoveRelatedForeach
import Flapjack.Compiler.Backend.RegAlloc.Proofs.NotCoalescedFilter
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MoveRelatedPartition

/-!
# reg_allocProof: success of the coalesce phase

Ports of `reg_allocProofScript.sml:2301-2725`: on a `good_ra_state` the move
consistency and Briggs/George checks, coalesce-pointer chasing, move
canonicalisation, the first-coalescible-move search, the coalescing step
itself and the prefreeze reset succeed and preserve the state invariant.
Renderings as in `PhaseSuccess`; HOL `case opt of NONE => T | SOME (a, b) => P`
is a Lean `match`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-! ### Reading the node tags (Flapjack infrastructure) -/

private theorem isFixed_ok {s : State} (hg : goodRaState s) {x : Nat} (hx : x < s.dim) :
    ∃ b, isFixed x s = (.success b, s) := by
  have hl : x < s.node_tag.length := by rw [hg.2.1]; exact hx
  refine ⟨match holEl x s.node_tag with | .Fixed _ => true | _ => false, ?_⟩
  simp only [isFixed, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hl, ret]
  rfl

private theorem good_coalesced {s : State} {c : List Nat} (h : goodRaState s)
    (hl : c.length = s.dim) (hv : ∀ v ∈ c, v < s.dim) :
    goodRaState { s with coalesced := c } := by
  obtain ⟨h1, h2, h3, _, h5, _, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, hl, h5, hv, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Exact HOL `consistency_ok_success` (`reg_allocProofScript.sml:2301-2318`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "consistency_ok_success"]
theorem consistencyOkSuccess :
    ∀ (x y : Nat) (s : State),
      goodRaState s ∧ x < s.dim ∧ y < s.dim →
      ∃ b, consistencyOk x y s = (.success b, s) ∧ (b = true → x < s.dim ∧ y < s.dim) := by
  intro x y s ⟨hg, hx, hy⟩
  refine (fun h => ?_) (show ∃ b, consistencyOk x y s = (.success b, s) from ?_)
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, hb, fun _ => ⟨hx, hy⟩⟩
  have hyl : y < s.adj_ls.length := by rw [hg.1]; exact hy
  have hxm : x < s.move_related.length := by rw [hg.2.2.2.2.1]; exact hx
  have hym : y < s.move_related.length := by rw [hg.2.2.2.2.1]; exact hy
  obtain ⟨bx, hbx⟩ := isFixed_ok hg hx
  obtain ⟨by_, hby⟩ := isFixed_ok hg hy
  unfold consistencyOk
  split
  · exact ⟨false, rfl⟩
  · simp only [Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos hyl]
    split
    · exact ⟨false, rfl⟩
    · refine ⟨(bx || holEl x s.move_related) && (by_ || holEl y s.move_related) && !(bx && by_),
        ?_⟩
      simp only [Translator.Monadic.MonadBase.bind, hbx, hby, moveRelatedSubEqn, if_pos hxm,
        if_pos hym, ret]

/-- Exact HOL `st_ex_FILTER_consistency_ok` (`reg_allocProofScript.sml:2320-2347`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FILTER_consistency_ok"]
theorem stExFilterConsistencyOk :
    ∀ (ls acc : List (Nat × (Nat × Nat))) (s : State),
      goodRaState s ∧ (∀ m ∈ ls, m.2.1 < s.dim ∧ m.2.2 < s.dim) →
      ∃ ts, stExFilter (fun (m : Nat × (Nat × Nat)) => consistencyOk m.2.1 m.2.2) ls acc s =
          (.success ts, s) ∧
        ∀ m ∈ ts, (m.2.1 < s.dim ∧ m.2.2 < s.dim) ∨ m ∈ acc := by
  intro ls
  induction ls with
  | nil => intro acc s _; exact ⟨acc, rfl, fun m hm => Or.inr hm⟩
  | cons m ms ih =>
      intro acc s ⟨hg, hb⟩
      obtain ⟨hx, hy⟩ := hb m List.mem_cons_self
      obtain ⟨b, hrun, _⟩ := consistencyOkSuccess m.2.1 m.2.2 s ⟨hg, hx, hy⟩
      have hms : ∀ m' ∈ ms, m'.2.1 < s.dim ∧ m'.2.2 < s.dim :=
        fun m' hm' => hb m' (List.mem_cons_of_mem _ hm')
      cases b with
      | true =>
          obtain ⟨ts, hts, hmem⟩ := ih (m :: acc) s ⟨hg, hms⟩
          refine ⟨ts, ?_, fun m' hm' => ?_⟩
          · simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun, if_true]
            exact hts
          rcases hmem m' hm' with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl ⟨hx, hy⟩
            · exact Or.inr h
      | false =>
          obtain ⟨ts, hts, hmem⟩ := ih acc s ⟨hg, hms⟩
          refine ⟨ts, ?_, hmem⟩
          simp only [stExFilter, Translator.Monadic.MonadBase.bind, hrun]
          exact hts

/-- `deg_or_inf` reads in-dimension nodes without changing the state. -/
private theorem stExMap_degOrInf {s : State} (hg : goodRaState s) (k : Nat) :
    ∀ (ls : List Nat), (∀ v ∈ ls, v < s.dim) → ∃ ds, stExMap (degOrInf k) ls s = (.success ds, s)
  | [], _ => ⟨[], rfl⟩
  | v :: vs, hb => by
      have hv := hb v List.mem_cons_self
      have hnl : v < s.node_tag.length := by rw [hg.2.1]; exact hv
      have hdl : v < s.degrees.length := by rw [hg.2.2.1]; exact hv
      obtain ⟨ds, hds⟩ := stExMap_degOrInf hg k vs (fun w hw => hb w (List.mem_cons_of_mem _ hw))
      have hd : ∃ d, degOrInf k v s = (.success d, s) := by
        obtain ⟨b, hb⟩ : ∃ b, isFixedK k v s = (.success b, s) := by
          refine ⟨match holEl v s.node_tag with | .Fixed n => decide (n < k) | _ => false, ?_⟩
          simp only [isFixedK, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos hnl, ret]
          rfl
        simp only [degOrInf, Translator.Monadic.MonadBase.bind, hb]
        cases b
        · exact ⟨holEl v s.degrees, by
            simp only [Bool.false_eq_true, ↓reduceIte, degreesSubEqn, if_pos hdl]⟩
        · exact ⟨k, rfl⟩
      obtain ⟨d, hd⟩ := hd
      exact ⟨d :: ds, by simp only [stExMap, Translator.Monadic.MonadBase.bind, hd, hds, ret]⟩

/-- Exact HOL `bg_ok_success` (`reg_allocProofScript.sml:2384-2437`); `s`, `x`, `y` and
`k` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "bg_ok_success"]
theorem bgOkSuccess (s : State) (x y k : Nat) :
    goodRaState s ∧ x < s.dim ∧ y < s.dim →
    ∃ opt, bgOk k x y s = (.success opt, s) ∧
      match opt with
      | none => True
      | some (case1, case2) => (∀ v ∈ case1, v < s.dim) ∧ (∀ v ∈ case2, v < s.dim) := by
  intro ⟨hg, hx, hy⟩
  have hxl : x < s.adj_ls.length := by rw [hg.1]; exact hx
  have hyl : y < s.adj_ls.length := by rw [hg.1]; exact hy
  have hntl : s.node_tag.length = s.dim := hg.2.1
  have hadjx := good_adj hg hx
  have hadjy := good_adj hg hy
  let pr := holPartition (fun v => sortedMem v (holEl x s.adj_ls)) (holEl y s.adj_ls)
  have hpr1 : ∀ v ∈ pr.1, v < s.dim := fun v hv => by
    rcases (mem_holPart _ _ [] [] v).1 hv with hv | hv
    · exact hadjy v hv
    · cases hv
  have hpr2 : ∀ v ∈ pr.2, v < s.dim := fun v hv => by
    rcases (mem_holPart _ _ [] [] v).2 hv with hv | hv
    · exact hadjy v hv
    · cases hv
  obtain ⟨c1, hc1, hc1b⟩ := stExFilterConsideredVar k pr.1 [] s
    ⟨fun v hv => by rw [hntl]; exact hpr1 v hv, fun v hv => by cases hv⟩
  obtain ⟨c2, hc2, hc2b⟩ := stExFilterConsideredVar k pr.2 [] s
    ⟨fun v hv => by rw [hntl]; exact hpr2 v hv, fun v hv => by cases hv⟩
  have hc1d : ∀ v ∈ c1, v < s.dim := fun v hv => by rw [← hntl]; exact hc1b v hv
  have hc2d : ∀ v ∈ c2, v < s.dim := fun v hv => by rw [← hntl]; exact hc2b v hv
  let case3 := (holEl x s.adj_ls).filter (fun v => !sortedMem v (holEl y s.adj_ls))
  obtain ⟨c3, hc3, hc3b⟩ := stExFilterConsideredVar k case3 [] s
    ⟨fun v hv => by rw [hntl]; exact hadjx v (List.mem_filter.mp hv).1, fun v hv => by cases hv⟩
  have hc3d : ∀ v ∈ c3, v < s.dim := fun v hv => by rw [← hntl]; exact hc3b v hv
  obtain ⟨d2, hd2⟩ := stExMap_degOrInf hg k c2 hc2d
  obtain ⟨d1, hd1⟩ := stExMap_degOrInf hg (k + 1) c1 hc1d
  obtain ⟨d3, hd3⟩ := stExMap_degOrInf hg k c3 hc3d
  let opt : Option (List Nat × List Nat) :=
    if (d2.filter (fun x => decide (x ≥ k))).length = 0 then some (c1, c2)
    else if (d1.filter (fun x => decide (x - 1 ≥ k))).length +
        (d2.filter (fun x => decide (x ≥ k))).length +
        (d3.filter (fun x => decide (x ≥ k))).length < k
      then some (c1, c2) else none
  have hopt : opt = none ∨ opt = some (c1, c2) := by
    simp only [opt]; split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
  have hrun : bgOk k x y s = (.success opt, s) := by
    simp only [bgOk, Translator.Monadic.MonadBase.bind, adjLsSubEqn, if_pos hxl, if_pos hyl]
    simp only [pr] at hc1 hc2
    simp only [case3] at hc3
    rw [hc1]
    simp only [hc2, hd2, opt]
    split
    · rfl
    · simp only [Translator.Monadic.MonadBase.bind, hc3, hd1, hd3, ret]
      split <;> rfl
  refine ⟨opt, hrun, ?_⟩
  rcases hopt with h | h <;> rw [h]
  · trivial
  · exact ⟨hc1d, hc2d⟩

/-- Exact HOL `coalesce_parent_success` (`reg_allocProofScript.sml:2439-2482`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "coalesce_parent_success"]
theorem coalesceParentSuccess :
    ∀ (x : Nat) (s : State),
      x < s.dim ∧ goodRaState s →
      ∃ y s' coal, coalesceParent x s = (.success y, s') ∧ y < s.dim ∧ goodRaState s' ∧
        s' = { s with coalesced := coal } := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
  intro s ⟨hx, hg⟩
  have hcl : x < s.coalesced.length := by rw [hg.2.2.2.1]; exact hx
  have hxt : holEl x s.coalesced < s.dim := by
    apply hg.2.2.2.2.2.1
    rw [holEl_eq_getElem _ _ hcl]; exact List.getElem_mem _
  obtain ⟨bx, hbx⟩ := isFixed_ok hg hxt
  rw [coalesceParent]
  simp only [Translator.Monadic.MonadBase.bind, coalescedSubEqn, if_pos hcl, hbx]
  split
  · exact ⟨_, s, s.coalesced, rfl, hxt, hg, rfl⟩
  · split
    · exact ⟨x, s, s.coalesced, rfl, hx, hg, rfl⟩
    · next hlt =>
      obtain ⟨anc, s1, c1, hrun, hanc, hg1, rfl⟩ :=
        ih (holEl x s.coalesced) (by omega) s ⟨hxt, hg⟩
      have hcl1 : x < c1.length := by rw [hg1.2.2.2.1]; exact hx
      refine ⟨anc, { s with coalesced := c1.set x anc }, c1.set x anc, ?_, hanc, ?_, rfl⟩
      · simp only [Translator.Monadic.MonadBase.bind, hrun, ignoreBind, updateCoalescedEqn]
        rw [if_pos hcl1]
        rfl
      · refine good_coalesced (s := { s with coalesced := c1 }) hg1 ?_ ?_
        · rw [List.length_set]; exact hg1.2.2.2.1
        · intro v hv
          rcases List.mem_or_eq_of_mem_set hv with hv | rfl
          · exact hg1.2.2.2.2.2.1 v hv
          · exact hanc

/-- Exact HOL `canonize_move_success` (`reg_allocProofScript.sml:2484-2493`); `x`, `y`
and `s` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "canonize_move_success"]
theorem canonizeMoveSuccess (x y : Nat) (s : State) :
    x < s.dim ∧ y < s.dim ∧ goodRaState s →
    ∃ x2 y2, canonizeMove x y s = (.success (x2, y2), s) ∧ x2 < s.dim ∧ y2 < s.dim := by
  intro ⟨hx, hy, hg⟩
  obtain ⟨bx, hbx⟩ := isFixed_ok hg hx
  obtain ⟨by_, hby⟩ := isFixed_ok hg hy
  simp only [canonizeMove, Translator.Monadic.MonadBase.bind, hbx, hby]
  split
  · exact ⟨y, x, rfl, hy, hx⟩
  · split
    · exact ⟨x, y, rfl, hx, hy⟩
    · split
      · exact ⟨x, y, rfl, hx, hy⟩
      · exact ⟨y, x, rfl, hy, hx⟩

/-- Exact HOL `reset_move_related_success` (`reg_allocProofScript.sml:2658-2682`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "reset_move_related_success"]
theorem resetMoveRelatedSuccess {α : Type} :
    ∀ (ls : List (α × (Nat × Nat))) (s : State),
      goodRaState s ∧ (∀ m ∈ ls, m.2.1 < s.dim ∧ m.2.2 < s.dim) →
      ∃ mv, resetMoveRelated ls s = (.success (), { s with move_related := mv }) ∧
        mv.length = s.dim := by
  intro ls s ⟨hg, hb⟩
  have hml := hg.2.2.2.2.1
  obtain ⟨lss, hrun1, hl1⟩ := stExForeachUpdateMoveRelated (List.range s.dim) s false
    (fun v hv => by rw [hml]; exact List.mem_range.mp hv)
  -- the second traversal only rewrites move-related flags of in-range nodes
  have key : ∀ (l : List (α × (Nat × Nat))) (mv : List Bool),
      (∀ m ∈ l, m.2.1 < s.dim ∧ m.2.2 < s.dim) → mv.length = s.dim →
      ∃ mv', stExForeach l (fun (m : α × (Nat × Nat)) =>
          bind (isFixed m.2.1) fun bx =>
            bind (isFixed m.2.2) fun by_ =>
              ignoreBind (updateMoveRelated m.2.1 (!bx)) (updateMoveRelated m.2.2 (!by_)))
          { s with move_related := mv } =
          (.success (), { s with move_related := mv' }) ∧ mv'.length = s.dim := by
    intro l
    induction l with
    | nil => intro mv _ hl; exact ⟨mv, rfl, hl⟩
    | cons m ms ih =>
        intro mv hb' hl
        obtain ⟨hx, hy⟩ := hb' m List.mem_cons_self
        have hg' : goodRaState { s with move_related := mv } := by
          obtain ⟨h1, h2, h3, h4, _, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hg
          exact ⟨h1, h2, h3, h4, hl, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        obtain ⟨bx, hbx⟩ := isFixed_ok hg' (x := m.2.1) hx
        obtain ⟨by_, hby⟩ := isFixed_ok hg' (x := m.2.2) hy
        have hxl : m.2.1 < mv.length := by rw [hl]; exact hx
        have hyl : m.2.2 < (mv.set m.2.1 (!bx)).length := by rw [List.length_set, hl]; exact hy
        obtain ⟨mv', hrun, hl'⟩ := ih ((mv.set m.2.1 (!bx)).set m.2.2 (!by_))
          (fun m' hm' => hb' m' (List.mem_cons_of_mem _ hm'))
          (by rw [List.length_set, List.length_set, hl])
        refine ⟨mv', ?_, hl'⟩
        simp only [stExForeach, ignoreBind, Translator.Monadic.MonadBase.bind, hbx, hby,
          updateMoveRelatedEqn]
        rw [if_pos hxl]
        simp only
        rw [if_pos hyl]
        exact hrun
  obtain ⟨mv, hrun2, hl2⟩ := key ls lss hb (by rw [hl1, hml])
  refine ⟨mv, ?_, hl2⟩
  simp only [resetMoveRelated, Translator.Monadic.MonadBase.bind, getDim, ignoreBind, hrun1]
  exact hrun2

/-- Exact HOL `st_ex_FIRST_consistency_ok_bg_ok` (`reg_allocProofScript.sml:2495-2547`); `k`
is free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_FIRST_consistency_ok_bg_ok"]
theorem stExFirstConsistencyOkBgOk (k : Nat) :
    ∀ (ls acc : List (Nat × (Nat × Nat))) (s : State),
      goodRaState s ∧ (∀ m ∈ ls, m.2.1 < s.dim ∧ m.2.2 < s.dim) ∧
        (∀ m ∈ acc, m.2.1 < s.dim ∧ m.2.2 < s.dim) →
      ∃ ores ys s' coal,
        stExFirst consistencyOk (bgOk k) ls acc s = (.success (ores, ys), s') ∧
        goodRaState s' ∧ s' = { s with coalesced := coal } ∧
        (∀ m ∈ ys, m.2.1 < s.dim ∧ m.2.2 < s.dim) ∧
        match ores with
        | some ((x, y), (case1, case2), rest) =>
            x < s.dim ∧ y < s.dim ∧ (∀ v ∈ case1, v < s.dim) ∧ (∀ v ∈ case2, v < s.dim) ∧
              (∀ m ∈ rest, m.2.1 < s.dim ∧ m.2.2 < s.dim)
        | _ => True := by
  intro ls
  induction ls with
  | nil =>
      intro acc s ⟨hg, _, hacc⟩
      exact ⟨none, acc, s, s.coalesced, rfl, hg, rfl, hacc, trivial⟩
  | cons m ms ih =>
      intro acc s ⟨hg, hb, hacc⟩
      obtain ⟨p, x, y⟩ := m
      obtain ⟨hx, hy⟩ := hb (p, x, y) List.mem_cons_self
      have hms : ∀ m ∈ ms, m.2.1 < s.dim ∧ m.2.2 < s.dim :=
        fun m hm => hb m (List.mem_cons_of_mem _ hm)
      obtain ⟨x', s1, c1, h1, hx', hg1, rfl⟩ := coalesceParentSuccess x s ⟨hx, hg⟩
      obtain ⟨y', s2, c2, h2, hy', hg2, rfl⟩ :=
        coalesceParentSuccess y { s with coalesced := c1 } ⟨hy, hg1⟩
      have e2 : ({ ({ s with coalesced := c1 } : State) with coalesced := c2 } : State) =
          { s with coalesced := c2 } := rfl
      rw [e2] at h2 hg2
      obtain ⟨b, h3, _⟩ := consistencyOkSuccess x' y' { s with coalesced := c2 } ⟨hg2, hx', hy'⟩
      cases b with
      | false =>
          obtain ⟨ores, ys, s', coal, hrun, hg', rfl, hys, hores⟩ :=
            ih acc { s with coalesced := c2 } ⟨hg2, hms, hacc⟩
          refine ⟨ores, ys, _, coal, ?_, hg', rfl, hys, hores⟩
          simp only [stExFirst, Translator.Monadic.MonadBase.bind, h1, h2, h3,
            Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
          exact hrun
      | true =>
          obtain ⟨x2, y2, h4, hx2, hy2⟩ :=
            canonizeMoveSuccess x' y' { s with coalesced := c2 } ⟨hx', hy', hg2⟩
          obtain ⟨opt, h5, hopt⟩ := bgOkSuccess { s with coalesced := c2 } x2 y2 k ⟨hg2, hx2, hy2⟩
          cases opt with
          | none =>
              have hacc' : ∀ m ∈ (p, (x2, y2)) :: acc, m.2.1 < s.dim ∧ m.2.2 < s.dim := by
                intro m hm
                rcases List.mem_cons.mp hm with rfl | hm
                · exact ⟨hx2, hy2⟩
                · exact hacc m hm
              obtain ⟨ores, ys, s', coal, hrun, hg', rfl, hys, hores⟩ :=
                ih ((p, (x2, y2)) :: acc) { s with coalesced := c2 } ⟨hg2, hms, hacc'⟩
              refine ⟨ores, ys, _, coal, ?_, hg', rfl, hys, hores⟩
              simp only [stExFirst, Translator.Monadic.MonadBase.bind, h1, h2, h3, h4, h5,
                not_true_eq_false, ↓reduceIte]
              exact hrun
          | some pr =>
              obtain ⟨c1', c2'⟩ := pr
              refine ⟨some ((x2, y2), (c1', c2'), ms), acc, _, c2, ?_, hg2, rfl, hacc,
                hx2, hy2, hopt.1, hopt.2, hms⟩
              simp only [stExFirst, Translator.Monadic.MonadBase.bind, h1, h2, h3, h4, h5,
                not_true_eq_false, ↓reduceIte, ret]

private theorem good_degrees' {s : State} {d : List Nat} (h : goodRaState s)
    (hl : d.length = s.degrees.length) : goodRaState { s with degrees := d } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, hl.trans h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

private theorem good_push {s : State} {d : List Nat} {mr : List Bool} {st : List Nat}
    (h : goodRaState s) (hd : d.length = s.degrees.length)
    (hm : mr.length = s.move_related.length) :
    goodRaState { s with degrees := d, move_related := mr, stack := st } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, hd.trans h3, h4, hm.trans h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Exact HOL `do_coalesce_real_success` (`reg_allocProofScript.sml:2549-2604`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "do_coalesce_real_success"]
theorem doCoalesceRealSuccess :
    ∀ (x y : Nat) (case1 case2 : List Nat) (s : State),
      y < s.dim ∧ x < s.dim ∧ (∀ v ∈ case1, v < s.dim) ∧ (∀ v ∈ case2, v < s.dim) ∧
        goodRaState s →
      ∃ s', doCoalesceReal x y case1 case2 s = (.success (), s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro x y case1 case2 s ⟨hy, hx, hc1, hc2, hg⟩
  have hyc : y < s.coalesced.length := by rw [hg.2.2.2.1]; exact hy
  have hg1 : goodRaState { s with coalesced := s.coalesced.set y x } :=
    good_coalesced hg (by rw [List.length_set]; exact hg.2.2.2.1) (fun v hv => by
      rcases List.mem_or_eq_of_mem_set hv with hv | rfl
      · exact hg.2.2.2.2.2.1 v hv
      · exact hx)
  obtain ⟨bx, hbx⟩ := isFixed_ok hg1 hx
  obtain ⟨d2, h2, hg2⟩ : ∃ d2,
      (if bx then ret () else incDeg x case2.length) { s with coalesced := s.coalesced.set y x } =
        (.success (), { s with coalesced := s.coalesced.set y x, degrees := d2 }) ∧
      goodRaState { s with coalesced := s.coalesced.set y x, degrees := d2 } := by
    cases bx with
    | true => exact ⟨s.degrees, rfl, hg1⟩
    | false =>
        have hxd : x < s.degrees.length := by rw [hg.2.2.1]; exact hx
        refine ⟨s.degrees.set x (holEl x s.degrees + case2.length), ?_,
          good_degrees' hg1 (List.length_set ..)⟩
        simp only [Bool.false_eq_true, ↓reduceIte, incDeg, Translator.Monadic.MonadBase.bind,
          degreesSubEqn, updateDegreesEqn, if_pos hxd]
  obtain ⟨s3, h3, hg3, hs3, hedge⟩ :=
    listInsertEdgeSucceeds case2 x { s with coalesced := s.coalesced.set y x, degrees := d2 }
      ⟨hg2, hx, hc2⟩
  have hdim3 : s3.dim = s.dim := by have h := congrArg State.dim hs3; exact h
  have htag3 : s3.node_tag = s.node_tag := by have h := congrArg State.node_tag hs3; exact h
  obtain ⟨d4, h4, hl4⟩ := decDegSuccess case1 s3 ⟨fun v hv => hdim3 ▸ hc1 v hv, hg3⟩
  obtain ⟨d5, mr5, st5, h5, hl5, hm5⟩ := pushStackSuccess [y] { s3 with degrees := d4 }
    ⟨fun v hv => by
      rw [List.mem_singleton.mp hv]; show y < s3.dim; rw [hdim3]; exact hy,
     good_degrees' hg3 hl4⟩
  have hp : pushStack y { s3 with degrees := d4 } =
      (.success (), { s3 with degrees := d5, move_related := mr5, stack := st5 }) := by
    simp only [stExForeach, ignoreBind] at h5
    split at h5
    · next r s5 hps =>
        simp only [ret, Prod.mk.injEq] at h5
        rw [hps, h5.2]
    · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h5
  refine ⟨{ s3 with degrees := d5, move_related := mr5, stack := st5 }, ?_,
    good_push hg3 (hl5.trans hl4) hm5, fun a b h => (hedge a b).2 (Or.inr (Or.inr h)),
    hdim3.symm, htag3.symm⟩
  simp only [doCoalesceReal, ignoreBind, Translator.Monadic.MonadBase.bind, updateCoalescedEqn,
    if_pos hyc, hbx, h2, h3, h4, hp]

private theorem good_wl {s : State} (h : goodRaState s) {sp fr : List Nat}
    {av un : List (Nat × (Nat × Nat))} (hsp : ∀ v ∈ sp, v < s.dim) (hfr : ∀ v ∈ fr, v < s.dim)
    (hav : ∀ m ∈ av, m.2.1 < s.dim ∧ m.2.2 < s.dim)
    (hun : ∀ m ∈ un, m.2.1 < s.dim ∧ m.2.2 < s.dim) :
    goodRaState { s with spill_wl := sp, freeze_wl := fr, avail_moves_wl := av,
                         unavail_moves_wl := un } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, _, _, _, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hsp, hfr, hav, hun, h14⟩

/-- `respill` keeps the graph and the state invariant. -/
private theorem respill_ok (k x : Nat) (s : State) (hg : goodRaState s) (hx : x < s.dim) :
    ∃ s', respill k x s = (.success (), s') ∧ goodRaState s' ∧ s'.adj_ls = s.adj_ls ∧
      s'.dim = s.dim ∧ s'.node_tag = s.node_tag := by
  have hxd : x < s.degrees.length := by rw [hg.2.2.1]; exact hx
  by_cases hlt : holEl x s.degrees < k
  · exact ⟨s, by simp only [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn,
      if_pos hxd, if_pos hlt, ret], hg, rfl, rfl, rfl⟩
  · by_cases hm : x ∈ s.freeze_wl
    · refine ⟨({ s with spill_wl := [x] ++ s.spill_wl,
                         freeze_wl := s.freeze_wl.filter (fun y => decide (y ≠ x)) }),
        ?_, ?_, rfl, rfl, rfl⟩
      · simp only [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn, if_pos hxd,
          if_neg hlt, getFreezeWl, if_pos hm, ignoreBind, addSpillWl, getSpillWl, setSpillWl,
          setFreezeWl]
      · exact good_wl hg
          (fun v hv => by
            rcases List.mem_append.mp hv with hv | hv
            · rw [List.mem_singleton.mp hv]; exact hx
            · exact hg.2.2.2.2.2.2.2.2.2.1 v hv)
          (fun v hv => hg.2.2.2.2.2.2.2.2.2.2.1 v (List.mem_filter.mp hv).1)
          hg.2.2.2.2.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.2.2.1
    · exact ⟨s, by simp only [respill, Translator.Monadic.MonadBase.bind, degreesSubEqn,
        if_pos hxd, if_neg hlt, getFreezeWl, if_neg hm, ret], hg, rfl, rfl, rfl⟩

/-- Exact HOL `do_coalesce_success` (`reg_allocProofScript.sml:2606-2643`); `k` is free in
HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_coalesce_success"]
theorem doCoalesceSuccess (k : Nat) :
    ∀ (s : State),
      goodRaState s →
      ∃ (s' : State) (b : Bool), doCoalesce k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro s hg
  have hav := hg.2.2.2.2.2.2.2.2.2.2.2.1
  have hun := hg.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ores, ys, _, coal, h1, hg1, rfl, hys, hores⟩ :=
    stExFirstConsistencyOkBgOk k s.avail_moves_wl [] s ⟨hg, hav, fun _ h => by cases h⟩
  have hun' : ∀ m ∈ ys ++ s.unavail_moves_wl, m.2.1 < s.dim ∧ m.2.2 < s.dim := fun m hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact hys m hm
    · exact hun m hm
  match ores, hores, h1 with
  | none, _, h1 =>
      refine ⟨({ s with coalesced := coal, unavail_moves_wl := ys ++ s.unavail_moves_wl,
                         avail_moves_wl := [] }), false, ?_,
        good_wl hg1 hg.2.2.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.1 (fun _ h => by cases h) hun',
        isSubgraphRefl _, rfl, rfl⟩
      simp only [doCoalesce, Translator.Monadic.MonadBase.bind, ignoreBind, getAvailMovesWl, h1,
        addUnavailMovesWl, getUnavailMovesWl, setUnavailMovesWl, setAvailMovesWl, ret]
  | some ((x, y), (c1, c2), ms), ⟨hx, hy, hc1, hc2, hms⟩, h1 =>
      have hg3 : goodRaState { s with coalesced := coal,
                                      unavail_moves_wl := ys ++ s.unavail_moves_wl,
                                      avail_moves_wl := ms } :=
        good_wl hg1 hg.2.2.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.2.2.1 hms hun'
      obtain ⟨s4, h4, hg4, hsub4, hdim4, htag4⟩ := doCoalesceRealSuccess x y c1 c2
        { s with coalesced := coal, unavail_moves_wl := ys ++ s.unavail_moves_wl,
                 avail_moves_wl := ms } ⟨hy, hx, hc1, hc2, hg3⟩
      obtain ⟨s5, _, h5, hg5, hsub5, hdim5, htag5⟩ := unspillSuccess (α := Unit) k s4 hg4
      obtain ⟨s6, h6, hg6, hadj6, hdim6, htag6⟩ :=
        respill_ok k x s5 hg5 (by rw [← hdim5, ← hdim4]; exact hx)
      refine ⟨s6, true, ?_, hg6,
        isSubgraphTrans _ _ _ ⟨hsub4, hadj6 ▸ hsub5⟩,
        hdim4.trans (hdim5.trans hdim6.symm), htag4.trans (htag5.trans htag6.symm)⟩
      simp only [doCoalesce, Translator.Monadic.MonadBase.bind, ignoreBind, getAvailMovesWl, h1,
        addUnavailMovesWl, getUnavailMovesWl, setUnavailMovesWl, setAvailMovesWl]
      rw [h4]
      simp only [h5, h6, ret]

/-- Exact HOL `do_prefreeze_success` (`reg_allocProofScript.sml:2684-2725`); `k` is free in
HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_prefreeze_success"]
theorem doPrefreezeSuccess (k : Nat) :
    ∀ (s : State),
      goodRaState s →
      ∃ (s' : State) (b : Bool), doPrefreeze k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro s hg
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
  obtain ⟨fwl, hf1, hfb⟩ := stExFilterIsNotCoalesced s.freeze_wl [] s
    ⟨fun x hx => by rw [g4]; exact g11 x hx, fun _ h => by cases h⟩
  obtain ⟨swl, hs1, hsb⟩ := stExFilterIsNotCoalesced s.spill_wl [] s
    ⟨fun x hx => by rw [g4]; exact g10 x hx, fun _ h => by cases h⟩
  have hfd : ∀ x ∈ fwl, x < s.dim := fun x hx => by rw [← g4]; exact hfb x hx
  have hg1 : goodRaState { s with spill_wl := swl } :=
    ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, fun v hv => by rw [← g4]; exact hsb v hv, g11, g12, g13,
      g14⟩
  obtain ⟨uam, hu1, hub⟩ :=
    stExFilterConsistencyOk s.unavail_moves_wl [] { s with spill_wl := swl } ⟨hg1, g13⟩
  have hub' : ∀ m ∈ uam, m.2.1 < s.dim ∧ m.2.2 < s.dim := fun m hm =>
    (hub m hm).resolve_right (fun h => by cases h)
  obtain ⟨mv, hr1, hmv⟩ := resetMoveRelatedSuccess uam { s with spill_wl := swl } ⟨hg1, hub'⟩
  obtain ⟨ltkf, ltks, hp1, hpf, hps⟩ := stExPartitionMoveRelatedSub fwl [] []
    { s with spill_wl := swl, move_related := mv, unavail_moves_wl := uam }
    (fun x hx => by show x < mv.length; rw [hmv]; exact hfd x hx)
  have hg5 : goodRaState { s with spill_wl := swl, move_related := mv, unavail_moves_wl := uam,
                                  simp_wl := ltks ++ s.simp_wl, freeze_wl := ltkf } :=
    ⟨g1, g2, g3, g4, hmv, g6, g7, g8,
      fun v hv => by
        rcases List.mem_append.mp hv with hv | hv
        · rcases hps v hv with hv | hv
          · cases hv
          · exact hfd v hv
        · exact g9 v hv,
      fun v hv => by rw [← g4]; exact hsb v hv,
      fun v hv => by
        rcases hpf v hv with hv | hv
        · cases hv
        · exact hfd v hv,
      g12, hub', g14⟩
  obtain ⟨s', b, h6, hg6, hsub6, hd6, ht6⟩ := doSimplifySuccess k _ hg5
  refine ⟨s', b, ?_, hg6, hsub6, hd6, ht6⟩
  simp only [doPrefreeze, Translator.Monadic.MonadBase.bind, ignoreBind, getFreezeWl, hf1,
    getSpillWl, hs1, setSpillWl, getUnavailMovesWl, hu1, hr1, setUnavailMovesWl, hp1, addSimpWl,
    getSimpWl, setSimpWl, setFreezeWl, h6]

end Flapjack.RegAlloc
