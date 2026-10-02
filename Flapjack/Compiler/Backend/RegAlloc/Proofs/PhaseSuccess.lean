import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Allocator
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
import Flapjack.Compiler.Backend.RegAlloc.Proofs.Invariants
import Flapjack.Compiler.Backend.RegAlloc.Proofs.MoveRelatedPartition
import Flapjack.Basis.Pure.MlList.SortPerm

/-!
# reg_allocProof: success of the simplify phase

Ports of `reg_allocProofScript.sml:2075-2300`: on a `good_ra_state` the
worklist operations of the simplify phase succeed and preserve the state
invariant. HOL `EVERY P l` is `∀ x ∈ l, P x`, `MEM` is list membership, HOL
`EL` the exact `holEl`, record updates are Lean structure updates, and an
unused existential of polymorphic type keeps that type, with `[Nonempty α]`
recording that HOL types are inhabited.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-! ### State-invariant bookkeeping (Flapjack infrastructure) -/

private theorem good_degrees {s : State} {d : List Nat} (h : goodRaState s)
    (hl : d.length = s.degrees.length) : goodRaState { s with degrees := d } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, hl.trans h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

private theorem good_stack_mr {s : State} {d : List Nat} {mr : List Bool} {st : List Nat}
    (h : goodRaState s) (hd : d.length = s.degrees.length)
    (hm : mr.length = s.move_related.length) :
    goodRaState { s with degrees := d, move_related := mr, stack := st } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, hd.trans h3, h4, hm.trans h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

private theorem good_dim_lt {s : State} (h : goodRaState s) :
    s.adj_ls.length = s.dim ∧ s.degrees.length = s.dim ∧ s.coalesced.length = s.dim ∧
      s.move_related.length = s.dim := ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Flapjack infrastructure: adjacency entries of a `good_ra_state` are in range. -/
theorem good_adj {s : State} (h : goodRaState s) {n : Nat} (hn : n < s.dim) :
    ∀ v ∈ holEl n s.adj_ls, v < s.dim := by
  have hl := h.1
  have hmem : holEl n s.adj_ls ∈ s.adj_ls := by
    rw [holEl_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  exact h.2.2.2.2.2.2.1 _ hmem

/-! ### Ports -/

/-- Exact HOL `is_not_coalesced_succeeds` (`reg_allocProofScript.sml:2075-2081`);
`s` and `n` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "is_not_coalesced_succeeds"]
theorem isNotCoalescedSucceeds (s : State) (n : Nat) :
    goodRaState s ∧ n < s.dim → ∃ b, isNotCoalesced n s = (.success b, s) := by
  intro ⟨hg, hn⟩
  have hc : n < s.coalesced.length := by rw [(good_dim_lt hg).2.2.1]; exact hn
  exact ⟨decide (n = holEl n s.coalesced), by
    simp only [isNotCoalesced, Translator.Monadic.MonadBase.bind, coalescedSubEqn, if_pos hc, ret]⟩

private theorem splitDegree_succeeds (s : State) (k v : Nat) (hg : goodRaState s) :
    ∃ c, splitDegree s.dim k v s = (.success c, s) := by
  unfold splitDegree
  by_cases hv : v < s.dim
  · rw [if_pos hv]
    have hd : v < s.degrees.length := by rw [(good_dim_lt hg).2.1]; exact hv
    obtain ⟨b, hb⟩ := isNotCoalescedSucceeds s v ⟨hg, hv⟩
    exact ⟨decide (holEl v s.degrees < k) && b, by
      simp only [Translator.Monadic.MonadBase.bind, degreesSubEqn, if_pos hd, hb, ret]⟩
  · rw [if_neg hv]; exact ⟨true, rfl⟩

/-- Exact HOL `st_ex_PARTITION_split_degree` (`reg_allocProofScript.sml:2085-2116`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_PARTITION_split_degree"]
theorem stExPartitionSplitDegree :
    ∀ (atemps : List Nat) (k : Nat) (lss lss' : List Nat) (s : State),
      goodRaState s →
      ∃ ts fs, stExPartition (splitDegree s.dim k) atemps lss lss' s = (.success (ts, fs), s) ∧
        (∀ x ∈ ts, x ∈ lss ∨ x ∈ atemps) ∧ (∀ x ∈ fs, x ∈ lss' ∨ x ∈ atemps) := by
  intro atemps k
  induction atemps with
  | nil =>
      intro lss lss' s _
      exact ⟨lss, lss', rfl, fun x hx => Or.inl hx, fun x hx => Or.inl hx⟩
  | cons h t ih =>
      intro lss lss' s hg
      obtain ⟨c, hc⟩ := splitDegree_succeeds s k h hg
      cases c with
      | true =>
          obtain ⟨ts, fs, heq, hts, hfs⟩ := ih (h :: lss) lss' s hg
          refine ⟨ts, fs, by simp only [stExPartition, Translator.Monadic.MonadBase.bind, hc, if_true]; exact heq, ?_, ?_⟩
          · intro x hx
            rcases hts x hx with hx | hx
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr List.mem_cons_self
              · exact Or.inl hx
            · exact Or.inr (List.mem_cons_of_mem _ hx)
          · intro x hx
            rcases hfs x hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (List.mem_cons_of_mem _ hx)
      | false =>
          obtain ⟨ts, fs, heq, hts, hfs⟩ := ih lss (h :: lss') s hg
          refine ⟨ts, fs, by simp only [stExPartition, Translator.Monadic.MonadBase.bind, hc]; exact heq, ?_, ?_⟩
          · intro x hx
            rcases hts x hx with hx | hx
            · exact Or.inl hx
            · exact Or.inr (List.mem_cons_of_mem _ hx)
          · intro x hx
            rcases hfs x hx with hx | hx
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact Or.inr List.mem_cons_self
              · exact Or.inl hx
            · exact Or.inr (List.mem_cons_of_mem _ hx)

/-- Exact HOL `dec_deg_success` (`reg_allocProofScript.sml:2139-2152`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "dec_deg_success"]
theorem decDegSuccess :
    ∀ (ls : List Nat) (s : State),
      (∀ v ∈ ls, v < s.dim) ∧ goodRaState s →
      ∃ d, stExForeach ls decDeg s = (.success (), { s with degrees := d }) ∧
        d.length = s.degrees.length := by
  intro ls
  induction ls with
  | nil => intro s _; exact ⟨s.degrees, rfl, rfl⟩
  | cons h t ih =>
      intro s ⟨hb, hg⟩
      have hh : h < s.degrees.length := by
        rw [(good_dim_lt hg).2.1]; exact hb h List.mem_cons_self
      let s1 : State := { s with degrees := s.degrees.set h (holEl h s.degrees - 1) }
      have hs1 : decDeg h s = (.success (), s1) := by
        simp only [decDeg, Translator.Monadic.MonadBase.bind, degreesSubEqn, if_pos hh, updateDegreesEqn]; rfl
      obtain ⟨d, hrun, hl⟩ := ih s1 ⟨fun v hv => hb v (List.mem_cons_of_mem _ hv),
        good_degrees hg List.length_set⟩
      refine ⟨d, ?_, by rw [hl]; exact List.length_set⟩
      simp only [stExForeach, ignoreBind, hs1]
      exact hrun

/-- Exact HOL `dec_degree_success` (`reg_allocProofScript.sml:2154-2173`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "dec_degree_success"]
theorem decDegreeSuccess :
    ∀ (ls : List Nat) (s : State),
      goodRaState s →
      ∃ d, stExForeach ls decDegree s = (.success (), { s with degrees := d }) ∧
        d.length = s.degrees.length := by
  intro ls
  induction ls with
  | nil => intro s _; exact ⟨s.degrees, rfl, rfl⟩
  | cons h t ih =>
      intro s hg
      by_cases hh : h < s.dim
      · have ha : h < s.adj_ls.length := by rw [(good_dim_lt hg).1]; exact hh
        obtain ⟨d1, hrun1, hl1⟩ := decDegSuccess (holEl h s.adj_ls) s ⟨good_adj hg hh, hg⟩
        have hs1 : decDegree h s = (.success (), { s with degrees := d1 }) := by
          simp only [decDegree, Translator.Monadic.MonadBase.bind, getDim, if_pos hh, adjLsSubEqn, if_pos ha]
          exact hrun1
        obtain ⟨d, hrun, hl⟩ := ih { s with degrees := d1 } (good_degrees hg hl1)
        refine ⟨d, ?_, by rw [hl]; exact hl1⟩
        simp only [stExForeach, ignoreBind, hs1]
        exact hrun
      · have hs1 : decDegree h s = (.success (), s) := by
          simp only [decDegree, Translator.Monadic.MonadBase.bind, getDim, if_neg hh, ret]
        obtain ⟨d, hrun, hl⟩ := ih s hg
        refine ⟨d, ?_, hl⟩
        simp only [stExForeach, ignoreBind, hs1]
        exact hrun

/-- Membership of a HOL `PARTITION` bucket. -/
theorem mem_holPart {α : Type} (P : α → Bool) :
    ∀ (l l1 l2 : List α) (x : α),
      (x ∈ (holPart P l l1 l2).1 → x ∈ l ∨ x ∈ l1) ∧ (x ∈ (holPart P l l1 l2).2 → x ∈ l ∨ x ∈ l2)
  | [], l1, l2, x => ⟨Or.inr, Or.inr⟩
  | h :: t, l1, l2, x => by
      simp only [holPart]
      split
      · obtain ⟨a, b⟩ := mem_holPart P t (h :: l1) l2 x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases a hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem _ hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inl List.mem_cons_self
            · exact Or.inr hx
        · rcases b hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem _ hx)
          · exact Or.inr hx
      · obtain ⟨a, b⟩ := mem_holPart P t l1 (h :: l2) x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · rcases a hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem _ hx)
          · exact Or.inr hx
        · rcases b hx with hx | hx
          · exact Or.inl (List.mem_cons_of_mem _ hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inl List.mem_cons_self
            · exact Or.inr hx

/-- Exact HOL `revive_moves_success` (`reg_allocProofScript.sml:2184-2204`); `s` and
`ls` are free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "revive_moves_success"]
theorem reviveMovesSuccess (s : State) (ls : List Nat) :
    (∀ x ∈ ls, x < s.adj_ls.length) →
    ∃ s', reviveMoves ls s = (.success (), s') ∧
      s' = { s with avail_moves_wl := s'.avail_moves_wl,
                    unavail_moves_wl := s'.unavail_moves_wl } ∧
      (∀ x ∈ s'.avail_moves_wl, x ∈ s.avail_moves_wl ++ s.unavail_moves_wl) ∧
      (∀ x ∈ s'.unavail_moves_wl, x ∈ s.avail_moves_wl ++ s.unavail_moves_wl) := by
  intro hb
  have hmap := stExMapAdjLsSub ls s hb
  let P := fun (m : Nat × (Nat × Nat)) =>
    (ls.map fun i => holEl i s.adj_ls).any (fun l => sortedMem m.2.1 l) ||
      (ls.map fun i => holEl i s.adj_ls).any (fun l => sortedMem m.2.2 l)
  let pr := holPartition P s.unavail_moves_wl
  let s' : State := { s with
    avail_moves_wl := smerge (sortMoves pr.1) s.avail_moves_wl
    unavail_moves_wl := pr.2 }
  refine ⟨s', ?_, rfl, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [reviveMoves, Translator.Monadic.MonadBase.bind, hmap, getUnavailMovesWl, getAvailMovesWl, ignoreBind,
      setAvailMovesWl, setUnavailMovesWl]
    rfl
  · rcases (memSmerge x _ _).mp hx with hx | hx
    · have hx' := (Basis.Pure.MlList.sortMem x _ _).mp hx
      rcases (mem_holPart P s.unavail_moves_wl [] [] x).1 hx' with hx | hx
      · exact List.mem_append_right _ hx
      · cases hx
    · exact List.mem_append_left _ hx
  · rcases (mem_holPart P s.unavail_moves_wl [] [] x).2 hx with hx | hx
    · exact List.mem_append_right _ hx
    · cases hx

/-- Exact HOL `unspill_success` (`reg_allocProofScript.sml:2206-2237`); the unused
existential `b` keeps its polymorphic HOL type. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "unspill_success"]
theorem unspillSuccess {α : Type} [Nonempty α] :
    ∀ (k : Nat) (s : State),
      goodRaState s →
      ∃ (s' : State) (_b : α), unspill k s = (.success (), s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro k s hg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hg
  obtain ⟨ltk, gtk, hpart, hltk, hgtk⟩ :=
    stExPartitionSplitDegree s.spill_wl k [] [] s ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have hltkb : ∀ x ∈ ltk, x < s.dim := fun x hx => by
    rcases hltk x hx with hx | hx
    · cases hx
    · exact h10 x hx
  have hgtkb : ∀ x ∈ gtk, x < s.dim := fun x hx => by
    rcases hgtk x hx with hx | hx
    · cases hx
    · exact h10 x hx
  obtain ⟨s1, hrev, hs1, hav, hun⟩ := reviveMovesSuccess s ltk (fun x hx => by rw [h1]; exact hltkb x hx)
  obtain ⟨A, U, rfl⟩ : ∃ A U, s1 = { s with avail_moves_wl := A, unavail_moves_wl := U } :=
    ⟨_, _, hs1⟩
  let s1 : State := { s with avail_moves_wl := A, unavail_moves_wl := U }
  have hmr : ∀ x ∈ ltk, x < s1.move_related.length := fun x hx => by
    show x < s.move_related.length
    rw [h5]; exact hltkb x hx
  obtain ⟨lf, ls, hpart2, hlf, hls⟩ := stExPartitionMoveRelatedSub ltk [] [] s1 hmr
  have hlfb : ∀ x ∈ lf, x < s.dim := fun x hx => by
    rcases hlf x hx with hx | hx
    · cases hx
    · exact hltkb x hx
  have hlsb : ∀ x ∈ ls, x < s.dim := fun x hx => by
    rcases hls x hx with hx | hx
    · cases hx
    · exact hltkb x hx
  have hmoveb : ∀ m ∈ s.avail_moves_wl ++ s.unavail_moves_wl, m.2.1 < s.dim ∧ m.2.2 < s.dim :=
    fun m hm => by
      rcases List.mem_append.mp hm with hm | hm
      · exact h12 m hm
      · exact h13 m hm
  let s' : State := { s1 with
    spill_wl := gtk, simp_wl := ls ++ s1.simp_wl, freeze_wl := lf ++ s1.freeze_wl }
  refine ⟨s', Classical.ofNonempty, ?_, ?_, ?_, ?_, ?_⟩
  · have hp2 : stExPartition moveRelatedSub ltk [] []
        { s with avail_moves_wl := A, unavail_moves_wl := U } = (.success (lf, ls), s1) := hpart2
    simp only [unspill, Translator.Monadic.MonadBase.bind, getDim, getSpillWl, hpart, ignoreBind,
      hrev, hp2, setSpillWl, addSimpWl, getSimpWl, setSimpWl, addFreezeWl, getFreezeWl,
      setFreezeWl]
    rfl
  · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
      fun v hv => by
        rcases List.mem_append.mp hv with hv | hv
        · exact hlsb v hv
        · exact h9 v hv,
      hgtkb,
      fun v hv => by
        rcases List.mem_append.mp hv with hv | hv
        · exact hlfb v hv
        · exact h11 v hv,
      fun m hm => hmoveb m (hav m hm), fun m hm => hmoveb m (hun m hm), h14⟩
  · exact isSubgraphRefl _
  · rfl
  · rfl

/-- Exact HOL `push_stack_success` (`reg_allocProofScript.sml:2239-2260`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "push_stack_success"]
theorem pushStackSuccess :
    ∀ (ls : List Nat) (s : State),
      (∀ x ∈ ls, x < s.dim) ∧ goodRaState s →
      ∃ d mr st, stExForeach ls pushStack s =
          (.success (), { s with degrees := d, move_related := mr, stack := st }) ∧
        d.length = s.degrees.length ∧ mr.length = s.move_related.length := by
  intro ls
  induction ls with
  | nil => intro s _; exact ⟨s.degrees, s.move_related, s.stack, rfl, rfl, rfl⟩
  | cons h t ih =>
      intro s ⟨hb, hg⟩
      have hd : h < s.degrees.length := by
        rw [(good_dim_lt hg).2.1]; exact hb h List.mem_cons_self
      have hm : h < s.move_related.length := by
        rw [(good_dim_lt hg).2.2.2]; exact hb h List.mem_cons_self
      let s1 : State := { s with
        degrees := s.degrees.set h 0
        move_related := s.move_related.set h false
        stack := h :: s.stack }
      have hs1 : pushStack h s = (.success (), s1) := by
        simp only [pushStack, Translator.Monadic.MonadBase.bind, getStack, ignoreBind,
          updateDegreesEqn, if_pos hd, updateMoveRelatedEqn, if_pos hm,
          setStack]
        rfl
      obtain ⟨d, mr, st, hrun, hdl, hml⟩ :=
        ih s1 ⟨fun v hv => hb v (List.mem_cons_of_mem _ hv),
          good_stack_mr hg List.length_set List.length_set⟩
      refine ⟨d, mr, st, ?_, by rw [hdl]; exact List.length_set,
        by rw [hml]; exact List.length_set⟩
      simp only [stExForeach, ignoreBind, hs1]
      exact hrun

/-- Exact HOL `do_simplify_success` (`reg_allocProofScript.sml:2262-2283`); `k` is free
in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_simplify_success"]
theorem doSimplifySuccess (k : Nat) :
    ∀ (s : State),
      goodRaState s →
      ∃ (s' : State) (b : Bool), doSimplify k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro s hg
  by_cases he : s.simp_wl = []
  · exact ⟨s, false, by simp only [doSimplify, Translator.Monadic.MonadBase.bind, getSimpWl,
      if_pos he, ret], hg, isSubgraphRefl _, rfl, rfl⟩
  obtain ⟨d, hrun1, hl1⟩ := decDegreeSuccess s.simp_wl s hg
  have hg1 := good_degrees hg hl1
  obtain ⟨d2, mr, st, hrun2, hl2, hm2⟩ :=
    pushStackSuccess s.simp_wl { s with degrees := d } ⟨hg.2.2.2.2.2.2.2.2.1, hg1⟩
  have hg2 : goodRaState { s with degrees := d2, move_related := mr, stack := st } :=
    good_stack_mr (s := { s with degrees := d }) hg1 hl2 hm2
  let s2 : State := { s with degrees := d2, move_related := mr, stack := st, simp_wl := [] }
  have hg3 : goodRaState s2 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11, h12, h13, h14⟩ := hg2
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, h10, h11, h12, h13, h14⟩
    intro v hv
    exact absurd hv List.not_mem_nil
  obtain ⟨s', _, hrun3, hg', hsub, hdim, htag⟩ := unspillSuccess (α := Unit) k s2 hg3
  refine ⟨s', true, ?_, hg', hsub, hdim, htag⟩
  simp only [doSimplify, Translator.Monadic.MonadBase.bind, getSimpWl, if_neg he, ignoreBind,
    hrun1, hrun2, setSimpWl]
  have h3' : unspill k { s with degrees := d2, move_related := mr, stack := st, simp_wl := [] } =
      (.success (), s') := hrun3
  rw [h3']
  rfl

end Flapjack.RegAlloc
