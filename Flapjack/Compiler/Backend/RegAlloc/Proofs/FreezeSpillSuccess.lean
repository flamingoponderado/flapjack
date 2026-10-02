import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Proofs.CoalesceSuccess

/-!
# reg_allocProof: success of the freeze and spill phases

Ports of `reg_allocProofScript.sml:2727-2837`: on a `good_ra_state` the freeze step, the
spill-candidate searches and the spill step succeed and preserve the state invariant, the
graph, the dimension and the node tags. Renderings as in `PhaseSuccess`.
-/

namespace Flapjack.RegAlloc

open Flapjack Flapjack.Translator.Monadic.MonadBase

/-- A singleton `st_ex_FOREACH` is the action itself (Flapjack infrastructure). -/
private theorem foreach_single {f : Nat → M State Unit StateException} {x : Nat}
    {s s' : State} (h : stExForeach [x] f s = (.success (), s')) : f x s = (.success (), s') := by
  simp only [stExForeach, ignoreBind] at h
  split at h
  · next r s5 hps =>
      simp only [ret, Prod.mk.injEq] at h
      rw [hps, h.2]
  · simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

/-- Decrement and push one in-range node, as `do_freeze` and `do_spill` do. -/
private theorem dec_push_ok (x : Nat) (s : State) (hg : goodRaState s) (hx : x < s.dim) :
    ∃ s1 s', decDegree x s = (.success (), s1) ∧ pushStack x s1 = (.success (), s') ∧
      goodRaState s' ∧ s'.adj_ls = s.adj_ls ∧ s'.dim = s.dim ∧ s'.node_tag = s.node_tag ∧
      s'.spill_wl = s.spill_wl ∧ s'.freeze_wl = s.freeze_wl := by
  obtain ⟨d, h1, hl1⟩ := decDegreeSuccess [x] s hg
  have hg1 : goodRaState { s with degrees := d } := by
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
    exact ⟨g1, g2, hl1.trans g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
  obtain ⟨d', mr, st, h2, hl2, hm2⟩ := pushStackSuccess [x] { s with degrees := d }
    ⟨fun v hv => by rw [List.mem_singleton.mp hv]; exact hx, hg1⟩
  refine ⟨_, { s with degrees := d', move_related := mr, stack := st }, foreach_single h1,
    foreach_single h2, ?_, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
  exact ⟨g1, g2, (hl2.trans hl1).trans g3, g4, hm2.trans g5, g6, g7, g8, g9, g10, g11, g12,
    g13, g14⟩

/-- Exact HOL `do_freeze_success` (`reg_allocProofScript.sml:2727-2755`); `k` is free in
HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_freeze_success"]
theorem doFreezeSuccess (k : Nat) :
    ∀ (s : State),
      goodRaState s →
      ∃ (s' : State) (b : Bool), doFreeze k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro s hg
  have hfr := hg.2.2.2.2.2.2.2.2.2.2.1
  match hf : s.freeze_wl with
  | [] =>
      exact ⟨s, false, by simp only [doFreeze, Translator.Monadic.MonadBase.bind, getFreezeWl, hf,
        ret], hg, isSubgraphRefl _, rfl, rfl⟩
  | x :: xs =>
      have hx : x < s.dim := hfr x (by rw [hf]; exact List.mem_cons_self)
      obtain ⟨s1, s2, h1, h2, hg2, ha2, hd2, ht2, _, _⟩ := dec_push_ok x s hg hx
      have hg3 : goodRaState { s2 with freeze_wl := xs } := by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, _, g12, g13, g14⟩ := hg2
        exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, fun v hv => by
          rw [hd2]; exact hfr v (by rw [hf]; exact List.mem_cons_of_mem _ hv), g12, g13, g14⟩
      obtain ⟨s4, _, h4, hg4, hsub4, hd4, ht4⟩ := unspillSuccess (α := Unit) k _ hg3
      refine ⟨s4, true, ?_, hg4, fun a b h => hsub4 a b (ha2 ▸ h), hd2.symm.trans hd4,
        ht2.symm.trans ht4⟩
      simp only [doFreeze, Translator.Monadic.MonadBase.bind, getFreezeWl, hf, ignoreBind, h1, h2,
        setFreezeWl, h4, ret]

/-- Exact HOL `st_ex_list_MIN_cost_success` (`reg_allocProofScript.sml:2758-2772`); `scost` is
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_list_MIN_cost_success"]
theorem stExListMinCostSuccess (scost : Spt Nat) :
    ∀ (ls : List Nat) (s : State) (k v : Nat) (acc : List Nat),
      goodRaState s ∧ (∀ v ∈ acc, v < s.dim) ∧ k < s.dim →
      ∃ x y, stExListMinCost scost ls s.dim k v acc s = (.success (x, y), s) ∧ x < s.dim ∧
        ∀ v ∈ y, v < s.dim := by
  intro ls
  induction ls with
  | nil => intro s k v acc ⟨_, hacc, hk⟩; exact ⟨k, acc, rfl, hk, hacc⟩
  | cons x xs ih =>
      intro s k v acc ⟨hg, hacc, hk⟩
      by_cases hx : x < s.dim
      · have hxd : x < s.degrees.length := by rw [hg.2.2.1]; exact hx
        by_cases hc : v > safeDiv (lookupAny x scost 0) (holEl x s.degrees)
        · obtain ⟨a, b, hr, ha, hb⟩ := ih s x (safeDiv (lookupAny x scost 0) (holEl x s.degrees))
            (k :: acc) ⟨hg, fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hk
              · exact hacc w hw, hx⟩
          exact ⟨a, b, by simp only [stExListMinCost, if_pos hx, Translator.Monadic.MonadBase.bind,
            degreesSubEqn, if_pos hxd, ret, if_pos hc, hr], ha, hb⟩
        · obtain ⟨a, b, hr, ha, hb⟩ := ih s k v (x :: acc) ⟨hg, fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hx
              · exact hacc w hw, hk⟩
          exact ⟨a, b, by simp only [stExListMinCost, if_pos hx, Translator.Monadic.MonadBase.bind,
            degreesSubEqn, if_pos hxd, ret, if_neg hc, hr], ha, hb⟩
      · obtain ⟨a, b, hr, ha, hb⟩ := ih s k v acc ⟨hg, hacc, hk⟩
        exact ⟨a, b, by simp only [stExListMinCost, if_neg hx, hr], ha, hb⟩

/-- Exact HOL `st_ex_list_MAX_deg_success` (`reg_allocProofScript.sml:2774-2788`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "st_ex_list_MAX_deg_success"]
theorem stExListMaxDegSuccess :
    ∀ (ls : List Nat) (s : State) (k v : Nat) (acc : List Nat),
      goodRaState s ∧ (∀ v ∈ acc, v < s.dim) ∧ k < s.dim →
      ∃ x y, stExListMaxDeg ls s.dim k v acc s = (.success (x, y), s) ∧ x < s.dim ∧
        ∀ v ∈ y, v < s.dim := by
  intro ls
  induction ls with
  | nil => intro s k v acc ⟨_, hacc, hk⟩; exact ⟨k, acc, rfl, hk, hacc⟩
  | cons x xs ih =>
      intro s k v acc ⟨hg, hacc, hk⟩
      by_cases hx : x < s.dim
      · have hxd : x < s.degrees.length := by rw [hg.2.2.1]; exact hx
        by_cases hc : v < holEl x s.degrees
        · obtain ⟨a, b, hr, ha, hb⟩ := ih s x (holEl x s.degrees) (k :: acc) ⟨hg, fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hk
              · exact hacc w hw, hx⟩
          exact ⟨a, b, by simp only [stExListMaxDeg, if_pos hx, Translator.Monadic.MonadBase.bind,
            degreesSubEqn, if_pos hxd, if_pos hc, hr], ha, hb⟩
        · obtain ⟨a, b, hr, ha, hb⟩ := ih s k v (x :: acc) ⟨hg, fun w hw => by
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hx
              · exact hacc w hw, hk⟩
          exact ⟨a, b, by simp only [stExListMaxDeg, if_pos hx, Translator.Monadic.MonadBase.bind,
            degreesSubEqn, if_pos hxd, if_neg hc, hr], ha, hb⟩
      · obtain ⟨a, b, hr, ha, hb⟩ := ih s k v acc ⟨hg, hacc, hk⟩
        exact ⟨a, b, by simp only [stExListMaxDeg, if_neg hx, hr], ha, hb⟩

/-- Exact HOL `do_spill_success` (`reg_allocProofScript.sml:2790-2837`); `scost` and `k` are
free in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "do_spill_success"]
theorem doSpillSuccess (scost : Option (Spt Nat)) (k : Nat) :
    ∀ (s : State),
      goodRaState s →
      ∃ (s' : State) (b : Bool), doSpill scost k s = (.success b, s') ∧ goodRaState s' ∧
        isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag := by
  intro s hg
  have hsp := hg.2.2.2.2.2.2.2.2.2.1
  match hf : s.spill_wl with
  | [] =>
      exact ⟨s, false, by simp only [doSpill, Translator.Monadic.MonadBase.bind, getSpillWl,
        getDim, hf, ret], hg, isSubgraphRefl _, rfl, rfl⟩
  | x :: xs =>
      have hx : x < s.dim := hsp x (by rw [hf]; exact List.mem_cons_self)
      have hxd : x < s.degrees.length := by rw [hg.2.2.1]; exact hx
      suffices H : ∀ y ys, y < s.dim → (∀ v ∈ ys, v < s.dim) →
          ∃ s', ignoreBind (decDegree y) (ignoreBind (pushStack y)
              (ignoreBind (setSpillWl ys) (ignoreBind (unspill k) (ret true)))) s =
              (.success true, s') ∧ goodRaState s' ∧
            isSubgraph s.adj_ls s'.adj_ls ∧ s.dim = s'.dim ∧ s.node_tag = s'.node_tag by
        cases scost with
        | none =>
            obtain ⟨y, ys, hc, hy, hys⟩ :=
              stExListMaxDegSuccess xs s x (holEl x s.degrees) [] ⟨hg, (fun _ h => by cases h), hx⟩
            obtain ⟨s', hr, hrest⟩ := H y ys hy hys
            refine ⟨s', true, ?_, hrest⟩
            simp only [doSpill, Translator.Monadic.MonadBase.bind, getSpillWl, getDim, hf,
              degreesSubEqn, if_pos hxd, hc]
            exact hr
        | some sc =>
            obtain ⟨y, ys, hc, hy, hys⟩ :=
              stExListMinCostSuccess sc xs s x
                (safeDiv (lookupAny x sc 0) (holEl x s.degrees)) []
                ⟨hg, (fun _ h => by cases h), hx⟩
            obtain ⟨s', hr, hrest⟩ := H y ys hy hys
            refine ⟨s', true, ?_, hrest⟩
            simp only [doSpill, Translator.Monadic.MonadBase.bind, getSpillWl, getDim, hf,
              degreesSubEqn, if_pos hxd, hc]
            exact hr
      intro y ys hy hys
      obtain ⟨s1, s2, h1, h2, hg2, ha2, hd2, ht2, _, _⟩ := dec_push_ok y s hg hy
      have hg3 : goodRaState { s2 with spill_wl := ys } := by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, _, g11, g12, g13, g14⟩ := hg2
        exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, fun v hv => by rw [hd2]; exact hys v hv, g11,
          g12, g13, g14⟩
      obtain ⟨s4, _, h4, hg4, hsub4, hd4, ht4⟩ := unspillSuccess (α := Unit) k _ hg3
      refine ⟨s4, ?_, hg4, fun a b h => hsub4 a b (ha2 ▸ h), hd2.symm.trans hd4,
        ht2.symm.trans ht4⟩
      simp only [ignoreBind, h1, h2, setSpillWl, h4, ret]

end Flapjack.RegAlloc
