import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.PanCommon
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# `eval_distinct_lists_not_affect` family over the exact Crep evaluator

Exact ports of HOL `eval_distinct_lists_not_affect'`,
`opt_mmap_eval_distinct_lists_not_affect`, `eval_distinct_lists_not_affect`, and
`opt_mmap_eval_distinct_lists_not_affect'`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3057-3093, 4111-4137`):
Crep expressions whose `var_cexp` avoid `vs` evaluate the same after
`s.locals |++ ZIP (vs, nvals)`. `eval` is the tagged `evalCrepSemHOLExp`,
`var_cexp` is `crepExpVarsHOL`, `distinct_lists` is `distinctListsHol`,
`|++ ZIP` is `updateListEq (zip)`, and `OPT_MMAP` is `List.mapM`. The address-set
decision is an instance argument, as in the neighbouring tagged crepProps port
`update_locals_not_vars_eval_eq`. The Call cases of `pc_compile_correct` use
these when return slots are declared around a call (bead
`flapjack-pxn.18.4.3.94.2`).
-/

namespace Flapjack

namespace EvalDistinctListsFiniteSupport

/-! Same-module canonical carrier witness for the `fmap_as_finite_support`
qualifier on the tagged ports below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end EvalDistinctListsFiniteSupport

private theorem updateListEq_zip_cons {α β : Type} [DecidableEq α]
    (map : HolFiniteMapExact α β) (v : α) (vs : List α) (n : β) (ns : List β) :
    map.updateListEq ((v :: vs).zip (n :: ns)) =
      (map.updateEq (v, n)).updateListEq (vs.zip ns) := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateListEq, List.zip_cons_cons, FUPDATE_LIST_HOL_cons]
  rfl

/-- Exact port of HOL `eval_distinct_lists_not_affect`
    (`pan_to_crepProofScript.sml:4111-4124`): `!vs s e w nvals.
    LENGTH vs = LENGTH nvals /\ distinct_lists vs (var_cexp e) ==>
    eval (s with locals := s.locals |++ ZIP (vs, nvals)) e = eval s e`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_distinct_lists_not_affect"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalDistinctListsNotAffectHOL {width : Nat} [NeZero width] {σ : Type} :
    ∀ (vs : List Nat) (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (e : CrepExpHOL width) (_w : HolWordLab width) (nvals : List (HolWordLab width)),
      vs.length = nvals.length ∧ distinctListsHol vs (crepExpVarsHOL e) = true →
      evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip nvals) } e =
        evalCrepSemHOLExp s e := by
  intro vs
  induction vs with
  | nil =>
      intro s _ e _ nvals _
      rfl
  | cons v vs ih =>
      intro s _ e w nvals ⟨hlen, hdist⟩
      cases nvals with
      | nil => simp at hlen
      | cons n ns =>
          simp only [distinctListsHol, List.all_cons, Bool.and_eq_true,
            decide_eq_true_eq] at hdist
          rw [updateListEq_zip_cons]
          let s' : CrepSemHOLState width σ := { s with locals := s.locals.updateEq (v, n) }
          letI : DecidablePred s'.memaddrs := fun a => by
            simpa [s'] using (inferInstance : Decidable (s.memaddrs a))
          have h := ih s' e w ns ⟨by simpa using hlen, by simpa [distinctListsHol] using hdist.2⟩
          have h1 : evalCrepSemHOLExp s' e = evalCrepSemHOLExp s e :=
            evalCrepSemHOLExp_updateLocals_eq_of_not_vars s e v n hdist.1
          exact h.trans h1

/-- Exact port of HOL `eval_distinct_lists_not_affect'`
    (`pan_to_crepProofScript.sml:3057-3075`): `!vs s e w nvals.
    eval s e = SOME w /\ LENGTH vs = LENGTH nvals /\ distinct_lists vs (var_cexp e) ==>
    eval (s with locals := s.locals |++ ZIP (vs, nvals)) e = SOME w`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_distinct_lists_not_affect'"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem evalDistinctListsNotAffectPrimeHOL {width : Nat} [NeZero width] {σ : Type} :
    ∀ (vs : List Nat) (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (e : CrepExpHOL width) (w : HolWordLab width) (nvals : List (HolWordLab width)),
      evalCrepSemHOLExp s e = some w ∧ vs.length = nvals.length ∧
        distinctListsHol vs (crepExpVarsHOL e) = true →
      evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip nvals) } e =
        some w := by
  intro vs s _ e w nvals ⟨heval, hlen, hdist⟩
  rw [evalDistinctListsNotAffectHOL vs s e w nvals ⟨hlen, hdist⟩, heval]

private theorem mapM_congr_mem {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x, x ∈ xs → f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.mapM_cons, h x (by simp),
        mapM_congr_mem f g xs (fun y hy => h y (by simp [hy]))]

/-- Exact port of HOL `opt_mmap_eval_distinct_lists_not_affect'`
    (`pan_to_crepProofScript.sml:4126-4137`): `!es s ws vs nvals.
    LENGTH vs = LENGTH nvals /\ distinct_lists vs (FLAT (MAP var_cexp es)) ==>
    OPT_MMAP (eval (s with locals := s.locals |++ ZIP (vs, nvals))) es =
    OPT_MMAP (eval s) es`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "opt_mmap_eval_distinct_lists_not_affect'"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalDistinctListsNotAffectPrimeHOL {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (_ws : List (HolWordLab width)) (vs : List Nat) (nvals : List (HolWordLab width)),
      vs.length = nvals.length ∧ distinctListsHol vs (es.flatMap crepExpVarsHOL) = true →
      es.mapM (evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip nvals) }) =
        es.mapM (evalCrepSemHOLExp s) := by
  intro es s _ ws vs nvals ⟨hlen, hdist⟩
  apply mapM_congr_mem
  intro e he
  apply evalDistinctListsNotAffectHOL vs s e (HolWordLab.word 0) nvals
  refine ⟨hlen, ?_⟩
  simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq] at hdist ⊢
  intro v hv hmem
  exact hdist v hv (List.mem_flatMap.mpr ⟨e, he, hmem⟩)

/-- Exact port of HOL `opt_mmap_eval_distinct_lists_not_affect`
    (`pan_to_crepProofScript.sml:3077-3093`): `!es s ws vs nvals.
    OPT_MMAP (eval s) es = SOME ws /\ LENGTH vs = LENGTH nvals /\
    distinct_lists vs (FLAT (MAP var_cexp es)) ==>
    OPT_MMAP (eval (s with locals := s.locals |++ ZIP (vs, nvals))) es = SOME ws`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "opt_mmap_eval_distinct_lists_not_affect"
  (fmap_as_finite_support := [locals, globals, code])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalDistinctListsNotAffectHOL {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
      (ws : List (HolWordLab width)) (vs : List Nat) (nvals : List (HolWordLab width)),
      es.mapM (evalCrepSemHOLExp s) = some ws ∧ vs.length = nvals.length ∧
        distinctListsHol vs (es.flatMap crepExpVarsHOL) = true →
      es.mapM (evalCrepSemHOLExp { s with locals := s.locals.updateListEq (vs.zip nvals) }) =
        some ws := by
  intro es s _ ws vs nvals ⟨heval, hlen, hdist⟩
  rw [optMmapEvalDistinctListsNotAffectPrimeHOL es s ws vs nvals ⟨hlen, hdist⟩, heval]

end Flapjack
