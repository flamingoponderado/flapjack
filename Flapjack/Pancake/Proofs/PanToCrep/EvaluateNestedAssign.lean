import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.Proofs.PanToCrep.TotalEvaluateCases

/-! Exact Pan-to-Crep Assign-list theorem group. -/

namespace Flapjack

namespace EvalNestedAssignFiniteSupport

/-! Flapjack-only canonical carrier witness required by the finite-map
qualifier in this module. This repeats the roundtrip in the exact theorem's
counterpart module so that the checker can validate evidence locally; it is not
a separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : CrepSemBroadState width σ) (h : state.FiniteSupport),
        (CrepSemBroadState.ofBroad state h).toBroad = state) ∧
    (∀ state : CrepSemHOLState width σ,
        CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  CrepSemHOLState.holFmapAsFiniteSupportWitness

end EvalNestedAssignFiniteSupport

/-! HOL's evaluator uses classical decisions for memory-domain membership.
The proof-side expression wrapper chooses that decision explicitly, keeping it
out of the ported theorem's quantified variables and five logical premises. -/

/-- Flapjack-only classical choice of the memory-domain decision procedure for
the exact expression evaluator. It is wrapper infrastructure because HOL's
`eval` has no explicit Lean `DecidablePred` argument. -/
noncomputable def evalCrepSemHOLExpDefault {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (expression : CrepExpHOL width) :=
  evalCrepSemHOLExpWithMemDec state
    (fun address => Classical.propDecidable (state.memaddrs address)) expression

/-- Flapjack-only proof infrastructure for the HOL list induction; there is no
separate HOL declaration for this internal lemma. The
explicit decision procedures are operational arguments to the Lean evaluator;
the final tagged theorem below hides them behind the classical wrappers. -/
theorem evalNestedAssignDistinctEqCrepHOLWithDeciders {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (memDec : (address : BitVec width) → Decidable (state.memaddrs address))
    (shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address))
    (expressions : List (CrepExpHOL width)) (names : List Nat)
    (values oldValues : List (HolWordLab width))
    (hEval : expressions.map (crepExactEvalExp state memDec) = values.map some)
    (hLocals : names.mapM state.locals.lookup = some oldValues)
    (hDistinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (hNodup : names.Nodup)
    (hLength : names.length = expressions.length) :
    evalCrepSemHOLProg state memDec shMemDec
        (crepNestedSeqHOL
          (names.zipWith (fun name expression => CrepProgHOL.assign name expression)
            expressions)) =
      (none, { state with locals := state.locals.updateListEq (names.zip values) }) := by
  induction expressions generalizing names values oldValues state memDec shMemDec with
  | nil =>
      cases names with
      | nil =>
          cases values with
          | nil =>
              simp [crepNestedSeqHOL, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
          | cons value values =>
              simp at hEval
      | cons name names =>
          simp at hLength
  | cons expression expressions ih =>
      cases names with
      | nil =>
          simp at hLength
      | cons name names =>
          cases values with
          | nil =>
              simp at hEval
          | cons value values =>
              simp only [List.map_cons] at hEval
              obtain ⟨hEvalHead, hEvalTail⟩ := List.cons.inj hEval
              have hLookMap :=
                (optMmapEqSome (name :: names) state.locals.lookup oldValues).mp hLocals
              cases oldValues with
              | nil =>
                  simp at hLookMap
              | cons oldValue oldValues =>
                  simp only [List.map_cons] at hLookMap
                  obtain ⟨hlookup, hLookupTailMap⟩ := List.cons.inj hLookMap
                  have hLookupTail :
                      names.mapM state.locals.lookup = some oldValues :=
                    (optMmapEqSome names state.locals.lookup oldValues).mpr hLookupTailMap
                  have hLengthTail : names.length = expressions.length := by
                    simpa using hLength
                  have hNodupTail : names.Nodup := (List.nodup_cons.mp hNodup).2
                  have hNameNotTail : name ∉ names := (List.nodup_cons.mp hNodup).1
                  have hDisjoint :
                      ListDisjoint (name :: names)
                        ((expression :: expressions).flatMap crepExpVarsHOL) :=
                    (distinctListsHol_eq_true_iff_listDisjoint _ _).mp hDistinct
                  have hNameNotVars :
                      name ∉ (expression :: expressions).flatMap crepExpVarsHOL := by
                    intro hmem
                    exact hDisjoint name (by simp) hmem
                  have hDistinctTail :
                      distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true := by
                    apply (distinctListsHol_eq_true_iff_listDisjoint _ _).mpr
                    intro n hn hvars
                    have hvars' : n ∈ (expression :: expressions).flatMap crepExpVarsHOL := by
                      simp only [List.flatMap_cons, List.mem_append]
                      exact Or.inr hvars
                    exact hDisjoint n (by simp [hn]) hvars'
                  have hNameNotHead : name ∉ crepExpVarsHOL expression := by
                    intro hmem
                    apply hNameNotVars
                    exact List.mem_flatMap.mpr ⟨expression, by simp, hmem⟩
                  have hNameNotTailVars :
                      ∀ e, e ∈ expressions → name ∉ crepExpVarsHOL e := by
                    intro e he hmem
                    apply hNameNotVars
                    exact List.mem_flatMap.mpr ⟨e, by simp [he], hmem⟩
                  let assignedState : CrepSemHOLState width σ :=
                    CrepSemHOLState.setVar name value state
                  let updatedState : CrepSemHOLState width σ :=
                    crepStampExactDomains state
                      (fixClockCrepSemHOL state
                        ((none : Option (CrepResultHOLExact width)), assignedState)).2
                  have hEvalUpdatedMap :
                      expressions.map (crepExactEvalExp updatedState memDec) =
                        expressions.map (crepExactEvalExp state memDec) := by
                    apply List.map_congr_left
                    intro e he
                    have hfresh := hNameNotTailVars e he
                    simpa [updatedState, assignedState, CrepSemHOLState.setVar,
                      crepStampExactDomains, fixClockCrepSemHOL, crepExactEvalExp,
                      evalCrepSemHOLExpWithMemDec] using
                      evalCrepSemHOLExpWithMemDec_updateLocals_eq_of_not_vars
                        state memDec e name value hfresh
                  have hEvalUpdated :
                      expressions.map (crepExactEvalExp updatedState memDec) =
                        values.map some := hEvalUpdatedMap.trans hEvalTail
                  have hLookupEq :
                      names.map updatedState.locals.lookup = names.map state.locals.lookup := by
                    apply List.map_congr_left
                    intro n hn
                    have hne : n ≠ name := by
                      intro heq
                      subst n
                      exact hNameNotTail hn
                    simp [updatedState, assignedState, CrepSemHOLState.setVar,
                      fixClockCrepSemHOL,
                      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hne]
                  have hLookupTailUpdated :
                      names.mapM updatedState.locals.lookup = some oldValues := by
                    apply (optMmapEqSome names updatedState.locals.lookup oldValues).mpr
                    rw [hLookupEq]
                    exact hLookupTailMap
                  have hAssign :
                      evalCrepSemHOLProg state memDec shMemDec (.assign name expression) =
                        (none, assignedState) := by
                    simp [evalCrepSemHOLProg_assign, hEvalHead, hlookup, assignedState,
                      CrepSemHOLState.setVar]
                  simp only [List.zipWith, crepNestedSeqHOL]
                  rw [evalCrepSemHOLProg_seq_normal_of_eval_eq state memDec shMemDec
                    (.assign name expression)
                    (crepNestedSeqHOL (List.zipWith
                      (fun n e => CrepProgHOL.assign n e) names expressions))
                    assignedState hAssign]
                  have htail := ih updatedState memDec shMemDec names values oldValues
                    hEvalUpdated hLookupTailUpdated hDistinctTail hNodupTail hLengthTail
                  simpa [updatedState, assignedState, CrepSemHOLState.setVar,
                    crepStampExactDomains, fixClockCrepSemHOL,
                    HolFiniteMapExact.updateListEq, HolFiniteMapExact.updateEq,
                    FUPDATE_LIST_HOL_cons] using htail

/-- Exact port of HOL `eval_nested_assign_distinct_eq`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:540-581`). The five HOL
premises map clause-for-clause: `MAP (eval t) es = MAP SOME ev` is the
classical expression list evaluation, `OPT_MMAP (FLOOKUP t.locals) ns = SOME vs`
is the local lookup list, `distinct_lists ns (FLAT (MAP var_cexp es))` is
`distinctListsHol`, `ALL_DISTINCT ns` is `names.Nodup`, and
`LENGTH ns = LENGTH es`. The conclusion evaluates `nested_seq (MAP2 Assign ns es)`
to `(NONE, t with locals := t.locals |++ ZIP (ns, ev))`, matching
`crepNestedSeqHOL`, `CrepProgHOL.assign`, and the exact `|++` rendering
`HolFiniteMapExact.updateListEq`. Tag restored 2026-09-28 (bead
`flapjack-pxn.18.4.3.113.1`) after the previously cited gaps were closed:
crepStampExactDomains domain inertness (`flapjack-4ac.5.16.5.32`), the exact
`UInt8`/word8 byte bridges (`flapjack-4ac.5.16.5.18`), the reviewed 19-arm
crepSem `evaluate_def` tag, and the imported-owner plus evaluator-local witness
rule (`flapjack-4ac.5.16.5.21`). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "eval_nested_assign_distinct_eq"
  (fmap_as_finite_support := [locals])
  (words_as_type_indexed_bitvec)]
theorem evalNestedAssignDistinctEqCrepHOL {width : Nat} [NeZero width]
    {σ : Type} (state : CrepSemHOLState width σ)
    (expressions : List (CrepExpHOL width)) (names : List Nat)
    (values oldValues : List (HolWordLab width))
    (hEval : expressions.map (evalCrepSemHOLExpDefault state) = values.map some)
    (hLocals : names.mapM state.locals.lookup = some oldValues)
    (hDistinct : distinctListsHol names (expressions.flatMap crepExpVarsHOL) = true)
    (hNodup : names.Nodup)
    (hLength : names.length = expressions.length) :
    evalCrepSemHOLProgExact state
        (crepNestedSeqHOL
          (names.zipWith (fun name expression => CrepProgHOL.assign name expression)
            expressions)) =
      (none, { state with locals := state.locals.updateListEq (names.zip values) }) := by
  let memDec : (address : BitVec width) → Decidable (state.memaddrs address) :=
    fun address => Classical.propDecidable (state.memaddrs address)
  let shMemDec : (address : BitVec width) → Decidable (state.shMemaddrs address) :=
    fun address => Classical.propDecidable (state.shMemaddrs address)
  have hEvalDef :
      evalCrepSemHOLExpDefault state = crepExactEvalExp state memDec := by
    funext expression
    rfl
  have hEval' : expressions.map (crepExactEvalExp state memDec) = values.map some := by
    rw [← hEvalDef]
    exact hEval
  simpa [evalCrepSemHOLProgExact, memDec, shMemDec] using
    evalNestedAssignDistinctEqCrepHOLWithDeciders state memDec shMemDec
      expressions names values oldValues hEval' hLocals hDistinct hNodup hLength


end Flapjack
