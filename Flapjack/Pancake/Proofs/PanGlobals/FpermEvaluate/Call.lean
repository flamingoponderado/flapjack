import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.CallEntry

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermCallSupport
/-- Canonical representation infrastructure, with no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermCallSupport

/-- Candidate original Call constructor of evaluate_fperm. The two IHs retain
the original successful-entry and matched-handler guards. All evaluator
results, including Error, are transported. The product-decomposition binders
of evaluate_ind are substituted by their components; the matched exception
ID equality is substituted before the handler IH. No target run or successful
result is assumed. The canonical state and positive word/Type0 FFI carriers
are qualified explicitly. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Call {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (name : MlS) (expressions : List (ExpHOL width))
    (ih : ∀ (values : List (ValueHOL width)) (body : ProgHOL width)
        (callee : HolFiniteMapExact MlS (ValueHOL width)) (shape : ShapeHOL),
      evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions = some values ∧
        lookupCodeHOLFinite state.code.lookup name values = some (body, callee, shape) ∧
        state.clock ≠ 0 →
      ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (res, post) →
        evaluateHOLFiniteState
          { callEntryStateHOLFinite state callee with code := fpermCodeHOL f g state.code }
          (fpermHOL f g body) = (res, { post with code := fpermCodeHOL f g post.code }))
    (ihHandler : ∀ (values : List (ValueHOL width)) (body : ProgHOL width)
        (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
        (post : PanSemStateFiniteExact width σ) (destination : Option (VarKind × MlS))
        (eid evar : MlS) (handler : ProgHOL width) (value : ValueHOL width) (shape : ShapeHOL),
      evalListHOLFinite state
          (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions = some values ∧
        lookupCodeHOLFinite state.code.lookup name values = some (body, callee, returnShape) ∧
        state.clock ≠ 0 ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
          (some (.exception eid value), post) ∧
        info = some (destination, some (eid, evar, handler)) ∧
        state.eshapes.lookup eid = some shape ∧ shapeOfHOLExact value = shape ∧
        isValidValueHOLExact state.toExact .local evar value = true →
      ∀ (res : Option (PanSemResultExact width)) (handlerPost : PanSemStateFiniteExact width σ),
        evaluateHOLFiniteState (setVarHOLFinite evar value { post with locals := state.locals })
          handler = (res, handlerPost) →
        evaluateHOLFiniteState
          { setVarHOLFinite evar value { post with locals := state.locals }
              with code := fpermCodeHOL f g post.code }
          (fpermHOL f g handler) =
          (res, { handlerPost with code := fpermCodeHOL f g handlerPost.code }))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.call info name expressions) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.call info name expressions)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have hperm : ∀ (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))),
      fpermHOL f g (.call caltyp name expressions) =
      .call (match caltyp with
        | none => none
        | some (destination, handler) => some (destination, match handler with
          | none => none
          | some (eid, evar, program) => some (eid, evar, fpermHOL f g program)))
        (fpermName f g name) expressions := by
    intro caltyp
    cases caltyp with
    | none => simp only [fpermHOL]
    | some pair =>
      obtain ⟨destination, handler⟩ := pair
      cases handler with
      | none => simp only [fpermHOL]
      | some triple =>
        obtain ⟨eid, evar, program⟩ := triple
        simp only [fpermHOL]
  have validCode : ∀ kind evar value,
      isValidValueHOLExact { state with code := fpermCodeHOL f g state.code }.toExact kind evar value =
        isValidValueHOLExact state.toExact kind evar value := by
    intro kind evar value
    cases kind <;> rfl
  have hfull : evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.call info name expressions)) =
      let result := evaluateHOLFiniteState state (.call info name expressions)
      (result.1, { result.2 with code := fpermCodeHOL f g result.2.code }) := by
    cases ha : evalListHOLFinite state
        (h := fun address => Classical.propDecidable (state.memaddrs address)) expressions with
    | none => exact FpermCallEntry.nonrecursive f g state info name expressions (Or.inl ha)
    | some values =>
      cases hl : lookupCodeHOLFinite state.code.lookup name values with
      | none =>
        exact FpermCallEntry.nonrecursive f g state info name expressions
          (Or.inr ⟨values, ha, Or.inl hl⟩)
      | some triple =>
        obtain ⟨body, callee, shape⟩ := triple
        by_cases hz : state.clock = 0
        · exact FpermCallEntry.nonrecursive f g state info name expressions
            (Or.inr ⟨values, ha, Or.inr hz⟩)
        · generalize hbody : evaluateHOLFiniteState
              (callEntryStateHOLFinite state callee) body = bodyRun
          obtain ⟨bodyRes, bodyPost⟩ := bodyRun
          have ht := ih values body callee shape ⟨ha, hl, hz⟩ bodyRes bodyPost hbody
          rw [hperm info]
          simp only [evaluateHOLFiniteState_call]
          rw [FpermCallEntry.arguments f g state expressions]
          simp only [ha]
          rw [FpermCallEntry.lookup f g state.code name values, hl]
          simp only [Option.map_some, hz, if_false]
          rw [FpermCallEntry.entry f g state callee, ht, hbody]
          simp only [validCode]
          cases bodyRes with
          | none => rfl
          | some result =>
            cases result with
            | «break» => rfl
            | «continue» => rfl
            | error => rfl
            | timeOut => rfl
            | finalFfi outcome => rfl
            | returned value =>
              by_cases hs : shapeEqHOL (shapeOfHOLExact value) shape = true
              · simp only [hs, if_true]
                cases info with
                | none => rfl
                | some pair =>
                  obtain ⟨destination, handler⟩ := pair
                  cases destination with
                  | none => rfl
                  | some pair =>
                    obtain ⟨kind, evar⟩ := pair
                    dsimp only
                    by_cases hv : isValidValueHOLExact state.toExact kind evar value = true
                    · simp only [hv, if_true]
                      cases kind <;> rfl
                    · simp only [hv, Bool.false_eq_true, if_false]
              · simp only [hs, Bool.false_eq_true, if_false]
            | exception eid value =>
              cases info with
              | none => rfl
              | some pair =>
                obtain ⟨destination, handler⟩ := pair
                cases handler with
                | none => rfl
                | some triple =>
                  obtain ⟨handlerId, evar, handler⟩ := triple
                  by_cases hid : eid = handlerId
                  · subst handlerId
                    simp only [if_true]
                    cases he : state.eshapes.lookup eid with
                    | none => rfl
                    | some handlerShape =>
                      by_cases hv : (shapeEqHOL (shapeOfHOLExact value) handlerShape &&
                          isValidValueHOLExact state.toExact .local evar value) = true
                      · have hh := hv
                        simp only [Bool.and_eq_true] at hh
                        obtain ⟨hshape, hvalid⟩ := hh
                        generalize hhandler : evaluateHOLFiniteState
                          (setVarHOLFinite evar value { bodyPost with locals := state.locals }) handler = handlerRun
                        obtain ⟨handlerRes, handlerPost⟩ := handlerRun
                        have hp := ihHandler values body callee shape bodyPost destination eid evar
                          handler value handlerShape ⟨ha, hl, hz, hbody, rfl, he, (shapeEqHOL_eq_true _ _).mp hshape, hvalid⟩
                          handlerRes handlerPost hhandler
                        simpa only [hv, if_true, setVarHOLFinite, hhandler] using hp
                      · simp only [hv, Bool.false_eq_true, if_false]
                  · simp only [hid, if_false]
                    rfl
  simpa only [heval] using hfull

end Flapjack
