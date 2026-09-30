import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerArguments
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerFlag
import Flapjack.Pancake.Proofs.PanGlobals.ShapeValueEval

namespace Flapjack.PanGlobalsCompileCorrectCallGlobalHandler
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsCompileCorrect

/-- Internal normalization of the two scoped declarations in the literal
Global-with-handler compile_def lowering (pan_globalsScript.sml:121-125).
Both restoration lookups are taken at the actual corresponding caller states;
no absent-binding or distinct-name assumption is made. This specialized proof
step has no standalone HOL original and does not establish compile_correct. -/
private theorem scopedHandlerPrefix {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (resultName flagName : MlS)
    (shape : ShapeHOL) (initializer : ValueHOL width) (body : ProgHOL width)
    (hinit : @evalHOLFinite width σ _ state
      (fun a => Classical.propDecidable (state.memaddrs a)) (shapeValHOL shape) = some initializer)
    (hshape : shape = shapeOfHOLExact initializer) :
    evaluateHOLFiniteState state
      (.dec resultName shape (shapeValHOL shape)
        (.dec flagName .one (.const (BitVec.ofNat width 0)) body)) =
      (let resultState := setVarHOLFinite resultName initializer state
       let scratchState := setVarHOLFinite flagName (.val (.word (BitVec.ofNat width 0))) resultState
       let output := evaluateHOLFiniteState scratchState body
       let flagPost := {output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
         (flagName, resultState.locals.lookup flagName))}
       (output.1, {flagPost with locals := (HolFiniteMapExact.resVarEq flagPost.locals
         (resultName, state.locals.lookup resultName))})) := by
  classical
  rw [evaluateHOLFiniteState_dec_total]
  have hinit' : @evalHOLExact width σ _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (shapeValHOL shape) = some initializer := hinit
  have hshape' : shapeEqHOL shape (shapeOfHOLExact initializer) = true :=
    (shapeEqHOL_eq_true _ _).mpr hshape
  simp only [hinit', hshape', ite_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ite_true]

/-- Internal source branch used when the global destination is absent. Non-Error
excludes a normal return to the missing global; all other Call clauses ignore
the return destination. This is a proof step, not a standalone HOL declaration. -/
private theorem missingGlobalCallRun {width : Nat} {σ : Type} [NeZero width]
    (state post : PanSemStateFiniteExact width σ) (name function handlerId handlerVar : MlS)
    (arguments : List (ExpHOL width)) (handler : ProgHOL width)
    (result : Option (PanSemResultExact width))
    (missing : state.globals.lookup name = none)
    (run : evaluateHOLFiniteState state
      (.call (some (some (.global, name), some (handlerId, handlerVar, handler)))
        function arguments) = (result, post))
    (nonError : result ≠ some .error) :
    evaluateHOLFiniteState state
      (.call (some (none, some (handlerId, handlerVar, handler))) function arguments) =
      (result, post) := by
  classical
  rw [evaluateHOLFiniteState_call] at run ⊢
  cases ha : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => simpa only [ha] using run
  | some args =>
    simp only [ha] at run ⊢
    cases hl : lookupCodeHOLFinite state.code.lookup function args with
    | none => simpa only [hl] using run
    | some entry =>
      rcases entry with ⟨body, locals, returnShape⟩
      simp only [hl] at run ⊢
      by_cases hz : state.clock = 0
      · simpa only [if_pos hz] using run
      · simp only [if_neg hz] at run ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) body with ⟨br, bs⟩
        simp only [hb] at run ⊢
        cases br with
        | none => exact run
        | some res =>
          cases res with
          | returned value =>
            have hv : isValidValueHOLExact state.toExact .global name value = false := by
              simp [isValidValueHOLExact, lookupKvarHOLExact, missing]
            by_cases hs : shapeEqHOL (shapeOfHOLExact value) returnShape = true
            · simp only [if_pos hs, hv, Bool.false_eq_true, ite_false] at run
              exact False.elim (nonError (Prod.mk.inj run).1.symm)
            · simp only [if_neg hs] at run
              exact False.elim (nonError (Prod.mk.inj run).1.symm)
          | «break» | «continue» | error | exception eid value | timeOut | finalFfi outcome => exact run

/-- Internal missing-context branch of the full constructor proof. The branch
condition selects the literal compiler fallback; the callee and handler IHs
remain those of the original evaluator. Untagged infrastructure until the full
constructor is assembled; this helper alone is not a HOL theorem port. -/
private theorem missingContextCorrect {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name function : MlS) (arguments : List (ExpHOL width))
    (handlerId handlerVar : MlS) (handlerBody : ProgHOL width)
    (ih : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body,callee,returnShape) ∧ source.clock ≠ 0 →
      compileCorrectGoal body (callEntryStateHOLFinite source callee))
    (ihHandler : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
      (value : ValueHOL width) (calleePost : PanSemStateFiniteExact width σ) (handlerShape : ShapeHOL),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body, callee, returnShape) ∧
      source.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body =
        (some (.exception handlerId value), calleePost) ∧
      source.eshapes.lookup handlerId = some handlerShape ∧
      shapeOfHOLExact value = handlerShape ∧
      isValidValueHOLExact source.toExact .local handlerVar value = true →
      compileCorrectGoal handlerBody
        (setVarHOLFinite handlerVar value {calleePost with locals := source.locals})) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      context.globals.lookup name = none →
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.call (some (some (.global, name), some (handlerId, handlerVar, handlerBody))) function arguments) = (res,post) ∧ res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target (compileProgExactHOL context (.call (some (some (.global, name), some (handlerId, handlerVar, handlerBody))) function arguments)) = (res,targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post hmissing ⟨hrel, hrun, hne⟩
  have hg : source.globals.lookup name = none := by
    cases hlookup : source.globals.lookup name with
    | none => rfl
    | some value =>
      obtain ⟨address, hcontext, _, _, _, _⟩ :=
        hrel.2.2.2.2.2.2.2.2.1 name value hlookup
      rw [hmissing] at hcontext
      contradiction
  have hsource := missingGlobalCallRun source post name function handlerId handlerVar
    arguments handlerBody res hg hrun hne
  obtain ⟨targetPost, htarget, hpost⟩ :=
    PanGlobalsCompileCorrectCallHandlerNoDestination.compileCorrect_CallHandlerNoDestination
      source function arguments handlerId handlerVar handlerBody ih ihHandler
      res context target post ⟨hrel, hsource, hne⟩
  refine ⟨targetPost, ?_, hpost⟩
  simpa only [compileProgExactHOL, hmissing] using htarget

end Flapjack.PanGlobalsCompileCorrectCallGlobalHandler
