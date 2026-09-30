import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerNoDestination
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerArguments
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallHandlerFlag
import Flapjack.Pancake.Proofs.PanGlobals.UnchangedLocal.Assemble
import Flapjack.Pancake.Proofs.PanGlobals.FreshLocal.TwoLocals
import Flapjack.Pancake.Proofs.PanGlobals.ShapeValueEval

namespace Flapjack.PanGlobalsCompileCorrectCallGlobalHandler
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString (ofString)
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsCompileCorrect

/-- Flapjack map infrastructure: undo a scoped write with its original lookup,
including an absent original binding. No separately named HOL declaration. -/
private theorem restoreUpdate {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS) (value : ValueHOL width) :
    HolFiniteMapExact.resVarEq (locals.update (name, value)) (name, locals.lookup name) = locals := by
  classical
  apply HolFiniteMapExact.ext
  funext key
  cases hl : locals.lookup name with
  | none =>
    simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
      HolFiniteMapExact.lookup_update_pointwise, FDOMSUB_HOL]
    by_cases hk : key = name <;> simp [hk, hl]
  | some oldValue =>
    simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_updateEq,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE_HOL]
    by_cases hk : key = name <;> simp [hk, hl]

/-- Internal restoration algebra for the two generated scratch locals. The
initializer and final result values may differ, and either original binding
may be absent. No standalone HOL declaration corresponds to this composition. -/
private theorem restoreTwoScratchWrites {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (resultName flagName : MlS)
    (initializer resultValue flagValue : ValueHOL width) (hne : resultName ≠ flagName) :
    HolFiniteMapExact.resVarEq
      (HolFiniteMapExact.resVarEq
        ((locals.update (resultName, resultValue)).update (flagName, flagValue))
        (flagName, (locals.update (resultName, initializer)).lookup flagName))
      (resultName, locals.lookup resultName) = locals := by
  have hlookup : (locals.update (resultName, initializer)).lookup flagName =
      (locals.update (resultName, resultValue)).lookup flagName := by
    simp [FUPDATE, hne]
  rw [hlookup, restoreUpdate, restoreUpdate]

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

/-- Present-global proof step: the original state relation supplies the shape
wellformedness needed by the generated declaration. Initialization success and
shape recovery are conclusions, not extra assumptions on the constructor.
This factoring has no standalone HOL declaration. -/
private theorem presentContextInitializer {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name : MlS) (shape : ShapeHOL) (address : BitVec width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hcontext : context.globals.lookup name = some (shape, address)) :
    ∃ initializer : ValueHOL width,
      @evalHOLFinite width σ _ target
        (fun a => Classical.propDecidable (target.memaddrs a)) (shapeValHOL shape) = some initializer ∧
      shape = shapeOfHOLExact initializer := by
  classical
  have hw := panGlobalsStateRelGlobalsWfHOLExact true context source target name
    (shape, address) ⟨hcontext, hrel⟩
  cases he : evalHOLFinite target (shapeValHOL shape) with
  | none =>
    exact False.elim (((PanGlobalsShapeValueEval.evalShapeValNone target).1 shape).mp he)
  | some initializer =>
    refine ⟨initializer, rfl, ?_⟩
    apply (PanGlobalsShapeValueEval.evalShapeValShape target).1 shape initializer
    exact ⟨he, hw⟩

/-- Normalize the literal present-global lowering using only its context entry
and the original state relation. Both declarations restore their actual saved
lookups. The remaining central Call/If computation is left intact for the
constructor's callee and handler induction hypotheses; this is an internal
proof step, not the full HOL correctness result. -/
private theorem presentContextScope {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name function handlerId handlerVar : MlS) (arguments : List (ExpHOL width))
    (handler : ProgHOL width) (shape : ShapeHOL) (address : BitVec width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hcontext : context.globals.lookup name = some (shape, address)) :
    let compiledArguments := compileExpExactHOLList context arguments
    let compiledHandler := compileProgExactHOL context handler
    let names := handlerVar :: freeVarIdsHOL compiledHandler ++ compiledArguments.flatMap varExpHOL
    let resultName := freshNameMlS (ofString "") names
    let flagName := freshNameMlS (ofString "vn'") (resultName :: names)
    let body := ProgHOL.seq
      (.call (some (some (.local, resultName), some (handlerId, handlerVar,
        .seq compiledHandler (.assign .local flagName (.const (BitVec.ofNat width 1))))))
        function compiledArguments)
      (.ite (.var .local flagName) .skip
        (.store (.op .sub [.topAddr, .const address]) (.var .local resultName)))
    ∃ initializer : ValueHOL width,
      shape = shapeOfHOLExact initializer ∧
      evaluateHOLFiniteState target
        (compileProgExactHOL context
          (.call (some (some (.global, name), some (handlerId, handlerVar, handler)))
            function arguments)) =
        (let resultState := setVarHOLFinite resultName initializer target
         let scratchState := setVarHOLFinite flagName (.val (.word (BitVec.ofNat width 0))) resultState
         let output := evaluateHOLFiniteState scratchState body
         let flagPost := {output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (flagName, resultState.locals.lookup flagName))}
         (output.1, {flagPost with locals := (HolFiniteMapExact.resVarEq flagPost.locals
           (resultName, target.locals.lookup resultName))})) := by
  classical
  dsimp only
  obtain ⟨initializer, hinit, hshape⟩ :=
    presentContextInitializer context source target name shape address hrel hcontext
  refine ⟨initializer, hshape, ?_⟩
  simp only [compileProgExactHOL, hcontext]
  exact scopedHandlerPrefix target _ _ shape initializer _ hinit hshape

/-- Normal-return tail of the present-global branch. Derives the Store run
and restores both scoped locals from the callee relation and caller snapshots.
The premises are internal branch facts, not a public constructor statement;
no target Store execution or post-state relation is assumed. -/
private theorem returnedValueStoreTail {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (source target sourcePost targetPost : PanSemStateFiniteExact width σ)
    (name resultName flagName : MlS) (initializer value : ValueHOL width)
    (hne : resultName ≠ flagName)
    (hcaller : panGlobalsStateRelHOLExact true context source target)
    (hcallee : panGlobalsStateRelHOLExact false context sourcePost targetPost)
    (hvalid : isValidValueHOLFinite sourcePost .global name value = true) :
    let targetResult := setVarHOLFinite resultName initializer target
    let targetScratch := setVarHOLFinite flagName (.val (.word (BitVec.ofNat width 0)))
      (setVarHOLFinite resultName value {targetPost with locals := target.locals})
    ∃ address storePost,
      context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
      evaluateHOLFiniteState targetScratch
        (.ite (.var .local flagName) .skip
          (.store (.op .sub [.topAddr, .const address]) (.var .local resultName))) = (none, storePost) ∧
      panGlobalsStateRelHOLExact true context
        (setGlobalHOLFinite name value {sourcePost with locals := source.locals})
        {storePost with locals := (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq storePost.locals
            (flagName, targetResult.locals.lookup flagName))
          (resultName, target.locals.lookup resultName))} := by
  classical
  dsimp only
  have hlocals := hcaller.2.1 rfl
  have hrestored := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL context
    sourcePost targetPost true source.locals).2 hcallee
  have hpair : panGlobalsStateRelHOLExact true context
      {sourcePost with locals := source.locals} {targetPost with locals := target.locals} := by
    simpa only [hlocals] using hrestored
  have hresult := PanGlobalsStateRelationLocals.stateRelSetVarHOL context _ _ true
    resultName value hpair
  have hscratch := PanGlobalsStateRelationLocals.stateRelSetVarHOL context _ _ true
    flagName (.val (.word (BitVec.ofNat width 0))) hresult
  let sourceScratch := setVarHOLFinite flagName (.val (.word (BitVec.ofNat width 0)))
    (setVarHOLFinite resultName value {sourcePost with locals := source.locals})
  have hlocal : sourceScratch.locals.lookup resultName = some value := by
    simp [sourceScratch, setVarHOLFinite, FUPDATE, Ne.symm hne]
  have hscratchValid : isValidValueHOLFinite sourceScratch .global name value = true := hvalid
  obtain ⟨address, storePost, hcontext, hrun, hstore⟩ :=
    PanGlobalsCompileCorrectCallGlobal.evalGlobalStoreFromRelatedLocal context sourceScratch _
      name resultName value hscratch hlocal hscratchValid
  have hsaved := PanGlobalsStateRelationLocals.stateRelSetVarHOL context source target true
    resultName initializer hcaller
  have hflag := PanGlobalsCompileCorrectResVar.stateRelResVar true context _ _
    (setVarHOLFinite resultName initializer source) (setVarHOLFinite resultName initializer target)
    flagName flagName ⟨hstore, hsaved⟩
  have hscope := PanGlobalsCompileCorrectResVar.stateRelResVar true context _ _ source target
    resultName resultName ⟨hflag, hcaller⟩
  refine ⟨address, storePost, hcontext, ?_, ?_⟩
  · simpa only [evaluateHOLFiniteState_ite, evalHOLExact, setVarHOLFinite,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE, beq_self_eq_true,
      ite_true, (show BitVec.ofNat width 0 = 0 from rfl)] using hrun
  · simpa only [sourceScratch, setVarHOLFinite, setGlobalHOLFinite,
      restoreTwoScratchWrites _ _ _ _ _ _ hne] using hscope

/-- Internal normal-return Call computation. The local destination's shape
check is derived from its actual initializer binding. Handler code is not run
on this clause. These are callee-IH branch facts, not extra premises on the
public constructor theorem. -/
private theorem returnedLocalCall {width : Nat} {σ : Type} [NeZero width]
    (state post : PanSemStateFiniteExact width σ) (name function : MlS)
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (initializer value : ValueHOL width)
    (handler : Option (MlS × MlS × ProgHOL width))
    (hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (hcode : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), post))
    (hreturn : shapeOfHOLExact value = returnShape)
    (hlocal : state.locals.lookup name = some initializer)
    (hshape : shapeOfHOLExact value = shapeOfHOLExact initializer) :
    evaluateHOLFiniteState state (.call (some (some (.local, name), handler)) function arguments) =
      (none, setVarHOLFinite name value {post with locals := state.locals}) := by
  classical
  have hv : isValidValueHOLExact state.toExact .local name value = true := by
    simp [isValidValueHOLExact, lookupKvarHOLExact, hlocal, hshape, shapeEqHOL_eq_true]
  have hs := (shapeEqHOL_eq_true _ _).mpr hreturn
  simp only [evaluateHOLFiniteState_call, hargs, hcode, if_neg hclock, hbody,
    hs, hv, ite_true, setKvarHOLFinite]

/-- Internal matched-exception Call computation. Derives the local handler
binding validity from the actual saved binding and value shape. The result is
the handler computation itself, so no successful handler execution is assumed.
This is an internal clause used by the full constructor, not its HOL statement. -/
private theorem matchedHandlerCall {width : Nat} {σ : Type} [NeZero width]
    (state post : PanSemStateFiniteExact width σ) (function handlerId handlerVar : MlS)
    (destination : Option (VarKind × MlS)) (handler : ProgHOL width)
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape handlerShape : ShapeHOL) (initializer value : ValueHOL width)
    (hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (hcode : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape))
    (hclock : state.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.exception handlerId value), post))
    (hexception : state.eshapes.lookup handlerId = some handlerShape)
    (hhandlerShape : shapeOfHOLExact value = handlerShape)
    (hlocal : state.locals.lookup handlerVar = some initializer)
    (hshape : shapeOfHOLExact value = shapeOfHOLExact initializer) :
    evaluateHOLFiniteState state
      (.call (some (destination, some (handlerId, handlerVar, handler))) function arguments) =
      evaluateHOLFiniteState
        (setVarHOLFinite handlerVar value {post with locals := state.locals}) handler := by
  classical
  have hv : isValidValueHOLExact state.toExact .local handlerVar value = true := by
    simp [isValidValueHOLExact, lookupKvarHOLExact, hlocal, hshape, shapeEqHOL_eq_true]
  have hs := (shapeEqHOL_eq_true _ _).mpr hhandlerShape
  simp only [evaluateHOLFiniteState_call, hargs, hcode, if_neg hclock, hbody,
    ite_true, hexception, hs, hv, Bool.true_and]

/-- Reorder the matched handler binding past the two distinct scratch writes.
This identifies the actual Call handler-entry state with the state used by the
accepted two-fresh-locals transport. Distinctness is a derived internal branch
fact from the compiler's freshness list, not an extra public-case premise. -/
private theorem handlerScratchEntry {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (resultName flagName handlerVar : MlS)
    (initializer flagValue exceptionValue : ValueHOL width)
    (hr : resultName ≠ handlerVar) (hf : flagName ≠ handlerVar) :
    setVarHOLFinite handlerVar exceptionValue
      (setVarHOLFinite flagName flagValue (setVarHOLFinite resultName initializer state)) =
    setVarHOLFinite flagName flagValue
      (setVarHOLFinite resultName initializer (setVarHOLFinite handlerVar exceptionValue state)) := by
  have comm (map : HolFiniteMapExact MlS (ValueHOL width)) (a b : MlS)
      (x y : ValueHOL width) (hne : a ≠ b) :
      (map.update (a, x)).update (b, y) = (map.update (b, y)).update (a, x) := by
    apply HolFiniteMapExact.ext
    exact FUPDATE_comm map.lookup a x b y hne
  simp only [setVarHOLFinite]
  congr 1
  rw [comm _ flagName handlerVar flagValue exceptionValue hf,
    comm _ resultName handlerVar initializer exceptionValue hr]

/-- Matched-handler transport at the actual reordered entry state. Preserves
all handler outcomes and retains HOL's conditional final-locals guarantee;
no successful handler or target evaluation premise is added. This internal
composition is untagged until the full constructor is assembled. -/
private theorem handlerScratchRun {width : Nat} {σ : Type} [NeZero width]
    (state post : PanSemStateFiniteExact width σ) (handler : ProgHOL width)
    (result : Option (PanSemResultExact width)) (resultName flagName handlerVar : MlS)
    (initializer flagValue exceptionValue : ValueHOL width)
    (hr : resultName ≠ handlerVar) (hf : flagName ≠ handlerVar)
    (hresultFresh : resultName ∉ freeVarIdsHOL handler)
    (hflagFresh : flagName ∉ freeVarIdsHOL handler)
    (hrun : evaluateHOLFiniteState (setVarHOLFinite handlerVar exceptionValue state) handler =
      (result, post)) :
    ∃ locals,
      evaluateHOLFiniteState
        (setVarHOLFinite handlerVar exceptionValue
          (setVarHOLFinite flagName flagValue (setVarHOLFinite resultName initializer state)))
        handler = (result, {post with locals := locals}) ∧
      (goodResHOL result = true ∧ result ≠ some .error →
        locals = (post.locals.update (resultName, initializer)).update (flagName, flagValue)) := by
  classical
  have updateEqEqUpdate (map : HolFiniteMapExact MlS (ValueHOL width))
      (entry : MlS × ValueHOL width) : map.updateEq entry = map.update entry := by
    apply HolFiniteMapExact.ext
    exact FUPDATE_HOL_eq_FUPDATE map.lookup entry
  obtain ⟨locals, htransport, hgood⟩ :=
    PanGlobalsTwoFreshLocals.evaluateTwoFreshLocalsHOL resultName initializer flagName flagValue
      handler (setVarHOLFinite handlerVar exceptionValue state) result post
      ⟨hresultFresh, hflagFresh, hrun⟩
  refine ⟨locals, ?_, ?_⟩
  · rw [handlerScratchEntry state resultName flagName handlerVar initializer flagValue exceptionValue hr hf]
    simpa only [updateEqEqUpdate, setVarHOLFinite] using htransport
  · intro hg
    simpa only [updateEqEqUpdate] using hgood hg

/-- Restore both matched-handler scopes. For good results, unchanged-local
preservation recovers the actual caller snapshots; for other results the
relation ignores locals. The conditional scratch-map fact comes from internal
handler transport, not an assumption on the public correctness theorem. -/
private theorem restoreHandlerScopes {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width)
    (caller sourcePost targetPost : PanSemStateFiniteExact width σ)
    (handler : ProgHOL width) (result : Option (PanSemResultExact width))
    (resultName flagName handlerVar : MlS) (initializer flagValue exceptionValue : ValueHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width))
    (hrf : resultName ≠ flagName) (hrh : resultName ≠ handlerVar) (hfh : flagName ≠ handlerVar)
    (hrFresh : resultName ∉ freeVarIdsHOL handler) (hfFresh : flagName ∉ freeVarIdsHOL handler)
    (hrun : evaluateHOLFiniteState (setVarHOLFinite handlerVar exceptionValue caller) handler =
      (result, targetPost)) (hne : result ≠ some .error)
    (hrel : panGlobalsStateRelHOLExact (goodResHOL result) context sourcePost targetPost)
    (hupdated : goodResHOL result = true →
      locals = (targetPost.locals.update (resultName, initializer)).update (flagName, flagValue)) :
    panGlobalsStateRelHOLExact (goodResHOL result) context sourcePost
      {targetPost with locals := (HolFiniteMapExact.resVarEq
        (HolFiniteMapExact.resVarEq locals
          (flagName, (setVarHOLFinite resultName initializer caller).locals.lookup flagName))
        (resultName, caller.locals.lookup resultName))} := by
  refine ⟨hrel.1, ?_, hrel.2.2⟩
  intro hg
  have keepResult := PanGlobalsUnchangedLocal.evaluateUnchangedLocalHOL resultName initializer
    handler (setVarHOLFinite handlerVar exceptionValue caller) result targetPost
    ⟨hrFresh, hrun, hg, hne⟩
  have keepFlag := PanGlobalsUnchangedLocal.evaluateUnchangedLocalHOL flagName flagValue
    handler (setVarHOLFinite handlerVar exceptionValue caller) result targetPost
    ⟨hfFresh, hrun, hg, hne⟩
  have kr : targetPost.locals.lookup resultName = caller.locals.lookup resultName := by
    simpa [setVarHOLFinite, FUPDATE, Ne.symm hrh] using keepResult
  have kf : targetPost.locals.lookup flagName = caller.locals.lookup flagName := by
    simpa [setVarHOLFinite, FUPDATE, Ne.symm hfh] using keepFlag
  have savedFlag : (setVarHOLFinite resultName initializer caller).locals.lookup flagName =
      caller.locals.lookup flagName := by
    simp [setVarHOLFinite, FUPDATE, hrf]
  change sourcePost.locals = _
  have flagLookup : (targetPost.locals.update (resultName, initializer)).lookup flagName =
      targetPost.locals.lookup flagName := by
    simp [FUPDATE, hrf]
  rw [hupdated hg, savedFlag, ← kf, ← kr, ← flagLookup, restoreUpdate, restoreUpdate]
  exact hrel.2.1 hg

/-- Normal matched-handler computation including the generated flag write.
The flag binding required by the assignment is derived from fresh-local
transport, and its final value is one. Internal composition, not a public
constructor theorem or a successful-target-execution assumption. -/
private theorem normalHandlerFlagRun {width : Nat} {σ : Type} [NeZero width]
    (caller post : PanSemStateFiniteExact width σ) (handler : ProgHOL width)
    (resultName flagName handlerVar : MlS) (initializer exceptionValue : ValueHOL width)
    (hr : resultName ≠ handlerVar) (hf : flagName ≠ handlerVar)
    (hrFresh : resultName ∉ freeVarIdsHOL handler) (hfFresh : flagName ∉ freeVarIdsHOL handler)
    (hrun : evaluateHOLFiniteState (setVarHOLFinite handlerVar exceptionValue caller) handler =
      (none, post)) :
    ∃ finalPost,
      evaluateHOLFiniteState
        (setVarHOLFinite handlerVar exceptionValue
          (setVarHOLFinite flagName (.val (.word (BitVec.ofNat width 0)))
            (setVarHOLFinite resultName initializer caller)))
        (.seq handler (.assign .local flagName (.const (BitVec.ofNat width 1)))) = (none, finalPost) ∧
      finalPost = {post with locals := ((post.locals.update (resultName, initializer)).update
        (flagName, .val (.word (BitVec.ofNat width 1))))} := by
  obtain ⟨locals, htransport, hgood⟩ := handlerScratchRun caller post handler none
    resultName flagName handlerVar initializer (.val (.word (BitVec.ofNat width 0))) exceptionValue
    hr hf hrFresh hfFresh hrun
  have hmap := hgood ⟨rfl, by simp⟩
  have hbinding : ({post with locals := locals} : PanSemStateFiniteExact width σ).locals.lookup flagName =
      some (.val (.word (BitVec.ofNat width 0))) := by
    simp [hmap, FUPDATE]
  have hflag := PanGlobalsCallHandlerFlag.handlerFlagNormal _ {post with locals := locals}
    handler flagName (BitVec.ofNat width 0) htransport hbinding
  refine ⟨_, hflag, ?_⟩
  simp only [setVarHOLFinite, hmap]
  congr 1
  apply HolFiniteMapExact.ext
  funext key
  by_cases hk : flagName = key <;> simp [FUPDATE, hk]

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
