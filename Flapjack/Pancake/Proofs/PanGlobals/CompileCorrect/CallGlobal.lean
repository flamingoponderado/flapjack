import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.CallLocal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.AssignGlobal
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ResVar

namespace Flapjack.PanGlobalsCompileCorrectCallGlobal
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString (ofString)
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsCompileCorrect

/-- Flapjack-only equation for the literal compiled argument list. -/
private theorem compileList_eq_map {width : Nat} [NeZero width]
    (context : PanGlobalsContextExact width) (args : List (ExpHOL width)) :
    compileExpExactHOLList context args = args.map (compileExpExactHOL context) := by
  induction args with
  | nil => simp only [compileExpExactHOLList, List.map_nil]
  | cons e es ih => simp only [compileExpExactHOLList, List.map_cons, ih]

/-- Flapjack map infrastructure: undo a scoped write with its original lookup,
including an absent original binding. No separately named HOL declaration. -/
private theorem restore_update {width : Nat} [NeZero width]
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

/-- Canonical state roundtrips for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Flapjack normal-return store infrastructure shared with the Global handler
case. Source validity and the related temporary binding derive the existential
store run and complete post relation through the accepted Assign case. These
are internal caller obligations, not additional compiler theorem hypotheses;
no separately named HOL declaration or exact HOL-port claim is made here. -/
theorem evalGlobalStoreFromRelatedLocal {width : Nat} {σ : Type} [NeZero width]
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width σ)
    (name temporary : MlS) (value : ValueHOL width)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hlocal : source.locals.lookup temporary = some value)
    (hvalid : isValidValueHOLFinite source .global name value = true) :
    ∃ address targetPost,
      context.globals.lookup name = some (shapeOfHOLExact value, address) ∧
      evaluateHOLFiniteState target
        (.store (.op .sub [.topAddr, .const address]) (.var .local temporary)) = (none, targetPost) ∧
      panGlobalsStateRelHOLExact true context (setGlobalHOLFinite name value source) targetPost := by
  classical
  cases hg : source.globals.lookup name with
  | none => simp [isValidValueHOLFinite, lookupKvarHOLFinite, hg] at hvalid
  | some existing =>
    have hshape : shapeOfHOLExact value = shapeOfHOLExact existing := by
      apply (shapeEqHOL_eq_true _ _).mp
      simpa [isValidValueHOLFinite, lookupKvarHOLFinite, hg] using hvalid
    obtain ⟨address, hc, _, _, _, _⟩ := hrel.2.2.2.2.2.2.2.2.1 name existing hg
    have hsourceRun : evaluateHOLFiniteState source (.assign .global name (.var .local temporary)) =
        (none, setKvarHOLFinite .global name value source) := by
      simp only [evaluateHOLFiniteState_assign, evalHOLExact, hlocal, hvalid, ite_true]
    obtain ⟨targetPost, hrun, hpost⟩ :=
      PanGlobalsCompileCorrectAssignGlobal.compileCorrect_AssignGlobal source name
        (.var .local temporary) none context target (setKvarHOLFinite .global name value source)
        ⟨hrel, hsourceRun, by simp⟩
    refine ⟨address, targetPost, ?_, ?_, hpost⟩
    · simpa only [hshape] using hc
    · simpa only [compileProgExactHOL, hc, compileExpExactHOL] using hrun

/-- Global destination Call without handler, using only the original guarded
callee IH. The target is the original DecCall with a scoped empty-name result
and Store continuation. The global write is derived through the accepted Assign
case on a paired temporary binding, then both caller-local maps are restored.
There is no target-store, post-relation or freshness premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals, callee])
  (words_as_type_indexed_bitvec)]
theorem compileCorrect_CallGlobal {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name function : MlS)
    (arguments : List (ExpHOL width))
    (ih : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments = some args ∧
      lookupCodeHOLFinite source.code.lookup function args = some (body, callee, returnShape) ∧
      source.clock ≠ 0 → compileCorrectGoal body (callEntryStateHOLFinite source callee)) :
    ∀ (res : Option (PanSemResultExact width)) (context : PanGlobalsContextExact width)
      (target post : PanSemStateFiniteExact width σ),
      panGlobalsStateRelHOLExact true context source target ∧
        evaluateHOLFiniteState source (.call (some (some (.global, name), none)) function arguments) = (res, post) ∧
        res ≠ some .error →
      ∃ targetPost,
        evaluateHOLFiniteState target
          (compileProgExactHOL context (.call (some (some (.global, name), none)) function arguments)) =
          (res, targetPost) ∧
        panGlobalsStateRelHOLExact (goodResHOL res) context post targetPost := by
  classical
  intro res context target post ⟨hrel, hev, hne⟩
  have hlocals := hrel.2.1 rfl
  rw [evaluateHOLFiniteState_call] at hev
  cases ha : evalListHOLFinite source (h := fun a => Classical.propDecidable (source.memaddrs a)) arguments with
  | none => simp only [ha] at hev; exact False.elim (hne (Prod.mk.inj hev).1.symm)
  | some args =>
    simp only [ha] at hev
    have hta := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL context source target arguments args ⟨hrel, ha⟩
    cases hl : lookupCodeHOLFinite source.code.lookup function args with
    | none => simp only [hl] at hev; exact False.elim (hne (Prod.mk.inj hev).1.symm)
    | some entry =>
      rcases entry with ⟨body, callee, returnShape⟩
      simp only [hl] at hev
      have htl := PanGlobalsStateRelationCode.stateRelLookupCodeHOL context source target true
        function args body callee returnShape ⟨hrel, hl⟩
      have hc := hrel.2.2.2.2.2.1
      by_cases hz : source.clock = 0
      · have htz : target.clock = 0 := hc ▸ hz
        simp only [if_pos hz] at hev
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
        refine ⟨emptyLocalsHOLFinite target, ?_,
          (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context source target false).1 hrel⟩
        cases hct : context.globals.lookup name with
        | none => simp only [compileProgExactHOL, hct, compileList_eq_map,
            evaluateHOLFiniteState_call, hta, htl, if_pos htz]
        | some pair => rcases pair with ⟨shape, address⟩
                       simp only [compileProgExactHOL, hct, compileList_eq_map,
                         evaluateHOLFiniteState_decCall_fixClockRewrite, hta, htl, if_pos htz]
      · have htz : target.clock ≠ 0 := hc ▸ hz
        simp only [if_neg hz] at hev
        have hd := PanGlobalsStateRelationClock.stateRelDecClockHOL context source target true hrel
        have he := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL context
          (decClockHOLFinite source) (decClockHOLFinite target) true callee).1 hd
        change panGlobalsStateRelHOLExact true context
          (callEntryStateHOLFinite source callee) (callEntryStateHOLFinite target callee) at he
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body with ⟨br, bs⟩
        simp only [hb] at hev
        have hbody := ih args body callee returnShape ⟨ha, hl, hz⟩
        cases br with
        | none => exact False.elim (hne (Prod.mk.inj hev).1.symm)
        | some result =>
          cases result with
          | «break» | «continue» | error => exact False.elim (hne (Prod.mk.inj hev).1.symm)
          | returned value =>
            by_cases hs : shapeEqHOL (shapeOfHOLExact value) returnShape = true
            · simp only [hs, ↓reduceIte] at hev
              by_cases hv : isValidValueHOLExact source.toExact .global name value = true
              · simp only [hv, ↓reduceIte] at hev
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
                cases hg : source.globals.lookup name with
                | none => simp [isValidValueHOLExact, lookupKvarHOLExact, hg] at hv
                | some oldValue =>
                  have hshape : shapeOfHOLExact value = shapeOfHOLExact oldValue := by
                    apply (shapeEqHOL_eq_true _ _).mp
                    simpa [isValidValueHOLExact, lookupKvarHOLExact, toExact, hg] using hv
                  obtain ⟨address, hct, _, _, _, _⟩ := hrel.2.2.2.2.2.2.2.2.1 name oldValue hg
                  obtain ⟨bt, hbt, hr⟩ := hbody (some (.returned value)) context
                    (callEntryStateHOLFinite target callee) bs ⟨he, hb, by simp⟩
                  obtain ⟨postValue, hpostLookup, hpostShape⟩ := evaluateHOLFiniteState_global_shape_invariant
                    (callEntryStateHOLFinite source callee) body (some (.returned value)) bs name oldValue hb hg
                  have hrestored := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL
                    context bs bt true source.locals).2 hr
                  let temporary := ofString ""
                  let ghostSource := setVarHOLFinite temporary value {bs with locals := source.locals}
                  let ghostTarget := setVarHOLFinite temporary value {bt with locals := target.locals}
                  have hghost : panGlobalsStateRelHOLExact true context ghostSource ghostTarget := by
                    simpa only [ghostSource, ghostTarget, hlocals] using
                      PanGlobalsStateRelationLocals.stateRelSetVarHOL context
                        {bs with locals := source.locals} {bt with locals := source.locals} true temporary value hrestored
                  have hghostLocal : ghostSource.locals.lookup temporary = some value := by
                    simp [ghostSource, setVarHOLFinite, FUPDATE]
                  have hghostValid : isValidValueHOLFinite ghostSource .global name value = true := by
                    simp [ghostSource, setVarHOLFinite, isValidValueHOLFinite, lookupKvarHOLFinite,
                      hpostLookup, hshape, hpostShape, shapeEqHOL_eq_true]
                  obtain ⟨storeAddress, storePost, hstoreContext, hstoreRun, hstoreRel⟩ :=
                    evalGlobalStoreFromRelatedLocal context ghostSource ghostTarget name temporary value
                      hghost hghostLocal hghostValid
                  have haddress : storeAddress = address := by
                    rw [hct] at hstoreContext
                    exact (congrArg Prod.snd (Option.some.inj hstoreContext)).symm
                  subst storeAddress
                  have hscope := PanGlobalsCompileCorrectResVar.stateRelResVar true context
                    (setKvarHOLFinite .global name value ghostSource) storePost source target temporary temporary
                    ⟨hstoreRel, hrel⟩
                  refine ⟨{storePost with locals :=
                    HolFiniteMapExact.resVarEq storePost.locals (temporary, target.locals.lookup temporary)}, ?_, ?_⟩
                  · have hshapeBool : shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact oldValue) = true :=
                      (shapeEqHOL_eq_true _ _).mpr hshape
                    simp only [compileProgExactHOL, hct, compileList_eq_map,
                      evaluateHOLFiniteState_decCall_fixClockRewrite, hta, htl, if_neg htz,
                      hbt, hshapeBool, hs, Bool.true_and, ↓reduceIte]
                    exact congrArg (fun pair => (pair.1,
                      {pair.2 with locals := HolFiniteMapExact.resVarEq pair.2.locals (temporary, target.locals.lookup temporary)})) hstoreRun
                  · simpa only [ghostSource, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
                      restore_update, goodResHOL] using hscope
              · simp only [if_neg hv] at hev
                exact False.elim (hne (Prod.mk.inj hev).1.symm)
            · simp only [if_neg hs] at hev
              exact False.elim (hne (Prod.mk.inj hev).1.symm)
          | exception eid value | timeOut | finalFfi outcome =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
            obtain ⟨bt, hbt, hr⟩ := hbody _ context (callEntryStateHOLFinite target callee) bs ⟨he, hb, by simp⟩
            refine ⟨emptyLocalsHOLFinite bt, ?_,
              (PanGlobalsStateRelationLocals.stateRelEmptyLocalsHOL context bs bt false).2 hr⟩
            cases hct : context.globals.lookup name with
            | none => simp only [compileProgExactHOL, hct, compileList_eq_map,
                evaluateHOLFiniteState_call, hta, htl, if_neg htz, hbt]
            | some pair => rcases pair with ⟨shape, address⟩
                           simp only [compileProgExactHOL, hct, compileList_eq_map,
                             evaluateHOLFiniteState_decCall_fixClockRewrite, hta, htl, if_neg htz, hbt]

end Flapjack.PanGlobalsCompileCorrectCallGlobal
