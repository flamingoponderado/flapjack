import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant

/-!
Finite-support evaluator invariant support for HOL PanProps results. The
structural-context preservation lemmas and Return/Raise payload leaves are
components of the results, not standalone HOL declarations. This module also
contains source-reviewed exact ports of `evaluate_structs_invariant` and
`evaluate_is_wf_shape_invariant`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ExpHOL ProgHOL MlS ShapeHOL)

private theorem fupdateList_eq_lookupCodeFold {width : Nat} [NeZero width]
    (initial : FiniteMap MlS (ValueHOL width))
    (entries : List (MlS × ValueHOL width)) :
    FUPDATE_LIST initial entries =
      List.foldl
        (fun (map : MlS → Option (ValueHOL width)) (entry : MlS × ValueHOL width) =>
          fun current => if current = entry.1 then some entry.2 else map current)
        initial entries := by
  induction entries generalizing initial with
  | nil => rfl
  | cons entry entries ih =>
      simp only [FUPDATE_LIST_cons, List.foldl_cons]
      have hUpdate : FUPDATE initial entry = fun current =>
          if current = entry.1 then some entry.2 else initial current := by
        funext current
        unfold FUPDATE
        by_cases h : current = entry.1
        · subst current
          have heq : (entry.1 == entry.1) = true := beq_iff_eq.mpr rfl
          rw [if_pos rfl, if_pos heq]
        · have h' : entry.1 ≠ current := fun heq => h heq.symm
          have hbeq : (entry.1 == current) = false := by
            cases heq : (entry.1 == current) with
            | false => rfl
            | true => exact False.elim (h' (beq_iff_eq.mp heq))
          have hnot : ¬ ((entry.1 == current) = true) := by
            rw [hbeq]
            decide
          simp only [if_neg h, if_neg hnot]
      rw [hUpdate]
      exact ih _

/-- The finite PanProps lookup wrapper and recursive finite PanSem evaluator use
    the same HOL `lookup_code` checks and produce extensionally identical
    callee-local lookups. This connects the existing PanProps invariant step to
    the recursive evaluator's exact lookup result. -/
private theorem lookupCodeHOLFinite_projection_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (fname : MlS) (arguments : List (ValueHOL width)) :
    (Flapjack.PanPropsEvalStateFiniteExact.lookupCodeHOLFinite state fname arguments).map
        (fun result : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL =>
          (result.1, result.2.1.lookup, result.2.2)) =
      Flapjack.lookupCodeHOLExact state.code.lookup fname arguments := by
  unfold Flapjack.PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
    Flapjack.lookupCodeHOLExact
  cases hcode : state.code.lookup fname with
  | none => rfl
  | some codeEntry =>
      rcases codeEntry with ⟨parameters, body, returnShape⟩
      by_cases hvalid : (parameters.map Prod.fst).Nodup ∧
          parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
      · simp [hvalid, HolFiniteMapExact.updateList,
          HolFiniteMapExact.empty, fupdateList_eq_lookupCodeFold]
      · simp only [if_neg hvalid, Option.map_none]

/-- Successful recursive `lookup_code` installs only values whose shapes were
    checked against the current well-formed locals/globals. This is the
    PanSem-carrier instance of HOL `lookup_code_wf_shape_invariant_step`. -/
theorem lookupCodeHOLExact_calleeLocalsWf {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (fname : MlS) (body : ProgHOL width) (calleeLocals : MlS → Option (ValueHOL width))
    (returnShape : ShapeHOL)
    (hargs : state.evalListHOLFinite arguments = some values)
    (hlookup : Flapjack.lookupCodeHOLExact state.code.lookup fname values =
      some (body, calleeLocals, returnShape))
    (hlocals : ∀ name value, state.locals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (hglobals : ∀ name value, state.globals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true) :
    ∀ name value, calleeLocals name = some value →
      isWfShapeValueHOLExact state.structs value = true := by
  let propsState : PanPropsEvalStateFiniteExact width σ := {
    locals := state.locals
    globals := state.globals
    structs := state.structs
    code := state.code
    eshapes := state.eshapes
    memory := state.memory
    memaddrs := state.memaddrs
    shMemaddrs := state.shMemaddrs
    clock := state.clock
    be := state.be
    ffi := state.ffi
    baseAddr := state.baseAddr
    topAddr := state.topAddr
  }
  have hargsProps : propsState.evalListHOL arguments = some values := by
    change evalListHOLExact propsState.toExact arguments = some values
    change evalListHOLExact state.toExact arguments = some values
    exact hargs
  have hproject := lookupCodeHOLFinite_projection_eq propsState fname values
  rw [hlookup] at hproject
  cases hfiniteLookup : PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
      propsState fname values with
  | none => simp [hfiniteLookup] at hproject
  | some found =>
      rcases found with ⟨foundBody, foundLocals, foundReturnShape⟩
      have htuple : (foundBody, foundLocals.lookup, foundReturnShape) =
          (body, calleeLocals, returnShape) := by
        simpa [hfiniteLookup] using hproject
      have hbodyEq : foundBody = body := congrArg Prod.fst htuple
      have hlocalsEq : foundLocals.lookup = calleeLocals :=
        congrArg (fun result => result.2.1) htuple
      have hreturnEq : foundReturnShape = returnShape :=
        congrArg (fun result => result.2.2) htuple
      have hlookupProps : PanPropsEvalStateFiniteExact.lookupCodeHOLFinite
          propsState fname values = some (body, foundLocals, returnShape) := by
        rw [hfiniteLookup]
        exact congrArg some (by
          rw [hbodyEq, hreturnEq])
      have hlocalsProps : ∀ name value, propsState.locals.lookup name = some value →
          isWfShapeValueHOLExact propsState.structs value = true := by
        simpa [propsState] using hlocals
      have hglobalsProps : ∀ name value, propsState.globals.lookup name = some value →
          isWfShapeValueHOLExact propsState.structs value = true := by
        simpa [propsState] using hglobals
      have hcallee := PanPropsEvalStateFiniteExact.lookupCodeWfShapeInvariantStep
        propsState arguments values fname body foundLocals returnShape
        ⟨hargsProps, hlookupProps, hlocalsProps, hglobalsProps⟩
      intro name value hvalue
      apply hcallee name value
      simpa [hlocalsEq] using hvalue

private def valuesHOLWf {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (lookup : MlS → Option (ValueHOL width)) : Prop :=
  ∀ name value, lookup name = some value →
    isWfShapeValueHOLExact structs value = true

private theorem valuesHOLWf_update {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (lookup : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (newValue : ValueHOL width)
    (hold : valuesHOLWf structs lookup.lookup)
    (hnew : isWfShapeValueHOLExact structs newValue = true) :
    valuesHOLWf structs (lookup.update (name, newValue)).lookup := by
  intro current value hlookup
  rw [HolFiniteMapExact.lookup_update_pointwise] at hlookup
  by_cases hname : current = name
  · subst current
    have hvalue : newValue = value := by simpa using hlookup
    subst value
    exact hnew
  · have hsource : lookup.lookup current = some value := by
      simpa [hname] using hlookup
    exact hold current value hsource

private theorem valuesHOLWf_empty {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact) :
    valuesHOLWf structs (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL width)).lookup := by
  intro name value hlookup
  simp at hlookup

private theorem valuesHOLWf_resVarEq {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (map1 map2 : HolFiniteMapExact MlS (ValueHOL width)) (name : MlS)
    (h1 : valuesHOLWf structs map1.lookup) (h2 : valuesHOLWf structs map2.lookup) :
    valuesHOLWf structs (HolFiniteMapExact.resVarEq map1 (name, map2.lookup name)).lookup := by
  let predicate : MlS × ValueHOL width → Bool := fun pair =>
    isWfShapeValueHOLExact structs pair.2
  have hmaps : feveryHOL predicate map1 ∧ feveryHOL predicate map2 := by
    constructor
    · intro key value hvalue
      simpa [predicate] using h1 key value hvalue
    · intro key value hvalue
      simpa [predicate] using h2 key value hvalue
  have hresult := feveryResVarFlookupHOL predicate map1 map2 name hmaps
  intro key value hvalue
  exact hresult key value hvalue

private theorem evalHOLFinite_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (hlocals : valuesHOLWf state.structs state.locals.lookup)
    (hglobals : valuesHOLWf state.structs state.globals.lookup)
    (expression : ExpHOL width) (value : ValueHOL width)
    (heval : state.evalHOLFinite expression = some value) :
    isWfShapeValueHOLExact state.structs value = true := by
  have hExact := evalHOLExact_isWfShapeValueHOLExact state.toExact
    (by simpa [valuesHOLWf, PanSemStateFiniteExact.toExact] using hlocals)
    (by simpa [valuesHOLWf, PanSemStateFiniteExact.toExact] using hglobals)
    expression value
  apply hExact
  simpa using heval

private theorem evalListHOLFinite_mem_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (hlocals : valuesHOLWf state.structs state.locals.lookup)
    (hglobals : valuesHOLWf state.structs state.globals.lookup) :
    ∀ expressions values, state.evalListHOLFinite expressions = some values →
      ∀ value, value ∈ values → isWfShapeValueHOLExact state.structs value = true := by
  intro expressions
  induction expressions with
  | nil =>
      intro values heval value hmem
      simp [PanSemStateFiniteExact.evalListHOLFinite, evalListHOLExact] at heval
      subst values
      simp at hmem
  | cons expression rest ih =>
      intro values heval value hmem
      letI : DecidablePred state.toExact.memaddrs := by
        simpa [PanSemStateFiniteExact.toExact] using
          (inferInstance : DecidablePred state.memaddrs)
      change evalListHOLExact state.toExact (expression :: rest) = some values at heval
      cases hhead : evalHOLExact state.toExact expression with
      | none => simp [evalListHOLExact, hhead] at heval
      | some head =>
          cases htail : evalListHOLExact state.toExact rest with
          | none => simp [evalListHOLExact, hhead, htail] at heval
          | some tail =>
              have hValues : values = head :: tail := by
                simpa [evalListHOLExact, hhead, htail] using heval.symm
              subst values
              simp only [List.mem_cons] at hmem
              rcases hmem with hheadMem | htailMem
              · subst value
                have hheadFinite : state.evalHOLFinite expression = some head := by
                  simpa using hhead
                exact evalHOLFinite_isWf state hlocals hglobals expression head hheadFinite
              · apply ih tail
                · simpa [PanSemStateFiniteExact.evalListHOLFinite] using htail
                · exact htailMem

/-- Flapjack-specific reduction helper for the Return/Exception result cases
    used by the evaluator invariant proofs. Its cases mirror the result match
    in HOL `evaluate_is_wf_shape_invariant`, but it has no standalone HOL
    declaration. -/
def panSemResultHOLWf {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact) :
    Option (PanSemResultExact width) → Prop
  | some (.returned value) => isWfShapeValueHOLExact structs value = true
  | some (.exception _ value) => isWfShapeValueHOLExact structs value = true
  | _ => True

namespace PanPropsShapeInvariantSupport

/-- Forwarding canonical finite-map witness for the imported owning carrier
    `PanPropsEvalStateFiniteExact` (declared in `PanProps/EvalInvariant.lean`).
    The `fmap_as_finite_support` qualifier on the exact
    `evaluate_is_wf_shape_invariant` port below requires a witness beside the
    tagged declaration, so this re-exports the canonical roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (hfinite : state.FiniteSupport),
      (PanPropsEvalStateFiniteExact.ofExact state hfinite).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
      PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness

end PanPropsShapeInvariantSupport

private def panSemStateVarsHOLWf {width : Nat} {σ : Type} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (state : PanSemStateFiniteExact width σ) : Prop :=
  valuesHOLWf structs state.locals.lookup ∧ valuesHOLWf structs state.globals.lookup

private def panSemExactStateVarsHOLWf {width : Nat} {σ : Type} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (state : PanSemStateExact width σ) : Prop :=
  valuesHOLWf structs state.locals ∧ valuesHOLWf structs state.globals

private theorem valuesHOLWf_setVarHOLExact {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact)
    (lookup : MlS → Option (ValueHOL width)) (name : MlS) (newValue : ValueHOL width)
    (hold : valuesHOLWf structs lookup)
    (hnew : isWfShapeValueHOLExact structs newValue = true) :
    valuesHOLWf structs (fun current => if current = name then some newValue else lookup current) := by
  intro current value hlookup
  by_cases hname : current = name
  · subst current
    have hvalue : newValue = value := by simpa using hlookup
    subst value
    exact hnew
  · exact hold current value (by simpa [hname] using hlookup)

private theorem valuesHOLWf_emptyHOLExact {width : Nat} [NeZero width]
    (structs : Flapjack.Pancake.PanLang.StructContextExact) :
    valuesHOLWf structs (fun _ : MlS => (none : Option (ValueHOL width))) := by
  intro name value hlookup
  simp at hlookup

private theorem panSemExactStateVarsHOLWf_setKvar {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (h : panSemExactStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemExactStateVarsHOLWf state.structs (setKvarHOLExact kind name value state) := by
  cases kind
  · simpa [panSemExactStateVarsHOLWf, setKvarHOLExact, setVarHOLExact] using
      (show valuesHOLWf state.structs (setVarHOLExact name value state).locals ∧
          valuesHOLWf state.structs (setVarHOLExact name value state).globals from
        ⟨by simpa [setVarHOLExact] using
            valuesHOLWf_setVarHOLExact state.structs state.locals name value h.1 hvalue,
          h.2⟩)
  · simpa [panSemExactStateVarsHOLWf, setKvarHOLExact, setGlobalHOLExact] using
      (show valuesHOLWf state.structs (setGlobalHOLExact name value state).locals ∧
          valuesHOLWf state.structs (setGlobalHOLExact name value state).globals from
      ⟨h.1, by simpa [setGlobalHOLExact] using
            valuesHOLWf_setVarHOLExact state.structs state.globals name value h.2 hvalue⟩)

private theorem panSemExactStateVarsHOLWf_emptyLocals {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    (h : panSemExactStateVarsHOLWf state.structs state) :
    panSemExactStateVarsHOLWf state.structs (emptyLocalsHOLExact state) := by
  exact ⟨valuesHOLWf_emptyHOLExact state.structs, h.2⟩

private theorem returnStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (hevalWf : ∀ value, evalExpression state expression = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : returnStepHOLExact state expression evalExpression = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  cases hvalue : evalExpression state expression with
  | none =>
      simp [returnStepHOLExact, hvalue] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | some value =>
      have hvalueWf := hevalWf value hvalue
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
          (shapeOfHOLExact value) ≤ 32
      · simp [returnStepHOLExact, hvalue, hsize] at heval
        rcases heval with ⟨rfl, rfl⟩
        exact ⟨rfl, panSemExactStateVarsHOLWf_emptyLocals state hvars,
          by simp [panSemResultHOLWf, hvalueWf]⟩
      · simp [returnStepHOLExact, hvalue, hsize] at heval
        rcases heval with ⟨rfl, rfl⟩
        exact ⟨rfl, hvars, trivial⟩

private theorem raiseStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (exception : MlS)
    (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (hevalWf : ∀ value, evalExpression state expression = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : raiseStepHOLExact state exception expression evalExpression = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  cases hvalue : evalExpression state expression with
  | none =>
      simp [raiseStepHOLExact, hvalue] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | some value =>
      have hvalueWf := hevalWf value hvalue
      cases hshape : state.eshapes exception with
      | none =>
          simp [raiseStepHOLExact, hvalue, hshape] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | some shape =>
          by_cases heq : shapeEqHOL (shapeOfHOLExact value) shape
          · by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                state.structs (shapeOfHOLExact value) ≤ 32
            · simp [raiseStepHOLExact, hvalue, hshape, heq, hsize] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, panSemExactStateVarsHOLWf_emptyLocals state hvars,
                by simp [panSemResultHOLWf, hvalueWf]⟩
            · simp [raiseStepHOLExact, hvalue, hshape, heq, hsize] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
          · simp [raiseStepHOLExact, hvalue, hshape, heq] at heval
            rcases heval with ⟨rfl, rfl⟩
            exact ⟨rfl, hvars, trivial⟩

private theorem tickStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : tickStepHOLExact state = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  by_cases hclock : state.clock = 0
  · simp [tickStepHOLExact, hclock] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, panSemExactStateVarsHOLWf_emptyLocals state hvars, trivial⟩
  · simp [tickStepHOLExact, hclock] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, trivial⟩

private theorem shMemLoadHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat)
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : shMemLoadHOLExact state kind name address nb = (result, output)) :
      output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  unfold shMemLoadHOLExact at heval
  by_cases hzero : nb = 0
  · by_cases hdomain : state.shMemaddrs address
    · generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb] (panWordToBytesHOL address false) = ffiResult at heval
      cases ffiResult with
      | final event =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, panSemExactStateVarsHOLWf_emptyLocals state hvars, trivial⟩
      | ret newFfi bytes =>
          have hnew : isWfShapeValueHOLExact state.structs
              (.val (.word (panWordOfBytesHOL (width := width) false 0 bytes))) = true := by
            simp [isWfShapeValueHOLExact]
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨by cases kind <;> rfl, by
            have hset := panSemExactStateVarsHOLWf_setKvar state kind name
              (.val (.word (panWordOfBytesHOL (width := width) false 0 bytes))) hvars hnew
            simpa [panSemExactStateVarsHOLWf, setKvarHOLExact,
              setVarHOLExact, setGlobalHOLExact] using hset,
            trivial⟩
    · simp [hzero, hdomain] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  · by_cases hdomain : state.shMemaddrs (panByteAlignHOL address)
    · generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb] (panWordToBytesHOL address false) = ffiResult at heval
      cases ffiResult with
      | final event =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, panSemExactStateVarsHOLWf_emptyLocals state hvars, trivial⟩
      | ret newFfi bytes =>
          have hnew : isWfShapeValueHOLExact state.structs
              (.val (.word (panWordOfBytesHOL (width := width) false 0 bytes))) = true := by
            simp [isWfShapeValueHOLExact]
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨by cases kind <;> rfl, by
            have hset := panSemExactStateVarsHOLWf_setKvar state kind name
              (.val (.word (panWordOfBytesHOL (width := width) false 0 bytes))) hvars hnew
            simpa [panSemExactStateVarsHOLWf, setKvarHOLExact,
              setVarHOLExact, setGlobalHOLExact] using hset,
            trivial⟩
    · simp [hzero, hdomain] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩

private theorem shMemStoreHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (word address : RiscV.Word width) (nb : Nat)
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : shMemStoreHOLExact state word address nb = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  unfold shMemStoreHOLExact at heval
  by_cases hzero : nb = 0
  · by_cases hdomain : state.shMemaddrs address
    · generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite)
          [BitVec.ofNat 8 nb]
          (panWordToBytesHOL word false ++ panWordToBytesHOL address false) = ffiResult at heval
      cases ffiResult with
      | final event =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | ret newFfi bytes =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, by simpa [panSemExactStateVarsHOLWf] using hvars, trivial⟩
    · simp [hzero, hdomain] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  · by_cases hdomain : state.shMemaddrs (panByteAlignHOL address)
    · generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedWrite)
          [BitVec.ofNat 8 nb]
          ((panWordToBytesHOL word false).take nb ++ panWordToBytesHOL address false) = ffiResult at heval
      cases ffiResult with
      | final event =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | ret newFfi bytes =>
          simp [hzero, hdomain] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, by simpa [panSemExactStateVarsHOLWf] using hvars, trivial⟩
    · simp [hzero, hdomain] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩

private theorem assignStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (hevalWf : ∀ value, evalExpression state source = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : assignStepHOLExact state kind name source evalExpression = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  cases hvalue : evalExpression state source with
  | none =>
      simp [assignStepHOLExact, hvalue] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | some value =>
      cases hvalid : isValidValueHOLExact state kind name value with
      | false =>
          simp [assignStepHOLExact, hvalue, hvalid] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | true =>
          have hvalueWf := hevalWf value hvalue
          simp [assignStepHOLExact, hvalue, hvalid] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨by cases kind <;> rfl,
            panSemExactStateVarsHOLWf_setKvar state kind name value hvars hvalueWf, trivial⟩

private theorem primitiveStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width)))
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : primitiveStepHOLExact state name operator arguments evalExpressions =
      (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  cases hvalues : evalExpressions state arguments with
  | none =>
      simp [primitiveStepHOLExact, hvalues] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | some values =>
      cases hprim : panPrimopHOLExact operator values with
      | none =>
          simp [primitiveStepHOLExact, hvalues, hprim] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | some value =>
          cases hvalid : isValidValueHOLExact state .local name value with
          | false =>
              simp [primitiveStepHOLExact, hvalues, hprim, hvalid] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
          | true =>
              have hvalueWf := panPrimopHOLExact_isWfShapeValueHOLExact
                state.structs operator values value hprim
              simp [primitiveStepHOLExact, hvalues, hprim, hvalid] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl,
                panSemExactStateVarsHOLWf_setKvar state .local name value hvars hvalueWf,
                trivial⟩

private theorem panSemExactStateVarsHOLWf_of_memoryStep {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    (step : Option (PanSemResultExact width) × PanSemStateExact width σ)
    (hstruct : step.2.structs = state.structs)
    (hlocals : step.2.locals = state.locals) (hglobals : step.2.globals = state.globals)
    (hresult : step.1 = none ∨ step.1 = some .error)
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : step = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  have houtput : output = step.2 := (congrArg Prod.snd heval).symm
  have hresultEq : result = step.1 := (congrArg Prod.fst heval).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [houtput]
    exact hstruct
  · constructor
    · intro name value hvalue
      rw [houtput, hlocals] at hvalue
      exact hvars.1 name value hvalue
    · intro name value hvalue
      rw [houtput, hglobals] at hvalue
      exact hvars.2 name value hvalue
  · rw [hresultEq]
    rcases hresult with h | h <;> simp [panSemResultHOLWf, h]

private theorem storeStepHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (hvars : panSemExactStateVarsHOLWf state.structs state)
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : storeStepHOLExact state destination source evalExpression = (result, output)) :
    output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
      panSemResultHOLWf state.structs result := by
  have hstep : (storeStepHOLExact state destination source evalExpression).2.structs =
      state.structs := by
    unfold storeStepHOLExact
    repeat' (first | split | simp)
  have hlocals : (storeStepHOLExact state destination source evalExpression).2.locals = state.locals := by
    unfold storeStepHOLExact
    repeat' (first | split)
    all_goals rfl
  have hglobals : (storeStepHOLExact state destination source evalExpression).2.globals = state.globals := by
    unfold storeStepHOLExact
    repeat' (first | split)
    all_goals rfl
  have hresult : (storeStepHOLExact state destination source evalExpression).1 =
      none ∨ (storeStepHOLExact state destination source evalExpression).1 = some .error := by
    unfold storeStepHOLExact
    repeat' (first | split)
    all_goals simp
  have houtput : output = (storeStepHOLExact state destination source evalExpression).2 :=
    (congrArg Prod.snd heval).symm
  have hresultEq : result =
      (storeStepHOLExact state destination source evalExpression).1 :=
    (congrArg Prod.fst heval).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [houtput]
    exact hstep
  · constructor
    · intro name value hvalue
      rw [houtput, hlocals] at hvalue
      exact hvars.1 name value hvalue
    · intro name value hvalue
      rw [houtput, hglobals] at hvalue
      exact hvars.2 name value hvalue
  · rw [hresultEq]
    rcases hresult with h | h <;> simp [panSemResultHOLWf, h]

private theorem evalPanSemNonrecursiveHOLExact_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (hvars : panSemExactStateVarsHOLWf state.structs state) :
    ∀ result output,
      evalPanSemNonrecursiveHOLExact program state = some (result, output) →
        output.structs = state.structs ∧ panSemExactStateVarsHOLWf state.structs output ∧
          panSemResultHOLWf state.structs result := by
  cases program with
  | skip =>
      intro result output heval
      simp only [evalPanSemNonrecursiveHOLExact, Option.some.injEq, Prod.mk.injEq] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | assign kind name source =>
      intro result output heval
      change some (assignStepHOLExact state kind name source
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      have hstep := Option.some.inj heval
      apply assignStepHOLExact_shapeInvariant state kind name source
        (fun _ expression => evalHOLExact state expression) hvars ?_ result output hstep
      intro value hvalue
      exact evalHOLExact_isWfShapeValueHOLExact state hvars.1 hvars.2 source value hvalue
  | primitive name operator arguments =>
      intro result output heval
      change some (primitiveStepHOLExact state name operator arguments
        (fun _ expressions => evalListHOLExact state expressions)) = some (result, output) at heval
      have hstep := Option.some.inj heval
      exact primitiveStepHOLExact_shapeInvariant state name operator arguments
        (fun _ expressions => evalListHOLExact state expressions) hvars result output hstep
  | dec _ _ _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | seq _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | ite _ _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | «while» _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | call _ _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | decCall _ _ _ _ _ => simp [evalPanSemNonrecursiveHOLExact]
  | «break» =>
      intro result output heval
      simp [evalPanSemNonrecursiveHOLExact] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | «continue» =>
      intro result output heval
      simp [evalPanSemNonrecursiveHOLExact] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | annot _ _ =>
      intro result output heval
      simp [evalPanSemNonrecursiveHOLExact] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact ⟨rfl, hvars, trivial⟩
  | store address value =>
      intro result output heval
      change some (storeStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      exact storeStepHOLExact_shapeInvariant state address value
        (fun _ expression => evalHOLExact state expression) hvars result output
        (Option.some.inj heval)
  | store32 address value =>
      intro result output heval
      change some (store32StepHOLExact state address value
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      have hstep := Option.some.inj heval
      have hstruct : (store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.structs = state.structs := by
        unfold store32StepHOLExact
        repeat' (first | split | simp)
      have hlocals : (store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.locals = state.locals := by
        unfold store32StepHOLExact
        repeat' (first | split)
        all_goals rfl
      have hglobals : (store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.globals = state.globals := by
        unfold store32StepHOLExact
        repeat' (first | split)
        all_goals rfl
      have hresult : (store32StepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).1 = none ∨
          (store32StepHOLExact state address value
            (fun _ expression => evalHOLExact state expression)).1 = some .error := by
        unfold store32StepHOLExact
        repeat' (first | split)
        all_goals simp
      exact panSemExactStateVarsHOLWf_of_memoryStep state _ hstruct hlocals hglobals hresult
        hvars result output hstep
  | storeByte address value =>
      intro result output heval
      change some (storeByteStepHOLExact state address value
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      have hstep := Option.some.inj heval
      have hstruct : (storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.structs = state.structs := by
        unfold storeByteStepHOLExact
        repeat' (first | split | simp)
      have hlocals : (storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.locals = state.locals := by
        unfold storeByteStepHOLExact
        repeat' (first | split)
        all_goals rfl
      have hglobals : (storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).2.globals = state.globals := by
        unfold storeByteStepHOLExact
        repeat' (first | split)
        all_goals rfl
      have hresult : (storeByteStepHOLExact state address value
          (fun _ expression => evalHOLExact state expression)).1 = none ∨
          (storeByteStepHOLExact state address value
            (fun _ expression => evalHOLExact state expression)).1 = some .error := by
        unfold storeByteStepHOLExact
        repeat' (first | split)
        all_goals simp
      exact panSemExactStateVarsHOLWf_of_memoryStep state _ hstruct hlocals hglobals hresult
        hvars result output hstep
  | «return» expression =>
      intro result output heval
      change some (returnStepHOLExact state expression
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      exact returnStepHOLExact_shapeInvariant state expression
        (fun _ expression => evalHOLExact state expression) hvars
        (by
          intro value hvalue
          exact evalHOLExact_isWfShapeValueHOLExact state hvars.1 hvars.2
            expression value hvalue)
        result output (Option.some.inj heval)
  | «raise» exception expression =>
      intro result output heval
      change some (raiseStepHOLExact state exception expression
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      exact raiseStepHOLExact_shapeInvariant state exception expression
        (fun _ expression => evalHOLExact state expression) hvars
        (by
          intro value hvalue
          exact evalHOLExact_isWfShapeValueHOLExact state hvars.1 hvars.2
            expression value hvalue)
        result output (Option.some.inj heval)
  | tick =>
      intro result output heval
      change some (tickStepHOLExact state) = some (result, output) at heval
      exact tickStepHOLExact_shapeInvariant state hvars result output
        (Option.some.inj heval)
  | shMemLoad operator kind name address =>
      intro result output heval
      change some (shMemLoadClauseHOLExact state operator kind name address
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      cases haddr : evalHOLExact state address with
      | none =>
          simp [shMemLoadClauseHOLExact, haddr] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | some addressValue =>
          cases addressValue with
          | val addressValue =>
              cases addressValue with
              | word address =>
                  cases hlocal : lookupKvarHOLExact kind name state with
                  | none =>
                      simp [shMemLoadClauseHOLExact, haddr, hlocal] at heval
                      rcases heval with ⟨rfl, rfl⟩
                      exact ⟨rfl, hvars, trivial⟩
                  | some localValue =>
                      cases localValue with
                      | val localValue =>
                          cases localValue with
                          | word _ =>
                              have hstep : shMemLoadHOLExact state kind name address
                                  (nbOpHOL operator) = (result, output) := by
                                simpa [shMemLoadClauseHOLExact, haddr, hlocal] using heval
                              exact shMemLoadHOLExact_shapeInvariant state kind name address
                                (nbOpHOL operator) hvars result output hstep
                      | rStruct _ =>
                          simp [shMemLoadClauseHOLExact, haddr, hlocal] at heval
                          rcases heval with ⟨rfl, rfl⟩
                          exact ⟨rfl, hvars, trivial⟩
                      | nStruct _ _ =>
                          simp [shMemLoadClauseHOLExact, haddr, hlocal] at heval
                          rcases heval with ⟨rfl, rfl⟩
                          exact ⟨rfl, hvars, trivial⟩
          | rStruct _ =>
              simp [shMemLoadClauseHOLExact, haddr] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
          | nStruct _ _ =>
              simp [shMemLoadClauseHOLExact, haddr] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
  | shMemStore operator address value =>
      intro result output heval
      change some (shMemStoreClauseHOLExact state operator address value
        (fun _ expression => evalHOLExact state expression)) = some (result, output) at heval
      cases haddr : evalHOLExact state address with
      | none =>
          simp [shMemStoreClauseHOLExact, haddr] at heval
          rcases heval with ⟨rfl, rfl⟩
          exact ⟨rfl, hvars, trivial⟩
      | some addressValue =>
          cases addressValue with
          | val addressValue =>
              cases addressValue with
              | word address =>
                  cases hvalue : evalHOLExact state value with
                  | none =>
                      simp [shMemStoreClauseHOLExact, haddr, hvalue] at heval
                      rcases heval with ⟨rfl, rfl⟩
                      exact ⟨rfl, hvars, trivial⟩
                  | some storedValue =>
                      cases storedValue with
                      | val storedValue =>
                          cases storedValue with
                          | word word =>
                              have hstep : shMemStoreHOLExact state word address
                                  (nbOpHOL operator) = (result, output) := by
                                simpa [shMemStoreClauseHOLExact, haddr, hvalue] using heval
                              exact shMemStoreHOLExact_shapeInvariant state word address
                                (nbOpHOL operator) hvars result output hstep
                      | rStruct _ =>
                          simp [shMemStoreClauseHOLExact, haddr, hvalue] at heval
                          rcases heval with ⟨rfl, rfl⟩
                          exact ⟨rfl, hvars, trivial⟩
                      | nStruct _ _ =>
                          simp [shMemStoreClauseHOLExact, haddr, hvalue] at heval
                          rcases heval with ⟨rfl, rfl⟩
                          exact ⟨rfl, hvars, trivial⟩
          | rStruct _ =>
              simp [shMemStoreClauseHOLExact, haddr] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
          | nStruct _ _ =>
              simp [shMemStoreClauseHOLExact, haddr] at heval
              rcases heval with ⟨rfl, rfl⟩
              exact ⟨rfl, hvars, trivial⟩
  | extCall function configuration configurationLength array arrayLength =>
      intro result output heval
      change some (extCallStepHOLExact state
        (fun _ expression => evalHOLExact state expression)
        function configuration configurationLength array arrayLength) =
          some (result, output) at heval
      rcases hvars with ⟨hlocalsWf, hglobalsWf⟩
      have hstep := Option.some.inj heval
      let step := extCallStepHOLExact state
        (fun _ expression => evalHOLExact state expression)
        function configuration configurationLength array arrayLength
      have hstruct : step.2.structs = state.structs := by
        dsimp [step]
        unfold extCallStepHOLExact
        repeat' (first | split)
        all_goals simp [emptyLocalsHOLExact]
      have hvarsStep : panSemExactStateVarsHOLWf state.structs step.2 := by
        dsimp [step]
        unfold extCallStepHOLExact
        repeat' (first | split)
        all_goals
          first
          | (refine ⟨?_, hglobalsWf⟩
             simp [valuesHOLWf, emptyLocalsHOLExact]
             done)
          | exact ⟨hlocalsWf, hglobalsWf⟩
      have houtput : output = step.2 := by
        calc
          output = (result, output).2 := rfl
          _ = step.2 := by rw [← hstep]
      have hresult : result = step.1 := by
        calc
          result = (result, output).1 := rfl
          _ = step.1 := by rw [← hstep]
      have hresultStep : panSemResultHOLWf state.structs step.1 := by
        dsimp [step]
        unfold extCallStepHOLExact
        repeat' (first | split)
        all_goals simp [panSemResultHOLWf]
      refine ⟨?_, ?_, ?_⟩
      · rw [houtput]
        exact hstruct
      · rw [houtput]
        exact hvarsStep
      · rw [hresult]
        exact hresultStep

private theorem evalPanSemNonrecursiveHOLFinite_shapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (hvars : panSemStateVarsHOLWf state.structs state) (program : ProgHOL width) :
    ∀ result output,
      PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite state program =
        some (result, output) →
        output.structs = state.structs ∧ panSemStateVarsHOLWf state.structs output ∧
          panSemResultHOLWf state.structs result := by
  intro result output heval
  let exactState := state.toExact
  letI : DecidablePred exactState.memaddrs := by
    simpa [exactState, PanSemStateFiniteExact.toExact] using
      (inferInstance : DecidablePred state.memaddrs)
  letI : DecidablePred exactState.shMemaddrs := by
    simpa [exactState, PanSemStateFiniteExact.toExact] using
      (inferInstance : DecidablePred state.shMemaddrs)
  have hvarsExact : panSemExactStateVarsHOLWf exactState.structs exactState := by
    simpa [panSemStateVarsHOLWf, panSemExactStateVarsHOLWf, PanSemStateFiniteExact.toExact,
      valuesHOLWf] using hvars
  have hprojection := congrArg
    (Option.map fun pair : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
      (pair.1, pair.2.toExact)) heval
  rw [PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite_toExact] at hprojection
  have hExactEval : evalPanSemNonrecursiveHOLExact program exactState =
      some (result, output.toExact) := by
    simpa [exactState] using hprojection
  have hInvariant := evalPanSemNonrecursiveHOLExact_shapeInvariant program exactState
    hvarsExact result output.toExact hExactEval
  refine ⟨?_, ?_, hInvariant.2.2⟩
  · simpa [PanSemStateFiniteExact.toExact] using hInvariant.1
  · simpa [panSemStateVarsHOLWf, panSemExactStateVarsHOLWf,
      PanSemStateFiniteExact.toExact, valuesHOLWf] using hInvariant.2.1

private theorem panSemStateVarsHOLWf_emptyLocals {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (h : panSemStateVarsHOLWf state.structs state) :
    panSemStateVarsHOLWf state.structs (PanSemStateFiniteExact.emptyLocalsHOLFinite state) := by
  exact ⟨valuesHOLWf_empty state.structs, h.2⟩

private theorem panSemStateVarsHOLWf_setVar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setVarHOLFinite name value state) := by
  exact ⟨valuesHOLWf_update state.structs state.locals name value h.1 hvalue, h.2⟩

private theorem panSemStateVarsHOLWf_setGlobal {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (name : MlS) (value : ValueHOL width)
    (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setGlobalHOLFinite name value state) := by
  exact ⟨h.1, valuesHOLWf_update state.structs state.globals name value h.2 hvalue⟩

private theorem panSemStateVarsHOLWf_setKvar {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS)
    (value : ValueHOL width) (h : panSemStateVarsHOLWf state.structs state)
    (hvalue : isWfShapeValueHOLExact state.structs value = true) :
    panSemStateVarsHOLWf state.structs
      (PanSemStateFiniteExact.setKvarHOLFinite kind name value state) := by
  cases kind
  · simpa [panSemStateVarsHOLWf, PanSemStateFiniteExact.setKvarHOLFinite] using
      panSemStateVarsHOLWf_setVar state name value h hvalue
  · simpa [panSemStateVarsHOLWf, PanSemStateFiniteExact.setKvarHOLFinite] using
      panSemStateVarsHOLWf_setGlobal state name value h hvalue

private theorem panSemStateVarsHOLWf_restoreLocal {width : Nat} {σ : Type} [NeZero width]
    (after caller : PanSemStateFiniteExact width σ) (name : MlS)
    (hafter : panSemStateVarsHOLWf after.structs after)
    (hcaller : valuesHOLWf after.structs caller.locals.lookup) :
    valuesHOLWf after.structs
        (HolFiniteMapExact.resVarEq after.locals
          (name, caller.locals.lookup name)).lookup ∧
      valuesHOLWf after.structs after.globals.lookup := by
  exact ⟨valuesHOLWf_resVarEq after.structs after.locals caller.locals name
      hafter.1 hcaller, hafter.2⟩

namespace PanSemStateFiniteExact

/-- Assign clauses change only variable maps, never the structural context. -/
@[simp] theorem assignStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (assignStepHOLExact state kind name source evalExpression).2.structs = state.structs := by
  unfold assignStepHOLExact
  cases hvalue : evalExpression state source with
  | none => rfl
  | some value =>
      by_cases hvalid : isValidValueHOLExact state kind name value = true
      · cases kind <;> simp [hvalid, setKvarHOLExact]
      · simp [hvalid]

/-- Primitive clauses change only local variables, never the structural
    context. -/
@[simp] theorem primitiveStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (name : MlS)
    (operator : PrimOp) (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width))) :
    (primitiveStepHOLExact state name operator arguments evalExpressions).2.structs =
      state.structs := by
  unfold primitiveStepHOLExact
  cases hvalues : evalExpressions state arguments with
  | none => simp
  | some values =>
      cases hprimop : panPrimopHOLExact operator values with
      | none => simp [hprimop]
      | some value =>
          by_cases hvalid : isValidValueHOLExact state .local name value = true
          · simp [hprimop, hvalid, setVarHOLExact]
          · simp [hprimop, hvalid]

/-- Store clauses update memory only, never the structural context. -/
@[simp] theorem storeStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (destination source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeStepHOLExact state destination source evalExpression).2.structs = state.structs := by
  unfold storeStepHOLExact
  repeat' (first | split | simp)

/-- Store32 clauses update memory only, never the structural context. -/
@[simp] theorem store32StepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (store32StepHOLExact state address value evalExpression).2.structs = state.structs := by
  unfold store32StepHOLExact
  repeat' (first | split | simp)

/-- StoreByte clauses update memory only, never the structural context. -/
@[simp] theorem storeByteStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (storeByteStepHOLExact state address value evalExpression).2.structs = state.structs := by
  unfold storeByteStepHOLExact
  repeat' (first | split | simp)

/-- ExtCall clauses update memory, FFI, or locals, but not the structural
    context. -/
@[simp] theorem extCallStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.structs =
      state.structs := by
  unfold extCallStepHOLExact
  all_goals (repeat' (first | split))
  all_goals simp [emptyLocalsHOLExact]

/-- Tick clauses update clock or locals, but not the structural context. -/
@[simp] theorem tickStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) :
    (tickStepHOLExact state).2.structs = state.structs := by
  unfold tickStepHOLExact
  split <;> simp [emptyLocalsHOLExact, decClockHOLExact]

/-- Shared-memory load clauses preserve the structural context. -/
@[simp] theorem shMemLoadClauseHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.structs =
      state.structs := by
  unfold shMemLoadClauseHOLExact
  unfold shMemLoadHOLExact
  all_goals (repeat' (first | split))
  all_goals simp [emptyLocalsHOLExact, setKvarHOLExact]
  all_goals cases kind <;> rfl

/-- Shared-memory store clauses preserve the structural context. -/
@[simp] theorem shMemStoreClauseHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.structs =
      state.structs := by
  unfold shMemStoreClauseHOLExact
  unfold shMemStoreHOLExact
  all_goals (repeat' (first | split))
  all_goals simp

/-- Return clauses clear locals but preserve the structural context. -/
@[simp] theorem returnStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (returnStepHOLExact state expression evalExpression).2.structs = state.structs := by
  unfold returnStepHOLExact
  cases hvalue : evalExpression state expression with
  | none => simp
  | some value =>
      by_cases hsize :
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
              (shapeOfHOLExact value) ≤ 32
      · simp [hsize, emptyLocalsHOLExact]
      · simp [hsize]

/-- Raise clauses clear locals but preserve the structural context. -/
@[simp] theorem raiseStepHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) (exception : MlS)
    (expression : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (raiseStepHOLExact state exception expression evalExpression).2.structs = state.structs := by
  unfold raiseStepHOLExact
  cases hvalue : evalExpression state expression with
  | none => simp
  | some value =>
      cases hshape : state.eshapes exception with
      | none => simp
      | some shape =>
          by_cases heq : shapeEqHOL (shapeOfHOLExact value) shape = true
          · by_cases hsize :
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL state.structs
                    (shapeOfHOLExact value) ≤ 32
            · simp [heq, hsize, emptyLocalsHOLExact]
            · simp [heq, hsize]
          · simp [heq]

/-- Every exact nonrecursive clause leaves the structural field unchanged. -/
theorem evalPanSemNonrecursiveHOLExact_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (result : Option (PanSemResultExact width)) (output : PanSemStateExact width σ)
    (heval : evalPanSemNonrecursiveHOLExact program state = some (result, output)) :
    output.structs = state.structs := by
  have hmap :
      (evalPanSemNonrecursiveHOLExact program state).map
          (fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ =>
            pair.2.structs) =
        (evalPanSemNonrecursiveHOLExact program state).map
          (fun _ : Option (PanSemResultExact width) × PanSemStateExact width σ =>
            state.structs) := by
    cases program <;> simp [evalPanSemNonrecursiveHOLExact]
  have hproj := congrArg
    (Option.map fun pair : Option (PanSemResultExact width) × PanSemStateExact width σ =>
      pair.2.structs) heval
  rw [hmap, heval, Option.map_some] at hproj
  exact (Option.some.inj hproj).symm

/-- Finite-support rendering preserves the structural context in every
    nonrecursive clause. -/
theorem evalPanSemNonrecursiveHOLFinite_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] [DecidablePred state.shMemaddrs]
    (program : ProgHOL width) (result : Option (PanSemResultExact width))
    (output : PanSemStateFiniteExact width σ)
    (heval : evalPanSemNonrecursiveHOLFinite state program = some (result, output)) :
    output.structs = state.structs := by
  unfold evalPanSemNonrecursiveHOLFinite at heval
  split at heval
  · simp at heval
  · rename_i exactOutput hexact
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    change exactOutput.2.structs = state.structs
    simpa [PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact] using
      evalPanSemNonrecursiveHOLExact_structs_eq program state.toExact
        exactOutput.1 exactOutput.2 hexact

/-- The clause-shaped finite-support evaluator preserves the source structural
    context on every successful evaluation. -/
theorem evalPanSemRecursiveCallFiniteContext_structs_eq {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width) (context : FiniteEvalContext width σ) :
    ∀ result output,
      evalPanSemRecursiveCallFiniteContext program context = some (result, output) →
        output.state.structs = context.state.structs := by
  fun_induction evalPanSemRecursiveCallFiniteContext program context
  case case1 =>
    simp
  case case3 =>
    rename_i ihBody
    rename_i bodyEval
    rename_i restored
    rename_i postContext
    rename_i result
    rename_i bodyContext
    rename_i bodyState
    rename_i shapeEq
    rename_i initEval
    rename_i value
    rename_i initializer
    rename_i body
    rename_i shape
    rename_i name
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody result postContext restored
    simpa [FiniteEvalContext.withState, bodyEval, bodyContext, bodyState,
      setVarHOLFinite,
      PanSemStateFiniteExact.setVarHOLFinite] using hbody
  case case4 =>
    simp
  case case6 =>
    rename_i ihSecond
    rename_i ihFirst
    rename_i fixedContext
    rename_i fixed
    rename_i firstEval
    rename_i postContext
    rename_i second
    rename_i first
    rename_i state
    rename_i context
    intro result output heval
    have hfirst := ihFirst none postContext firstEval
    have hsecond := ihSecond result output heval
    calc
      output.state.structs = fixedContext.state.structs := hsecond
      _ = fixed.2.structs := rfl
      _ = state.structs := by simpa [fixed, fixClockHOLFinite, state] using hfirst
  case case7 =>
    rename_i ihFirst
    rename_i fixedContext
    rename_i fixed
    rename_i firstEval
    rename_i val
    rename_i postContext
    rename_i second
    rename_i first
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hfirst := ihFirst (some val) postContext firstEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, fixed, fixClockHOLFinite, state]
      using hfirst
  case case10 =>
    simp
  case case11 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case12 =>
    simp
  case case13 =>
    rename_i ihLoop
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    have hbody := ihBody (some .continue) postContext bodyEval
    have hloop := ihLoop result output heval
    calc
      output.state.structs = fixedContext.state.structs := hloop
      _ = entry.structs := by
        simp [FiniteEvalContext.withState, fixedContext, fixed,
          fixClockHOLFinite, entryContext, hbody]
      _ = state.structs := by simp [entry, decClockHOLFinite]
      _ = context.state.structs := rfl
  case case14 =>
    rename_i ihLoop
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    have hbody := ihBody none postContext bodyEval
    have hloop := ihLoop result output heval
    calc
      output.state.structs = fixedContext.state.structs := hloop
      _ = entry.structs := by
        simp [FiniteEvalContext.withState, fixedContext, fixed,
          fixClockHOLFinite, entryContext, hbody]
      _ = state.structs := rfl
      _ = context.state.structs := rfl
  case case15 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some .break) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, fixed,
      fixClockHOLFinite, entryContext, entry, decClockHOLFinite, state] using hbody
  case case16 =>
    rename_i ihBody
    rename_i hbreak
    rename_i hnone
    rename_i hcontinue
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i bodyResult
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody bodyResult postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, fixed,
      fixClockHOLFinite, entryContext, entry, decClockHOLFinite, state] using hbody
  case case17 =>
    simp
  case case18 =>
    simp
  case case19 =>
    simp
  case case20 =>
    simp
  case case21 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case22 =>
    simp
  case case23 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody none postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite] using hbody
  case case24 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some .break) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case25 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some .continue) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case26 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite, FiniteEvalContext.emptyLocalsContextHOLFinite,
      state, emptyLocalsHOLFinite] using hbody
  case case27 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i infoTail
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite,
      callRestoreLocalsContextHOLFinite] using hbody
  case case29 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hvalid
    rename_i infoTail
    rename_i name
    rename_i kind
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case30 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case31 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.exception exceptionId value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite, emptyLocalsHOLFinite] using hbody
  case case32 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i infoTail
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.exception exceptionId value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite, emptyLocalsHOLFinite] using hbody
  case case33 =>
    rename_i ihHandler
    rename_i ihBody
    rename_i handlerContext
    rename_i fixedContext
    rename_i bodyEval
    rename_i shapeLookup
    rename_i hvalid
    rename_i shape
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    have hbody := ihBody (some (.exception handlerId value)) postContext bodyEval
    have hhandler := ihHandler result output heval
    let handlerState := handlerStateHOLFinite context fixedContext handlerVar value
    calc
      output.state.structs = handlerContext.state.structs := hhandler
      _ = handlerState.structs := rfl
      _ = fixedContext.state.structs := by
        simp [handlerState, handlerStateHOLFinite, setVarHOLFinite,
          fixedContext, callFixedContextHOLFinite]
      _ = entry.structs := by
        simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
          fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
          callEntryContextHOLFinite] using hbody
      _ = state.structs := by simp [entry, callEntryStateHOLFinite]
      _ = context.state.structs := rfl
  case case34 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i shapeLookup
    rename_i hvalid
    rename_i shape
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.exception handlerId value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case35 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshapeLookup
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.exception handlerId value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case36 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hneq
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.exception exceptionId value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite, emptyLocalsHOLFinite] using hbody
  case case37 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hexception
    rename_i hreturned
    rename_i hcontinue
    rename_i hbreak
    rename_i other
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some other) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      callEntryContextHOLFinite, emptyLocalsHOLFinite] using hbody
  case case38 =>
    simp
  case case39 =>
    simp
  case case40 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case41 =>
    simp
  case case42 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody none postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case43 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some .break) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case44 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some .continue) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case45 =>
    simp
  case case46 =>
    rename_i ihContinuation
    rename_i ihBody
    rename_i continuationEval
    rename_i continuationContext
    rename_i fixedContext
    rename_i bodyEval
    rename_i restored
    rename_i postContext
    rename_i continuationResult
    rename_i hshape
    rename_i value
    rename_i bodyPostContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i continuation
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) bodyPostContext bodyEval
    have hcontinuation := ihContinuation continuationResult postContext continuationEval
    simpa [FiniteEvalContext.withState, restored, continuationContext, callContinuationContextHOLFinite,
      handlerStateHOLFinite, setVarHOLFinite, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      state, hbody] using hcontinuation
  case case47 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i continuation
    rename_i resultName
    rename_i shape
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some (.returned value)) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody
  case case48 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hreturned
    rename_i hcontinue
    rename_i hbreak
    rename_i other
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i continuation
    rename_i resultName
    rename_i shape
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hbody := ihBody (some other) postContext bodyEval
    simpa [FiniteEvalContext.withState, FiniteEvalContext.withState_state, fixedContext, callFixedContextHOLFinite,
      fixClockHOLFinite, entryContext, entry, callEntryStateHOLFinite,
      emptyLocalsHOLFinite] using hbody
  case case49 =>
    simp
  case case50 =>
    simp
  case case51 =>
    simp
  case case52 =>
    simp
  case case53 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case54 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case55 =>
    simp
  case case56 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case57 =>
    simp
  case case58 =>
    simp
  case case59 =>
    simp
  case case60 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    rfl
  case case61 =>
    simp
  case case62 =>
    simp
  case case28 =>
    intro result output heval
    try rcases heval with ⟨rfl, rfl⟩
    cases (show VarKind from by assumption) <;>
      try simp_all (config := { zetaDelta := true })
        [FiniteEvalContext.withState, callFixedContextHOLFinite,
          callEntryStateHOLFinite,
          callEntryContextHOLFinite, fixClockHOLFinite,
          setVarHOLFinite, setKvarHOLFinite,
          callSetKvarContextHOLFinite,
          setGlobalHOLFinite, PanSemStateFiniteExact.toExact]
  case case66 =>
    let ctx : FiniteEvalContext width σ := by assumption
    intro result output heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred ctx.state.memaddrs := ctx.memaddrsDecidable
    letI : DecidablePred ctx.state.shMemaddrs := ctx.shMemaddrsDecidable
    simp only [FiniteEvalContext.withState]
    apply evalPanSemNonrecursiveHOLFinite_structs_eq
    assumption
  all_goals
    intro result output heval <;>
      (try rcases heval with ⟨rfl, rfl⟩) <;>
      (set_option linter.unusedSimpArgs false in simp_all (config := { zetaDelta := true })
        [FiniteEvalContext.withState, fixClockHOLFinite, decClockHOLFinite,
          emptyLocalsHOLFinite, setVarHOLFinite,
          PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact])

/-- A successful finite-support `Return` result has a well-formed payload when
    all values initially readable from locals and globals are well-formed. -/
theorem evalPanSemFiniteReturnPayloadWf {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hlocals : ∀ name value, context.state.locals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (hglobals : ∀ name value, context.state.globals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (expression : ExpHOL width) (value : ValueHOL width)
    (output : FiniteEvalContext width σ)
    (heval : evalPanSemRecursiveCallFiniteContext (.return expression : ProgHOL width) context =
      some (some (.returned value), output)) :
    isWfShapeValueHOLExact context.state.structs value = true := by
  letI : DecidablePred context.state.toExact.memaddrs := by
    simpa [PanSemStateFiniteExact.toExact] using context.memaddrsDecidable
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  cases hvalue : evalHOLExact context.state.toExact expression with
  | none => simp [hvalue] at heval
  | some returned =>
      by_cases hsize :
          Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
            (shapeOfHOLExact returned) ≤ 32
      · have hpayload : returned = value := by
          have hproject := congrArg (Option.map Prod.fst) heval
          simp [hvalue, hsize] at hproject
          exact hproject
        subst value
        exact evalHOLExact_isWfShapeValueHOLExact context.state.toExact
          (by simpa [PanSemStateFiniteExact.toExact] using hlocals)
          (by simpa [PanSemStateFiniteExact.toExact] using hglobals)
          expression returned hvalue
      · simp [hvalue, hsize] at heval

/-- A successful finite-support `Raise` result has a well-formed payload when
    all values initially readable from locals and globals are well-formed. -/
theorem evalPanSemFiniteRaisePayloadWf {width : Nat} {σ : Type} [NeZero width]
    (context : FiniteEvalContext width σ)
    (hlocals : ∀ name value, context.state.locals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (hglobals : ∀ name value, context.state.globals.lookup name = some value →
      isWfShapeValueHOLExact context.state.structs value = true)
    (exception : MlS) (expression : ExpHOL width) (value : ValueHOL width)
    (output : FiniteEvalContext width σ)
    (heval : evalPanSemRecursiveCallFiniteContext (.raise exception expression : ProgHOL width) context =
      some (some (.exception exception value), output)) :
    isWfShapeValueHOLExact context.state.structs value = true := by
  letI : DecidablePred context.state.toExact.memaddrs := by
    simpa [PanSemStateFiniteExact.toExact] using context.memaddrsDecidable
  rw [evalPanSemRecursiveCallFiniteContext.eq_def] at heval
  cases hvalue : evalHOLExact context.state.toExact expression with
  | none => simp [hvalue] at heval
  | some raised =>
      cases hshape : context.state.eshapes.lookup exception with
      | none => simp [hvalue, hshape] at heval
      | some shape =>
          by_cases heq : shapeEqHOL (shapeOfHOLExact raised) shape
          · by_cases hsize :
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL context.state.structs
                  (shapeOfHOLExact raised) ≤ 32
            · have hpayload : raised = value := by
                have hproject := congrArg (Option.map Prod.fst) heval
                simp [hvalue, hshape, heq, hsize] at hproject
                exact hproject
              subst value
              exact evalHOLExact_isWfShapeValueHOLExact context.state.toExact
                (by simpa [PanSemStateFiniteExact.toExact] using hlocals)
                (by simpa [PanSemStateFiniteExact.toExact] using hglobals)
                expression raised hvalue
            · simp [hvalue, hshape, heq, hsize] at heval
          · simp [hvalue, hshape, heq] at heval

theorem evalPanSemRecursiveCallFiniteContext_shapeInvariant
    {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (sourceContext : FiniteEvalContext width σ)
    (hvars : panSemStateVarsHOLWf sourceContext.state.structs sourceContext.state) :
    ∀ result output,
      evalPanSemRecursiveCallFiniteContext program sourceContext = some (result, output) →
        output.state.structs = sourceContext.state.structs ∧
        panSemStateVarsHOLWf sourceContext.state.structs output.state ∧
        panSemResultHOLWf sourceContext.state.structs result := by
  fun_induction evalPanSemRecursiveCallFiniteContext program sourceContext
  case case3 =>
    rename_i ihBody
    rename_i bodyEval
    rename_i restored
    rename_i postContext
    rename_i bodyResult
    rename_i bodyContext
    rename_i bodyState
    rename_i shapeEq
    rename_i initEval
    rename_i value
    rename_i initializer
    rename_i body
    rename_i shape
    rename_i name
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := by
      simpa [state] using context.memaddrsDecidable
    have hvalue : isWfShapeValueHOLExact state.structs value = true :=
      evalHOLFinite_isWf state hvars.1 hvars.2 body value initEval
    have hbodyVars := panSemStateVarsHOLWf_setVar state name value hvars hvalue
    have hbody := ihBody hbodyVars bodyResult postContext restored
    rcases hbody with ⟨hstructs, hpostVars, hresult⟩
    have hstructs' : postContext.state.structs = state.structs := by
      simpa [bodyContext, bodyState, setVarHOLFinite,
        PanSemStateFiniteExact.setVarHOLFinite] using hstructs
    have hpostVars' : panSemStateVarsHOLWf state.structs postContext.state := by
      simpa [bodyContext, bodyState, setVarHOLFinite,
        PanSemStateFiniteExact.setVarHOLFinite] using hpostVars
    have hpostVarsAtPost : panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      simpa [hstructs'] using hpostVars'
    have hcallerLocals : valuesHOLWf postContext.state.structs state.locals.lookup := by
      rw [hstructs']
      exact hvars.1
    have hrestoredVars : panSemStateVarsHOLWf state.structs bodyEval := by
      simpa [bodyEval, panSemStateVarsHOLWf, hstructs'] using
        panSemStateVarsHOLWf_restoreLocal postContext.state state name
          hpostVarsAtPost hcallerLocals
    refine ⟨?_, ?_, ?_⟩
    · simp [state, FiniteEvalContext.withState, bodyEval, hstructs']
    · simpa [FiniteEvalContext.withState, bodyEval] using hrestoredVars
    · simpa [bodyContext, bodyState, setVarHOLFinite,
        PanSemStateFiniteExact.setVarHOLFinite] using hresult
  case case4 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case1 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case2 =>
    intro result output heval
    simp at heval
  case case5 =>
    intro result output heval
    simp at heval
  case case8 =>
    rename_i ihBranch
    exact ihBranch hvars
  case case9 =>
    rename_i ihBranch
    exact ihBranch hvars
  case case6 =>
    rename_i ihSecond
    rename_i ihFirst
    rename_i fixedContext
    rename_i fixed
    rename_i firstEval
    rename_i postContext
    rename_i second
    rename_i first
    rename_i state
    rename_i context
    intro result output heval
    have hfirst := ihFirst hvars none postContext firstEval
    have hfirstVarsAtPost : panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hfirst.1]
      exact hfirst.2.1
    have hfixedVars : panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hfirstVarsAtPost
    have hsecond := ihSecond hfixedVars result output heval
    refine ⟨?_, ?_, ?_⟩
    · calc
        output.state.structs = fixedContext.state.structs := hsecond.1
        _ = state.structs := by
          simpa [fixedContext, fixed, fixClockHOLFinite] using hfirst.1
        _ = context.state.structs := rfl
    · simpa [fixedContext, fixed, fixClockHOLFinite, hfirst.1] using hsecond.2.1
    · simpa [fixedContext, fixed, fixClockHOLFinite, hfirst.1] using hsecond.2.2
  case case7 =>
    rename_i ihFirst
    rename_i fixedContext
    rename_i fixed
    rename_i firstEval
    rename_i val
    rename_i postContext
    rename_i second
    rename_i first
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hfirst := ihFirst hvars (some val) postContext firstEval
    have hfirstVarsAtPost : panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hfirst.1]
      exact hfirst.2.1
    have hfixedVars : panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hfirstVarsAtPost
    have hfixedVarsAtOrig : panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [fixedContext, fixed, fixClockHOLFinite, hfirst.1] using hfixedVars
    refine ⟨?_, hfixedVarsAtOrig, ?_⟩
    · simpa [fixedContext, fixed, fixClockHOLFinite] using hfirst.1
    · exact hfirst.2.2
  case case10 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case11 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, panSemStateVarsHOLWf_emptyLocals _ hvars,
      by simp [panSemResultHOLWf]⟩
  case case12 =>
    simp
  case case13 =>
    rename_i ihLoop
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    have hentryVars : panSemStateVarsHOLWf entryContext.state.structs entryContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, entryContext, entry,
        decClockHOLFinite] using hvars
    have hbody := ihBody hentryVars (some .continue) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hloop := ihLoop hfixedVars result output heval
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, fixed, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by
          simp [entryContext, entry, decClockHOLFinite, state]
    refine ⟨?_, ?_, ?_⟩
    · calc
        output.state.structs = fixedContext.state.structs := hloop.1
        _ = context.state.structs := hfixedStructs
    · simpa [hfixedStructs] using hloop.2.1
    · simpa [hfixedStructs] using hloop.2.2
  case case14 =>
    rename_i ihLoop
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    have hentryVars : panSemStateVarsHOLWf entryContext.state.structs entryContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, entryContext, entry,
        decClockHOLFinite] using hvars
    have hbody := ihBody hentryVars none postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hloop := ihLoop hfixedVars result output heval
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, fixed, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by
          simp [entryContext, entry, decClockHOLFinite, state]
    refine ⟨?_, ?_, ?_⟩
    · calc
        output.state.structs = fixedContext.state.structs := hloop.1
        _ = context.state.structs := hfixedStructs
    · simpa [hfixedStructs] using hloop.2.1
    · simpa [hfixedStructs] using hloop.2.2
  case case15 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hentryVars : panSemStateVarsHOLWf entryContext.state.structs entryContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, entryContext, entry,
        decClockHOLFinite] using hvars
    have hbody := ihBody hentryVars (some .break) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, fixed, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by
          simp [entryContext, entry, decClockHOLFinite, state]
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case31 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception exceptionId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext,
        callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hvalueWf : isWfShapeValueHOLExact context.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite,
        callEntryContextHOLFinite] using hbody.2.2
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by
      simpa [panSemResultHOLWf] using hvalueWf⟩
  case case32 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i infoTail
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception exceptionId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hvalueWf : isWfShapeValueHOLExact context.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite,
        callEntryContextHOLFinite] using hbody.2.2
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by
      simpa [panSemResultHOLWf] using hvalueWf⟩
  case case41 =>
    intro result output heval
    simp_all
  case case33 =>
    rename_i ihHandler
    rename_i ihBody
    rename_i handlerContext
    rename_i fixedContext
    rename_i bodyEval
    rename_i shapeLookup
    rename_i hvalid
    rename_i shape
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception handlerId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hvalueWf : isWfShapeValueHOLExact context.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    let handlerBase : PanSemStateFiniteExact width σ :=
      { fixedContext.state with locals := state.locals }
    have hhandlerBaseStructs : handlerBase.structs = context.state.structs := by
      simpa [handlerBase] using hfixedStructs
    have hhandlerBaseVars : panSemStateVarsHOLWf handlerBase.structs handlerBase := by
      refine ⟨?_, ?_⟩
      · simpa [handlerBase, hfixedStructs] using hvars.1
      · simpa [handlerBase] using hfixedVars.2
    have hsetHandler :
        panSemStateVarsHOLWf handlerBase.structs
          (PanSemStateFiniteExact.setVarHOLFinite handlerVar value handlerBase) :=
      panSemStateVarsHOLWf_setVar handlerBase handlerVar value hhandlerBaseVars
        (by simpa [hhandlerBaseStructs] using hvalueWf)
    let handlerState := handlerStateHOLFinite context fixedContext handlerVar value
    have hhandlerVars : panSemStateVarsHOLWf context.state.structs handlerState := by
      rw [← hhandlerBaseStructs]
      simpa [handlerState, handlerStateHOLFinite, handlerBase, setVarHOLFinite] using hsetHandler
    have hhandlerStateStructs : handlerState.structs = context.state.structs := by
      simpa [handlerState, handlerStateHOLFinite, setVarHOLFinite] using hhandlerBaseStructs
    have hhandlerStructs : handlerContext.state.structs = context.state.structs := by
      simpa [handlerContext, FiniteEvalContext.withState, FiniteEvalContext.withState_state,
        callContinuationContextHOLFinite] using hhandlerStateStructs
    have hhandlerVarsAtContext :
        panSemStateVarsHOLWf handlerContext.state.structs handlerContext.state := by
      simpa [handlerContext, FiniteEvalContext.withState, FiniteEvalContext.withState_state,
        callContinuationContextHOLFinite, handlerState, hhandlerStateStructs] using hhandlerVars
    have hhandler := ihHandler hhandlerVarsAtContext result output heval
    refine ⟨?_, ?_, ?_⟩
    · calc
        output.state.structs = handlerContext.state.structs := hhandler.1
        _ = context.state.structs := hhandlerStructs
    · simpa [hhandlerStructs] using hhandler.2.1
    · simpa [hhandlerStructs] using hhandler.2.2
  case case38 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case39 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case40 =>
    let ctx : FiniteEvalContext width σ := by assumption
    have hvarsCtx : panSemStateVarsHOLWf ctx.state.structs ctx.state := by assumption
    have hempty := panSemStateVarsHOLWf_emptyLocals ctx.state hvarsCtx
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨by rfl,
      by simpa [FiniteEvalContext.withState] using hempty,
      by simp [panSemResultHOLWf]⟩
  case case42 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars none postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case43 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some .break) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case44 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some .continue) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case45 =>
    intro result output heval
    simp_all
  case case46 =>
    rename_i ihContinuation
    rename_i ihBody
    rename_i continuationEval
    rename_i continuationContext
    rename_i fixedContext
    rename_i bodyEval
    rename_i restored
    rename_i postContext
    rename_i continuationResult
    rename_i hshape
    rename_i value
    rename_i bodyPostContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned value)) bodyPostContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf bodyPostContext.state.structs bodyPostContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = bodyPostContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hvalueWf : isWfShapeValueHOLExact context.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    let continuationBase : PanSemStateFiniteExact width σ :=
      { fixedContext.state with locals := state.locals }
    let continuationState := handlerStateHOLFinite context fixedContext resultName value
    have hcontinuationBaseStructs : continuationBase.structs = context.state.structs := by
      simpa [continuationBase] using hfixedStructs
    have hcontinuationBaseVars :
        panSemStateVarsHOLWf continuationBase.structs continuationBase := by
      refine ⟨?_, ?_⟩
      · simpa [continuationBase, hfixedStructs] using hvars.1
      · simpa [continuationBase] using hfixedVars.2
    have hcontinuationStateVars :
        panSemStateVarsHOLWf continuationState.structs continuationState := by
      have hset := panSemStateVarsHOLWf_setVar continuationBase resultName value
        hcontinuationBaseVars (by simpa [hcontinuationBaseStructs] using hvalueWf)
      simpa [continuationState, continuationBase, handlerStateHOLFinite, setVarHOLFinite] using hset
    have hcontinuationVarsAtContext :
        panSemStateVarsHOLWf continuationContext.state.structs continuationContext.state := by
      simpa [continuationContext, callContinuationContextHOLFinite, FiniteEvalContext.withState, continuationState, handlerStateHOLFinite, setVarHOLFinite] using hcontinuationStateVars
    have hcontinuation :=
      ihContinuation hcontinuationVarsAtContext continuationResult postContext continuationEval
    have hcontinuationStateStructs :
        continuationState.structs = continuationBase.structs := by
      simp [continuationState, continuationBase, handlerStateHOLFinite, setVarHOLFinite]
    have hcontinuationContextStructs :
        continuationContext.state.structs = context.state.structs := by
      calc
        continuationContext.state.structs = continuationState.structs := rfl
        _ = continuationBase.structs := hcontinuationStateStructs
        _ = context.state.structs := hcontinuationBaseStructs
    have hpostStructs : postContext.state.structs = context.state.structs := by
      calc
        postContext.state.structs = continuationContext.state.structs := hcontinuation.1
        _ = context.state.structs := hcontinuationContextStructs
    have hpostVars :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hcontinuation.1]
      exact hcontinuation.2.1
    have hcallerLocals : valuesHOLWf postContext.state.structs state.locals.lookup := by
      simpa [hpostStructs] using hvars.1
    have hrestoredVarsPair :=
      panSemStateVarsHOLWf_restoreLocal postContext.state state resultName
        hpostVars hcallerLocals
    have hrestoredVars : panSemStateVarsHOLWf context.state.structs restored := by
      refine ⟨?_, ?_⟩
      · simpa [restored, hpostStructs] using hrestoredVarsPair.1
      · simpa [restored, hpostStructs] using hrestoredVarsPair.2
    have hresultWf : panSemResultHOLWf context.state.structs continuationResult := by
      simpa [hcontinuationContextStructs] using hcontinuation.2.2
    exact ⟨by simpa [restored, FiniteEvalContext.withState] using hpostStructs,
      by simpa [restored, FiniteEvalContext.withState] using hrestoredVars,
      hresultWf⟩
  case case47 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case48 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hreturned
    rename_i hcontinue
    rename_i hbreak
    rename_i other
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i continuation
    rename_i arguments
    rename_i function
    rename_i shape
    rename_i resultName
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some other) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hresultWf : panSemResultHOLWf context.state.structs (some other) := by
      simpa [entryContext, FiniteEvalContext.withState, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    exact ⟨hfixedStructs, hfixedVarsAtOrig, hresultWf⟩
  case case49 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case50 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case51 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case52 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case53 =>
    let ctx : FiniteEvalContext width σ := by assumption
    have hvarsCtx : panSemStateVarsHOLWf ctx.state.structs ctx.state := by assumption
    have hempty := panSemStateVarsHOLWf_emptyLocals ctx.state hvarsCtx
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, by simpa [FiniteEvalContext.withState] using hempty,
      by simp [panSemResultHOLWf]⟩
  case case54 =>
    let ctx : FiniteEvalContext width σ := by assumption
    have hvarsCtx : panSemStateVarsHOLWf ctx.state.structs ctx.state := by assumption
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl,
      by simpa [panSemStateVarsHOLWf, PanSemStateFiniteExact.decClockHOLFinite] using hvarsCtx,
      by simp [panSemResultHOLWf]⟩
  case case55 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case56 =>
    let ctx : FiniteEvalContext width σ := by assumption
    let expression : ExpHOL width := by assumption
    let value : ValueHOL width := by assumption
    letI : DecidablePred ctx.state.memaddrs := ctx.memaddrsDecidable
    have hevalValue : ctx.state.evalHOLFinite expression = some value := by assumption
    have hvalueWf := evalHOLFinite_isWf ctx.state hvars.1 hvars.2
      expression value hevalValue
    have hempty := panSemStateVarsHOLWf_emptyLocals ctx.state hvars
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, by simpa [FiniteEvalContext.withState] using hempty,
      by simpa [panSemResultHOLWf, ctx, value] using hvalueWf⟩
  case case57 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case58 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case59 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case60 =>
    let ctx : FiniteEvalContext width σ := by assumption
    let expression : ExpHOL width := by assumption
    let value : ValueHOL width := by assumption
    letI : DecidablePred ctx.state.memaddrs := ctx.memaddrsDecidable
    have hevalValue : ctx.state.evalHOLFinite expression = some value := by assumption
    have hvalueWf := evalHOLFinite_isWf ctx.state hvars.1 hvars.2
      expression value hevalValue
    have hempty := panSemStateVarsHOLWf_emptyLocals ctx.state hvars
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, by simpa [FiniteEvalContext.withState] using hempty,
      by simpa [panSemResultHOLWf, ctx, value] using hvalueWf⟩
  case case61 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case62 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case63 =>
    let ctx : FiniteEvalContext width σ := by assumption
    let state : PanSemStateFiniteExact width σ := ctx.state
    let size : OpSize := by assumption
    let kind : VarKind := by assumption
    let name : MlS := by assumption
    let address : ExpHOL width := by assumption
    let exactState := state.toExact
    letI : DecidablePred exactState.memaddrs := by
      simpa [exactState, PanSemStateFiniteExact.toExact] using ctx.memaddrsDecidable
    letI : DecidablePred exactState.shMemaddrs := by
      simpa [exactState, PanSemStateFiniteExact.toExact] using ctx.shMemaddrsDecidable
    have hvarsExact : panSemExactStateVarsHOLWf exactState.structs exactState := by
      simpa [panSemStateVarsHOLWf, panSemExactStateVarsHOLWf,
        PanSemStateFiniteExact.toExact, valuesHOLWf] using hvars
    let pairExact : Option (PanSemResultExact width) × PanSemStateExact width σ := by assumption
    have hnonrecursive :
        evalPanSemNonrecursiveHOLExact (.shMemLoad size kind name address) exactState =
          some pairExact := by
      rfl
    have hInvariant := evalPanSemNonrecursiveHOLExact_shapeInvariant
      (.shMemLoad size kind name address) exactState hvarsExact
      pairExact.1 pairExact.2 hnonrecursive
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    simpa [FiniteEvalContext.withState, pairExact, exactState,
      panSemStateVarsHOLWf, panSemExactStateVarsHOLWf,
      PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact,
      PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite,
      evalPanSemNonrecursiveHOLExact, valuesHOLWf] using hInvariant
  case case64 =>
    rename_i pairExactInput
    rename_i evalExpression
    rename_i valueExpression
    rename_i addressExpression
    rename_i sizeInput
    rename_i stateInput
    rename_i contextInput
    let ctx : FiniteEvalContext width σ := contextInput
    let state : PanSemStateFiniteExact width σ := stateInput
    let size : OpSize := sizeInput
    let value : ExpHOL width := valueExpression
    let address : ExpHOL width := addressExpression
    let exactState := state.toExact
    letI : DecidablePred exactState.memaddrs := by
      simpa [exactState, PanSemStateFiniteExact.toExact] using ctx.memaddrsDecidable
    letI : DecidablePred exactState.shMemaddrs := by
      simpa [exactState, PanSemStateFiniteExact.toExact] using ctx.shMemaddrsDecidable
    have hvarsExact : panSemExactStateVarsHOLWf exactState.structs exactState := by
      simpa [panSemStateVarsHOLWf, panSemExactStateVarsHOLWf,
        PanSemStateFiniteExact.toExact, valuesHOLWf] using hvars
    let pairExact : Option (PanSemResultExact width) × PanSemStateExact width σ := pairExactInput
    have hnonrecursive :
        evalPanSemNonrecursiveHOLExact (.shMemStore size address value) exactState =
          some pairExact := by
      rfl
    have hInvariant := evalPanSemNonrecursiveHOLExact_shapeInvariant
      (.shMemStore size address value) exactState hvarsExact
      pairExact.1 pairExact.2 hnonrecursive
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    simpa [FiniteEvalContext.withState, pairExact, exactState,
      panSemStateVarsHOLWf, panSemExactStateVarsHOLWf,
      PanSemStateFiniteExact.toExact, PanSemStateFiniteExact.ofExact,
      PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite,
      evalPanSemNonrecursiveHOLExact, valuesHOLWf] using hInvariant
  case case34 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i shapeLookup
    rename_i hvalid
    rename_i shape
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception handlerId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case35 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshapeLookup
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception handlerId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case36 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hneq
    rename_i handlerProgram
    rename_i handlerVar
    rename_i handlerId
    rename_i infoTail
    rename_i value
    rename_i exceptionId
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.exception exceptionId value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hvalueWf : isWfShapeValueHOLExact context.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by
      simpa [panSemResultHOLWf] using hvalueWf⟩
  case case37 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hexception
    rename_i hreturned
    rename_i hcontinue
    rename_i hbreak
    rename_i other
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some other) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hresultWf : panSemResultHOLWf context.state.structs (some other) := by
      simpa [entryContext, FiniteEvalContext.withState, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    exact ⟨hfixedStructs, hfixedVarsAtOrig, hresultWf⟩
  case case30 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i values
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := context.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments hargs function
      body callee.lookup returnShape values hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case16 =>
    rename_i ihBody
    rename_i hbreak
    rename_i hnone
    rename_i hcontinue
    rename_i fixedContext
    rename_i fixed
    rename_i bodyEval
    rename_i postContext
    rename_i bodyResult
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hnonzero
    rename_i conditionEval
    rename_i value
    rename_i body
    rename_i condition
    rename_i state
    rename_i context
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    have hentryVars : panSemStateVarsHOLWf entryContext.state.structs entryContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, entryContext, entry,
        decClockHOLFinite] using hvars
    have hbody := ihBody hentryVars bodyResult postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, fixed,
        fixClockHOLFinite] using hbodyVarsAtPost
    have hbodyResultWf : panSemResultHOLWf context.state.structs bodyResult := by
      simpa [entryContext, entry, decClockHOLFinite] using hbody.2.2
    have hfixedResultWf : panSemResultHOLWf context.state.structs fixed.1 := by
      simpa [fixed, fixClockHOLFinite] using hbodyResultWf
    have hfixedStructs : fixedContext.state.structs = context.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, fixed, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = context.state.structs := by
          simp [entryContext, entry, decClockHOLFinite, state]
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf context.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    refine ⟨hfixedStructs, hfixedVarsAtOrig, ?_⟩
    simpa [fixed, fixClockHOLFinite] using hfixedResultWf
  case case17 =>
    intro result output heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case18 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case19 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case20 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, hvars, by simp [panSemResultHOLWf]⟩
  case case21 =>
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact ⟨rfl, panSemStateVarsHOLWf_emptyLocals _ hvars,
      by simp [panSemResultHOLWf]⟩
  case case22 =>
    simp
  case case23 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i stateContext
    rename_i sourceContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred stateContext.memaddrs := sourceContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some stateContext.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf stateContext arguments hargs function
      body callee.lookup returnShape hargsEval hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf stateContext.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf stateContext.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars none postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = sourceContext.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = sourceContext.state.structs := rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf sourceContext.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case24 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i stateContext
    rename_i sourceContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred stateContext.memaddrs := sourceContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some stateContext.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf stateContext arguments hargs function
      body callee.lookup returnShape hargsEval hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf stateContext.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf stateContext.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some .break) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = sourceContext.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = sourceContext.state.structs := rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf sourceContext.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case25 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i hargs
    rename_i arguments
    rename_i function
    rename_i info
    rename_i stateContext
    rename_i sourceContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred stateContext.memaddrs := sourceContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some stateContext.code.lookup function hargs
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf stateContext arguments hargs function
      body callee.lookup returnShape hargsEval hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf stateContext.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf stateContext.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some .continue) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = sourceContext.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = sourceContext.state.structs := rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf sourceContext.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case26 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i values
    rename_i arguments
    rename_i function
    rename_i state
    rename_i sourceContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := sourceContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function values
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments values function
      body callee.lookup returnShape hargsEval hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = sourceContext.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = sourceContext.state.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf sourceContext.state.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    have houtputVars :
        panSemStateVarsHOLWf sourceContext.state.structs
          (PanSemStateFiniteExact.emptyLocalsHOLFinite fixedContext.state) := by
      simpa [hfixedStructs] using
        panSemStateVarsHOLWf_emptyLocals fixedContext.state hfixedVars
    have hvalueWf : isWfShapeValueHOLExact sourceContext.state.structs value = true := by
      simpa [panSemResultHOLWf, entryContext, entry, callEntryStateHOLFinite, callEntryContextHOLFinite] using hbody.2.2
    refine ⟨?_, ?_, ?_⟩
    · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite,
        hfixedStructs]
    · simpa [FiniteEvalContext.withState] using houtputVars
    · simpa [panSemResultHOLWf] using hvalueWf
  case case27 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i infoTail
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i values
    rename_i arguments
    rename_i function
    rename_i state
    rename_i sourceContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred state.memaddrs := sourceContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some state.code.lookup function values
      body callee returnShape hlookup
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state arguments values function
      body callee.lookup returnShape hargsEval hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf state.structs entry := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.structs callee.lookup
        exact hcallee
      · simpa [entry, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned value)) postContext bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf postContext.state.structs postContext.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = sourceContext.state.structs := by
      calc
        fixedContext.state.structs = postContext.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = entryContext.state.structs := hbody.1
        _ = sourceContext.state.structs := by rfl
    have hrestoredVars :
        panSemStateVarsHOLWf sourceContext.state.structs
          { fixedContext.state with locals := state.locals } := by
      refine ⟨?_, ?_⟩
      · simpa [hfixedStructs] using hvars.1
      · simpa [hfixedStructs] using hfixedVars.2
    refine ⟨?_, ?_, by simp [panSemResultHOLWf]⟩
    · simp [FiniteEvalContext.withState, callRestoreLocalsContextHOLFinite, hfixedStructs]
    · simpa [FiniteEvalContext.withState, callRestoreLocalsContextHOLFinite,
        hfixedStructs] using hrestoredVars
  case case28 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i fixed
    rename_i hbody
    rename_i hvalid
    rename_i infoTail
    rename_i name
    rename_i kind
    rename_i hreturn
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i calleeLocals
    rename_i body
    rename_i hargs
    rename_i values
    rename_i arguments
    rename_i function
    rename_i state
    rename_i context
    intro result output heval
    letI : DecidablePred state.state.memaddrs := state.memaddrsDecidable
    have hentryStruct : postContext.state.structs = state.state.structs := by rfl
    have hlookupExact := lookupCodeHOLFinite_eq_some state.state.code.lookup arguments hargs
      calleeLocals returnShape hlookup hclock
    have hcallee := lookupCodeHOLExact_calleeLocalsWf state.state values hargs arguments
      calleeLocals returnShape.lookup hlookup body hlookupExact hvars.1 hvars.2
    let entryState := function.callEntryStateHOLFinite returnShape
    have hentryVars : panSemStateVarsHOLWf state.state.structs entryState := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf state.state.structs returnShape.lookup
        exact hcallee
      · simpa [entryState, callEntryStateHOLFinite] using hvars.2
    have hbodyInvariant := ihBody hentryVars (some (.returned hreturn)) value fixed
    have hbodyPayload : isWfShapeValueHOLExact state.state.structs hreturn = true := by
      simpa [panSemResultHOLWf, hentryStruct] using hbodyInvariant.2.2
    have hfixedStruct : fixedContext.state.structs = state.state.structs := by
      calc
        fixedContext.state.structs = value.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = postContext.state.structs := hbodyInvariant.1
        _ = state.state.structs := hentryStruct
    have hfixedLocalWf : valuesHOLWf state.state.structs value.state.locals.lookup := by
      simpa [hentryStruct, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using
        hbodyInvariant.2.1.1
    have hfixedGlobalWf : valuesHOLWf state.state.structs fixedContext.state.globals.lookup := by
      simpa [hentryStruct, fixedContext, callFixedContextHOLFinite, fixClockHOLFinite] using
        hbodyInvariant.2.1.2
    let callerState : PanSemStateFiniteExact width σ :=
      { fixedContext.state with locals := state.state.locals }
    have hcallerStruct : callerState.structs = state.state.structs := by
      simpa [callerState, fixedContext, FiniteEvalContext.withState] using hfixedStruct
    have hcallerVars : panSemStateVarsHOLWf callerState.structs callerState := by
      refine ⟨?_, ?_⟩
      · simpa [callerState, fixedContext, FiniteEvalContext.withState, hfixedStruct] using hvars.1
      · simpa [callerState, fixedContext, FiniteEvalContext.withState, hfixedStruct] using
          hfixedGlobalWf
    have hbodyPayloadCaller :
        isWfShapeValueHOLExact callerState.structs hreturn = true := by
      simpa [callerState, fixedContext, FiniteEvalContext.withState, hfixedStruct] using
        hbodyPayload
    have hsetVars := panSemStateVarsHOLWf_setKvar callerState name infoTail hreturn
      hcallerVars hbodyPayloadCaller
    have hpair : (none, fixedContext.withState
          (PanSemStateFiniteExact.setKvarHOLFinite name infoTail hreturn callerState)
          (by cases name <;> rfl) (by cases name <;> rfl)) = (result, output) := by
      exact Option.some.inj heval
    have hresult : none = result := congrArg Prod.fst hpair
    subst result
    have houtput : fixedContext.withState
        (PanSemStateFiniteExact.setKvarHOLFinite name infoTail hreturn callerState)
        (by cases name <;> rfl) (by cases name <;> rfl) = output := congrArg Prod.snd hpair
    rw [← houtput]
    simp only [FiniteEvalContext.withState_state]
    constructor
    · calc
        (PanSemStateFiniteExact.setKvarHOLFinite name infoTail hreturn callerState).structs =
            callerState.structs := by cases name <;> rfl
        _ = state.state.structs := by simpa using hcallerStruct
    · constructor
      · have hsetVarsContext :
            panSemStateVarsHOLWf state.state.structs
              (PanSemStateFiniteExact.setKvarHOLFinite name infoTail hreturn callerState) := by
          rw [← hcallerStruct]
          exact hsetVars
        exact hsetVarsContext
      · simp [panSemResultHOLWf]
  case case29 =>
    rename_i ihBody
    rename_i fixedContext
    rename_i bodyEval
    rename_i hshape
    rename_i value
    rename_i postContext
    rename_i entryContext
    rename_i entry
    rename_i hclock
    rename_i hlookup
    rename_i returnShape
    rename_i callee
    rename_i body
    rename_i hargsEval
    rename_i values
    rename_i arguments
    rename_i function
    rename_i state
    rename_i sourceContext
    rename_i inputArguments
    rename_i inputFunction
    rename_i inputState
    rename_i inputContext
    intro result output heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    letI : DecidablePred inputState.memaddrs := inputContext.memaddrsDecidable
    have hlookupExact := lookupCodeHOLFinite_eq_some inputState.code.lookup inputFunction
      sourceContext function arguments values hargsEval
    have hcallee := lookupCodeHOLExact_calleeLocalsWf inputState inputArguments sourceContext
      inputFunction function arguments.lookup values state hlookupExact hvars.1 hvars.2
    have hentryVars : panSemStateVarsHOLWf inputState.structs callee := by
      refine ⟨?_, ?_⟩
      · change valuesHOLWf inputState.structs arguments.lookup
        exact hcallee
      · simpa [callee, callEntryStateHOLFinite] using hvars.2
    have hbody := ihBody hentryVars (some (.returned hclock)) hlookup bodyEval
    have hbodyVarsAtPost :
        panSemStateVarsHOLWf hlookup.state.structs hlookup.state := by
      rw [hbody.1]
      exact hbody.2.1
    have hfixedVars :
        panSemStateVarsHOLWf fixedContext.state.structs fixedContext.state := by
      simpa [panSemStateVarsHOLWf, FiniteEvalContext.withState, fixedContext,
        callFixedContextHOLFinite, fixClockHOLFinite] using hbodyVarsAtPost
    have hfixedStructs : fixedContext.state.structs = inputState.structs := by
      calc
        fixedContext.state.structs = hlookup.state.structs := by
          simp [fixedContext, callFixedContextHOLFinite, fixClockHOLFinite]
        _ = returnShape.state.structs := hbody.1
        _ = inputState.structs := by rfl
    have hfixedVarsAtOrig :
        panSemStateVarsHOLWf inputState.structs fixedContext.state := by
      simpa [hfixedStructs] using hfixedVars
    exact ⟨hfixedStructs, hfixedVarsAtOrig, by simp [panSemResultHOLWf]⟩
  case case65 =>
    intro result output heval
    simp_all
  case case66 =>
    let ctx : FiniteEvalContext width σ := by assumption
    letI : DecidablePred ctx.state.memaddrs := ctx.memaddrsDecidable
    letI : DecidablePred ctx.state.shMemaddrs := ctx.shMemaddrsDecidable
    let other : ProgHOL width := by assumption
    let pair : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ := by
      assumption
    have hnonrec : PanSemStateFiniteExact.evalPanSemNonrecursiveHOLFinite
        ctx.state other = some pair := by assumption
    intro result output heval
    have hInvariant := evalPanSemNonrecursiveHOLFinite_shapeInvariant
      ctx.state hvars other pair.1 pair.2 hnonrec
    simp only [FiniteEvalContext.withState] at heval
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    rcases heval with ⟨rfl, rfl⟩
    exact hInvariant
end PanSemStateFiniteExact

/-- Exact finite-support port of HOL `evaluate_structs_invariant`
    (`panPropsScript.sml:1210-1212`). The premise is the HOL result-pair
    equation for `evaluate`; the conclusion preserves the structural context.
    Its proof uses the same finite-support recursive evaluator as the exact
    PanSem `evaluate_def` port. Only the four named finite-map fields and the
    positive width-indexed words use reviewed representation translations. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_structs_invariant" 1210
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateStructsInvariantFiniteExact {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width)
    (source : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (postState : PanPropsEvalStateFiniteExact width σ)
    (heval : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair source program =
      (result, postState)) :
    postState.structs = source.structs := by
  classical
  let panSource := source.toPanSemFinite
  have hevalPan : PanSemStateFiniteExact.evaluateHOLFiniteState panSource program =
      (result, postState.toPanSemFinite) := by
    let actual := PanSemStateFiniteExact.evaluateHOLFiniteState panSource program
    have hlocalEval :
        (actual.1, PanPropsEvalStateFiniteExact.ofPanSemFinite actual.2) =
          (result, postState) := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, actual,
        panSource] using heval
    have hpostCustom : PanPropsEvalStateFiniteExact.ofPanSemFinite actual.2 =
        postState := by
      simpa using congrArg Prod.snd hlocalEval
    have hpostFinite := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hpostCustom
    apply Prod.ext
    · simpa [actual] using congrArg Prod.fst hlocalEval
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] using hpostFinite
  have hevalMarked := (PanSemStateFiniteExact.evaluateHOLFiniteResult_eq_iff
    panSource program (result, postState.toPanSemFinite)).2 hevalPan
  let evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ :=
    ⟨panSource, inferInstance, inferInstance⟩
  have hevalProjection :
      (PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        program evaluationContext).map
        (fun pair => (pair.1, pair.2.state)) =
        some (result, postState.toPanSemFinite) := by
    simpa [PanSemStateFiniteExact.evaluateHOLFinite, evaluationContext] using hevalMarked
  cases hcontextEval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
      program evaluationContext with
  | none => simp [hcontextEval] at hevalProjection
  | some output =>
      have hprojectPair : (output.1, output.2.state) =
          (result, postState.toPanSemFinite) := by
        simpa [hcontextEval] using hevalProjection
      have hpostFinite : output.2.state = postState.toPanSemFinite :=
        congrArg Prod.snd hprojectPair
      have hpost : PanPropsEvalStateFiniteExact.ofPanSemFinite output.2.state =
          postState := by
        rw [hpostFinite]
        simp
      have hstructs := PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext_structs_eq
        program evaluationContext output.1 output.2 (by simp [hcontextEval])
      calc
        postState.structs =
            (PanPropsEvalStateFiniteExact.ofPanSemFinite output.2.state).structs := by
              rw [← hpost]
        _ = output.2.state.structs := rfl
        _ = evaluationContext.state.structs := hstructs
        _ = source.structs := rfl

/-- Exact finite-support port of HOL `evaluate_is_wf_shape_invariant`
    (`cakeml/pancake/semantics/panPropsScript.sml:1250-1264`). The two input
    predicates and two post-state predicates are the pointwise rendering of
    HOL `FEVERY`; the result match is HOL's Return/Exception conclusion. Only
    the four named finite-map fields use the canonical representation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_is_wf_shape_invariant"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateIsWfShapeInvariantFiniteExact {width : Nat} {σ : Type}
    [NeZero width]
    (program : ProgHOL width)
    (source : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (postState : PanPropsEvalStateFiniteExact width σ)
    (heval : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair source program =
      (result, postState))
    (hlocals : ∀ name value, source.locals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true)
    (hglobals : ∀ name value, source.globals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) :
    (∀ name value, postState.locals.lookup name = some value →
      isWfShapeValueHOLExact postState.structs value = true) ∧
    (∀ name value, postState.globals.lookup name = some value →
      isWfShapeValueHOLExact postState.structs value = true) ∧
    panSemResultHOLWf source.structs result := by
  classical
  let panSource := source.toPanSemFinite
  have hvars : panSemStateVarsHOLWf panSource.structs panSource := by
    constructor
    · intro name value hlookup
      exact hlocals name value (by
        simpa [panSource, PanPropsEvalStateFiniteExact.toPanSemFinite,
          PanPropsEvalStateFiniteExact.toExact,
          PanSemStateFiniteExact.ofExact] using hlookup)
    · intro name value hlookup
      exact hglobals name value (by
        simpa [panSource, PanPropsEvalStateFiniteExact.toPanSemFinite,
          PanPropsEvalStateFiniteExact.toExact,
          PanSemStateFiniteExact.ofExact] using hlookup)
  have hevalPan : PanSemStateFiniteExact.evaluateHOLFiniteState panSource program =
      (result, postState.toPanSemFinite) := by
    let actual := PanSemStateFiniteExact.evaluateHOLFiniteState panSource program
    have hlocalEval : (actual.1,
        PanPropsEvalStateFiniteExact.ofPanSemFinite actual.2) =
          (result, postState) := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, actual,
        panSource] using heval
    have hpostCustom : PanPropsEvalStateFiniteExact.ofPanSemFinite actual.2 =
        postState := by
      simpa using congrArg Prod.snd hlocalEval
    have hpostFinite := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hpostCustom
    apply Prod.ext
    · simpa [actual] using congrArg Prod.fst hlocalEval
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] using hpostFinite
  have hevalMarked := (PanSemStateFiniteExact.evaluateHOLFiniteResult_eq_iff
    panSource program (result, postState.toPanSemFinite)).2 hevalPan
  let evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ :=
    ⟨panSource, inferInstance, inferInstance⟩
  have hevalProjection :
      (PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        program evaluationContext).map
        (fun pair => (pair.1, pair.2.state)) =
        some (result, postState.toPanSemFinite) := by
    simpa [PanSemStateFiniteExact.evaluateHOLFinite, evaluationContext] using hevalMarked
  have hpostAndResult :
      postState.toPanSemFinite.structs = panSource.structs ∧
      panSemStateVarsHOLWf panSource.structs postState.toPanSemFinite ∧
      panSemResultHOLWf panSource.structs result := by
    cases hcontextEval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        program evaluationContext with
    | none => simp [hcontextEval] at hevalProjection
    | some pair =>
        have hprojectPair : (pair.1, pair.2.state) = (result, postState.toPanSemFinite) := by
          simpa [hcontextEval] using hevalProjection
        have hresult : pair.1 = result := congrArg Prod.fst hprojectPair
        have hstate : pair.2.state = postState.toPanSemFinite :=
          congrArg Prod.snd hprojectPair
        have hcontextSuccess :
            PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
              program evaluationContext = some (result, pair.2) := by
          rw [hcontextEval]
          cases pair with
          | mk evalResult evalContext => simp_all
        have hinvariant :=
          PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext_shapeInvariant
            program evaluationContext hvars result pair.2 hcontextSuccess
        have hpostVars : panSemStateVarsHOLWf panSource.structs
            postState.toPanSemFinite := by
          simpa [hstate] using hinvariant.2.1
        exact ⟨by simpa [hstate] using hinvariant.1, hpostVars, hinvariant.2.2⟩
  have hstructs : postState.structs = source.structs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite, panSource,
      PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact] using
      hpostAndResult.1
  refine ⟨?_, ?_, ?_⟩
  · intro name value hlookup
    have h := hpostAndResult.2.1.1 name value ?_
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite, panSource,
        PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact,
        hstructs] using h
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite,
        PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact] using hlookup
  · intro name value hlookup
    have h := hpostAndResult.2.1.2 name value ?_
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite, panSource,
        PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact,
        hstructs] using h
    · simpa [PanPropsEvalStateFiniteExact.toPanSemFinite,
        PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact] using hlookup
  · simpa [panSemResultHOLWf, PanPropsEvalStateFiniteExact.toPanSemFinite,
      panSource, PanSemStateFiniteExact.ofExact, PanPropsEvalStateFiniteExact.toExact] using
      hpostAndResult.2.2

end Flapjack
