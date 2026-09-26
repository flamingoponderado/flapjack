import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Finite-support Pan-to-Crep relation infrastructure for the shape-invariant
proof path. The field types follow HOL `state_rel_def` and `locals_rel_def`:
`MlS`, `ValueHOL`, `ShapeHOL`, finite-support maps, and `CrepSemHOLState`.

These declarations are intentionally untagged support. The current
`fmap_as_finite_support` qualifier can certify fields owned by one carrier
structure, while these relations span the separate PanSem and CrepSem state
carriers. They are not claims that a HOL relation declaration has been
ported; the exact theorem tag must wait for reviewed multi-carrier qualifier
support and the faithful evaluator proof.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL ProgHOL StructContextExact isWfShapeExactHOL)

/-- Flapjack-specific exact-map bound predicate for relation support. It
    mirrors the shape of HOL `ctxt_max_def`, but is not a tagged port: it takes
    a bare finite-map parameter without the owning carrier witness required by
    the current finite-map qualifier. -/
def ctxtMaxFiniteExact {κ β : Type}
    (n : Nat) (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ key shape slots, map.lookup key = some (shape, slots) →
    ∀ slot ∈ slots, slot ≤ n

/-- Flapjack-specific exact-map overlap predicate for relation support. It
    mirrors the shape of HOL `no_overlap_def`, but is not a tagged port because
    its bare map parameter cannot carry the reviewed finite-map qualifier. -/
def noOverlapFiniteExact {κ β : Type}
    (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  (∀ key shape slots, map.lookup key = some (shape, slots) → slots.Nodup) ∧
    ∀ key key' shape shape' slots slots',
      map.lookup key = some (shape, slots) →
      map.lookup key' = some (shape', slots') →
      (∃ slot, slot ∈ slots ∧ slot ∈ slots') → key = key'

/-- Flapjack-specific state-relation support over the exact finite-support
    PanSem and CrepSem carriers. `globals.lookup = none` renders HOL `FEMPTY`;
    this is not a tagged `state_rel_def` port because its finite-map fields span
    two owning state carriers. -/
def panToCrepStateRelFiniteExact {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ) : Prop :=
  source.memory = target.memory ∧
    source.memaddrs = target.memaddrs ∧
    source.shMemaddrs = target.shMemaddrs ∧
    source.structs = [] ∧
    source.globals.lookup = (fun _ => none) ∧
    source.clock = target.clock ∧
    source.be = target.be ∧
    source.ffi = target.ffi ∧
    source.baseAddr = target.baseAddr ∧
    source.topAddr = target.topAddr

/-- Flapjack-specific local-relation support over the exact finite-support
    PanSem value and CrepSem word carriers. The final conjunct preserves the
    source shape invariant; this is not a tagged `locals_rel_def` port because
    the relation spans separate map carriers. -/
def panToCrepLocalsRelFiniteExact {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width)) : Prop :=
  noOverlapFiniteExact context.vars ∧
    ctxtMaxFiniteExact context.vmax context.vars ∧
    ∀ name value, sourceLocals.lookup name = some value →
      ∃ slots words,
        context.vars.lookup name = some (shapeOfHOLExact value, slots) ∧
        slots.mapM targetLocals.lookup = some words ∧
        flattenHOL value = words ∧
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true

/-- The exact finite-support locals relation immediately supplies the literal
    `is_wf_shape_nil (shape_of v)` fact for every present source local. -/
theorem panToCrepLocalsRelFiniteExact_shapeProjection {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  obtain ⟨slots, words, _hcontext, _hmapped, _hflatten, hwf⟩ :=
    hrel.2.2 name value hlookup
  exact hwf

/-- The value-level well-formedness fact is a separate bridge from the literal
    HOL `locals_rel` conjunct `is_wf_shape_nil (shape_of v)`. -/
theorem panToCrepLocalsRelFiniteExact_valueShapeProjection {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    isWfShapeValueHOLExact [] value = true := by
  have hshape := panToCrepLocalsRelFiniteExact_shapeProjection
    context sourceLocals targetLocals name value hrel hlookup
  have hbridge := isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil
    ([] : StructContextExact) rfl value
  rw [hbridge] at hshape
  exact hshape

/-- Projection of HOL `state_rel_def`'s structural-context conjunct. -/
theorem panToCrepStateRelFiniteExact_structs {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.structs = [] := hrel.2.2.2.1

/-- The exact Pan-to-Crep relations provide the initial locals/globals shape
    hypotheses used by the PanSem evaluator invariant. -/
theorem panToCrepExactInitialShapeInvariant {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (context : PanToCrepContextExact width)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact context source.locals targetLocals) :
    (∀ name value, source.locals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) ∧
    (∀ name value, source.globals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) := by
  constructor
  · intro name value hlookup
    have hshape := panToCrepLocalsRelFiniteExact_valueShapeProjection
      context source.locals targetLocals name value hlocals hlookup
    have hstruct := panToCrepStateRelFiniteExact_structs source target hstate
    simpa [hstruct] using hshape
  · intro name value hlookup
    have hglobals : source.globals.lookup = (fun _ => none) := hstate.2.2.2.2.1
    rw [hglobals] at hlookup
    simp at hlookup

/-- Flapjack-specific Return-clause composition: exact Pan-to-Crep relations
    supply the evaluator's initial map hypotheses, and the finite evaluator's
    Return clause proves the HOL-shaped empty-context payload conclusion. This
    remains untagged because its evaluator premise is a finite-context clause,
    not HOL's complete `evaluate` relation. -/
theorem panToCrepFiniteReturnPayloadShape {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (relationContext : PanToCrepContextExact width)
    (evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (expression : ExpHOL width) (value : ValueHOL width)
    (output : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (hcontext : evaluationContext.state = source)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext source.locals targetLocals)
    (heval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
      (.return expression) evaluationContext = some (some (.returned value), output)) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  have hinitial := panToCrepExactInitialShapeInvariant
    source target targetLocals relationContext hstate hlocals
  have hpayload := PanSemStateFiniteExact.evalPanSemFiniteReturnPayloadWf
    evaluationContext (by simpa [hcontext] using hinitial.1)
    (by simpa [hcontext] using hinitial.2) expression value output heval
  rw [hcontext] at hpayload
  have hstructs := panToCrepStateRelFiniteExact_structs source target hstate
  have hvalue : isWfShapeValueHOLExact [] value = true := by
    simpa [hstructs] using hpayload
  exact isWfShapeValueHOLExact_shapeOfHOLExact [] value hvalue

/-- Flapjack-specific Raise-clause composition with the exact Pan-to-Crep
    relations. The premise is the finite-context Raise clause, so this helper
    is proof support and not a tagged port of the complete HOL theorem. -/
theorem panToCrepFiniteRaisePayloadShape {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (relationContext : PanToCrepContextExact width)
    (evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (exception : MlS) (expression : ExpHOL width) (value : ValueHOL width)
    (output : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (hcontext : evaluationContext.state = source)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext source.locals targetLocals)
    (heval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
      (.raise exception expression) evaluationContext = some (some (.exception exception value), output)) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  have hinitial := panToCrepExactInitialShapeInvariant
    source target targetLocals relationContext hstate hlocals
  have hpayload := PanSemStateFiniteExact.evalPanSemFiniteRaisePayloadWf
    evaluationContext (by simpa [hcontext] using hinitial.1)
    (by simpa [hcontext] using hinitial.2) exception expression value output heval
  rw [hcontext] at hpayload
  have hstructs := panToCrepStateRelFiniteExact_structs source target hstate
  have hvalue : isWfShapeValueHOLExact [] value = true := by
    simpa [hstructs] using hpayload
  exact isWfShapeValueHOLExact_shapeOfHOLExact [] value hvalue

 /-- Finite-support view of the independent HOL `t_locs` map parameter. -/
abbrev PanToCrepTargetLocalsBroad (width : Nat) [NeZero width] :=
  Nat → Option (HolWordLab width)

/-- Forget the finite-support proof on HOL `t_locs` while retaining lookups. -/
def panToCrepTargetLocalsToBroad {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact Nat (HolWordLab width)) :
    PanToCrepTargetLocalsBroad width := locals.lookup

/-- Rebuild HOL `t_locs` from its lookup function and finite-domain witness. -/
def panToCrepTargetLocalsOfBroad {width : Nat} [NeZero width]
    (locals : PanToCrepTargetLocalsBroad width)
    (finiteSupport : ∃ keys : List Nat, ∀ key, locals key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (HolWordLab width) :=
  ⟨locals, finiteSupport⟩

/-- FLAPJACK-SPECIFIC carrier witness (not a HOL declaration): the theorem's
    independent finite-map parameter roundtrips through its lookup function
    and finite-domain witness. It is checked separately from the three state
    owners. -/
theorem holFmapParameterAsFiniteSupportWitness_panToCrepFiniteEvaluateShapeInvariantRetInst
    {width : Nat} [NeZero width]
    (locals : HolFiniteMapExact Nat (HolWordLab width)) :
    panToCrepTargetLocalsOfBroad (panToCrepTargetLocalsToBroad locals)
      locals.finiteSupport = locals := by
  cases locals
  rfl

/-- Flapjack-specific full-program shape-invariant composition over the
    finite-support PanSem/CrepSem carriers. It proves the HOL conclusion from a
    result-shaped view of the finite-context evaluator. The complete projection
    to `evalPanSemRecursiveCallContextHOLExact` is proved by
    `evaluateHOLFinite_toExact` (the 66-case evaluator projection tracked by
    `flapjack-6yq`). It remains untagged because its relation hypotheses are
    support definitions spanning multiple carriers; the faithful theorem and
    source-reviewed representation support remain open under `flapjack-4ac.5.83`.
    -/
theorem panToCrepFiniteEvaluateShapeInvariantRetInst {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width)
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (relationContext : PanToCrepContextExact width)
    (result : PanSemResultExact width)
    (postState : PanSemStateFiniteExact width σ)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext
      source.locals targetLocals)
    (heval : PanSemStateFiniteExact.evaluateHOLFiniteState source program =
      (some result, postState)) :
    match result with
    | .returned value =>
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true
    | .exception _ value =>
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true
    | _ => True := by
  classical
  have hevalHelper : PanSemStateFiniteExact.evaluateHOLFiniteResult source program =
      (some result, postState) := by
    simpa [PanSemStateFiniteExact.evaluateHOLFiniteState,
      PanSemStateFiniteExact.evaluateHOLFiniteResult,
      PanSemStateFiniteExact.evaluateHOLFiniteStateWithDeciders] using heval
  have hevalMarked := (PanSemStateFiniteExact.evaluateHOLFiniteResult_eq_iff
    source program (some result, postState)).2 hevalHelper
  let evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ :=
    ⟨source, inferInstance, inferInstance⟩
  have hevalProjection :
      (PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        program evaluationContext).map
        (fun pair => (pair.1, pair.2.state)) = some (some result, postState) := by
    simpa [PanSemStateFiniteExact.evaluateHOLFinite, evaluationContext] using hevalMarked
  have hinitial := panToCrepExactInitialShapeInvariant
    source target targetLocals relationContext hstate hlocals
  have hresultWf : Flapjack.panSemResultHOLWf source.structs (some result) := by
    cases hcontextEval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        program evaluationContext with
    | none => simp [hcontextEval] at hevalProjection
    | some pair =>
        have hprojectPair : (pair.1, pair.2.state) = (some result, postState) := by
          simpa [hcontextEval] using hevalProjection
        have hresult : pair.1 = some result := congrArg Prod.fst hprojectPair
        have hpair : pair = (some result, pair.2) := by
          apply Prod.ext
          · exact hresult
          · rfl
        have hcontextSuccess :
            PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
              program evaluationContext = some (some result, pair.2) := by
          rw [hpair] at hcontextEval
          exact hcontextEval
        have hinvariant :=
          PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext_shapeInvariant
            program evaluationContext ⟨hinitial.1, hinitial.2⟩ (some result) pair.2
            hcontextSuccess
        exact hinvariant.2.2
  have hstructs := panToCrepStateRelFiniteExact_structs
    source target hstate
  cases result with
  | returned value =>
      have hvalue :
          isWfShapeValueHOLExact source.structs value = true := by
        simpa [Flapjack.panSemResultHOLWf] using hresultWf
      have hvalueNil : isWfShapeValueHOLExact [] value = true := by
        simpa [hstructs] using hvalue
      exact isWfShapeValueHOLExact_shapeOfHOLExact [] value hvalueNil
  | exception exceptionId value =>
      have hvalue :
          isWfShapeValueHOLExact source.structs value = true := by
        simpa [Flapjack.panSemResultHOLWf] using hresultWf
      have hvalueNil : isWfShapeValueHOLExact [] value = true := by
        simpa [hstructs] using hvalue
      exact isWfShapeValueHOLExact_shapeOfHOLExact [] value hvalueNil
  | _ => trivial

end Flapjack
