import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanProps.EvaluateResultInvariant
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
Finite-support Pan-to-Crep relation infrastructure for the shape-invariant
proof path. The field types follow HOL `state_rel_def` and `locals_rel_def`:
`MlS`, `ValueHOL`, `ShapeHOL`, finite-support maps, and `CrepSemHOLState`.

These declarations are untagged relation support. Their conjunctions were
compared with HOL `state_rel_def` and `locals_rel_def` at
`pan_to_crepProofScript.sml:45-82`; the finite-map fields are now named through
their separate owning carriers, with same-module roundtrip witnesses for the
multi-carrier qualifier. The final theorem remains untagged until the direct
finite-map `evaluate_def` source review and tag are completed (bead
`flapjack-qj5`).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL ProgHOL StructContextExact isWfShapeExactHOL)

/-- Flapjack-specific exact-map bound predicate for relation support. It
    has the same quantifiers and bounds as HOL `ctxt_max_def`
    (`pan_commonPropsScript.sml:11-15`): `0 ≤ n` and every slot from each
    lookup is at most `n`. `Nat` renders HOL `num`, and its map is the exact
    `PanToCrepContextExact.vars` field. -/
def ctxtMaxFiniteExact {κ β : Type}
    (n : Nat) (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  0 ≤ n ∧ ∀ key shape slots, map.lookup key = some (shape, slots) →
    ∀ slot ∈ slots, slot ≤ n

/-- Flapjack-specific exact-map overlap predicate for relation support. It
    renders HOL `no_overlap_def` (`pan_commonPropsScript.sml:18-24`): each slot
    list is Nodup and no slot occurs in two distinct key lists. The existential
    shared-slot formulation is equivalent to HOL's negated `DISJOINT` on the
    two list sets. The map is `PanToCrepContextExact.vars`. -/
def noOverlapFiniteExact {κ β : Type}
    (map : HolFiniteMapExact κ (β × List Nat)) : Prop :=
  (∀ key shape slots, map.lookup key = some (shape, slots) → slots.Nodup) ∧
    ∀ key key' shape shape' slots slots',
      map.lookup key = some (shape, slots) →
      map.lookup key' = some (shape', slots') →
      (∃ slot, slot ∈ slots ∧ slot ∈ slots') → key = key'

/-- Same-module canonical relation witness for the multi-carrier
    `fmap_as_finite_support_relation` qualifier. It forwards the canonical
    finite-support roundtrip of `PanSemStateFiniteExact`, the carrier owning the
    single finite-map field traversed by HOL `state_rel_def` (`globals`). -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Exact port of HOL `state_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:45-58`). `source.globals`
    is the only finite-map field of an exact state carrier that the relation
    traverses, and HOL asserts it is `FEMPTY`; the qualifier records exactly
    that field. The Crep target contributes no traversed finite-map field. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals])]
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
    literal `is_wf_shape_nil (shape_of v)` conjunct. `mapM` is the
    `OPT_MMAP` result equation, `flattenHOL` is `flatten`, and the shape
    equality uses exact `ShapeHOL` names. The premises and quantified names
    follow HOL `locals_rel_def` (`pan_to_crepProofScript.sml:71-82`); relation
    carrier translations are recorded by the final theorem qualifier. -/
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

/-- Owner structure for the independent finite-map parameter `t_locs`. -/
structure PanToCrepTargetLocalsExact (width : Nat) [NeZero width] where
  targetLocals : HolFiniteMapExact Nat (HolWordLab width)

/-- Project the independent `t_locs` carrier to its broad map representation. -/
def PanToCrepTargetLocalsExact.toBroad {width : Nat} [NeZero width]
    (locals : PanToCrepTargetLocalsExact width) : PanToCrepTargetLocalsBroad width :=
  panToCrepTargetLocalsToBroad locals.targetLocals

/-- Rebuild the canonical owner carrier from the broad map and support witness. -/
def PanToCrepTargetLocalsExact.ofBroad {width : Nat} [NeZero width]
    (locals : PanToCrepTargetLocalsBroad width)
    (finiteSupport : ∃ keys : List Nat, ∀ key, locals key ≠ none → key ∈ keys) :
    PanToCrepTargetLocalsExact width :=
  ⟨panToCrepTargetLocalsOfBroad locals finiteSupport⟩

/-- The independent map owner roundtrips through its broad counterpart. -/
theorem PanToCrepTargetLocalsExact.ofBroad_toBroad {width : Nat} [NeZero width]
    (locals : PanToCrepTargetLocalsExact width) :
    PanToCrepTargetLocalsExact.ofBroad locals.toBroad
      locals.targetLocals.finiteSupport = locals := by
  cases locals
  rfl

/-- Same-module multi-carrier witness for the exact `t_locs` finite-map field. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepTargetLocalsExact
    {width : Nat} [NeZero width] (locals : PanToCrepTargetLocalsExact width) :
    PanToCrepTargetLocalsExact.ofBroad locals.toBroad
      locals.targetLocals.finiteSupport = locals :=
  PanToCrepTargetLocalsExact.ofBroad_toBroad locals

/-- Same-module multi-carrier witness for CrepSem's finite-map fields. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type} (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

/-- Same-module multi-carrier witness for the Pan-to-Crep context maps. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad context.toBroad = context := by
  cases context
  rfl

/-- Source-reviewed port of HOL `evaluate_shape_invariant_ret_inst`
    (`pan_to_crepProofScript.sml:3016-3028`). The binders `program`, source,
    result, and postState render HOL `p`, `s`, `v`, and `s'`; the only premises
    are the successful `evaluate` result, `state_rel`, and `locals_rel`, and the
    Return/Exception cases conclude the value-level rendering of
    `is_wf_shape_v_nil`. `state_rel_def` and `locals_rel_def` were compared at
    `pan_to_crepProofScript.sml:45-82`; `ctxt_max_def` and `no_overlap_def` at
    `pan_commonPropsScript.sml:11-24`. PanSem maps, context `vars`, and the
    independent HOL `t_locs` map use the named finite-support owners and their
    same-module roundtrip witnesses. `ValueHOL`, `PanSemResultExact`,
    `ProgHOL`, `ShapeHOL`, and `MlS` have exact constructor/field carriers, and
    `[NeZero width]` matches HOL's positive word dimension.

    The premise uses the pair-shaped `evaluateHOLFiniteState` view of the
    finite context evaluator. Its recursive clauses were compared with all 21
    HOL `evaluate_def` constructors (panSemScript.sml:556-761); nonrecursive
    clauses call the reviewed exact clause helpers and rewrap finite-support
    post-states. The outer recursive assembly marker is proved total, so the
    wrapper's fallback is unreachable. The 66-case projection proves agreement
    with the broad exact evaluator. The evaluator definition remains untagged;
    this theorem's tag claims only the source-reviewed theorem statement and
    its explicit finite-map carrier translations. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "evaluate_shape_invariant_ret_inst"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanToCrepContextExact.vars,
    PanToCrepTargetLocalsExact.targetLocals])]
theorem panToCrepFiniteEvaluateShapeInvariantRetInst {width : Nat} {σ : Type}
    [NeZero width] (program : ProgHOL width)
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (targetLocals : PanToCrepTargetLocalsExact width)
    (relationContext : PanToCrepContextExact width)
    (result : PanSemResultExact width)
    (postState : PanSemStateFiniteExact width σ)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext
      source.locals targetLocals.targetLocals)
    (heval : PanSemStateFiniteExact.evaluateHOLFiniteState source program =
      (some result, postState)) :
    match result with
    | .returned value =>
        isWfShapeValueHOLExact [] value = true
    | .exception _ value =>
        isWfShapeValueHOLExact [] value = true
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
    source target targetLocals.targetLocals relationContext hstate hlocals
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
      simpa [hstructs] using hvalue
  | exception exceptionId value =>
      have hvalue :
          isWfShapeValueHOLExact source.structs value = true := by
        simpa [Flapjack.panSemResultHOLWf] using hresultWf
      simpa [hstructs] using hvalue
  | _ => trivial

end Flapjack
