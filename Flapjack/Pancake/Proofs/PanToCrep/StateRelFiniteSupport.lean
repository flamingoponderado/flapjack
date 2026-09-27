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
multi-carrier qualifier. The final theorem
`panToCrepFiniteEvaluateShapeInvariantRetInst` below now carries the reviewed
HOL tag. Its faithful `evaluate_is_wf_shape_invariant` prerequisite is tagged
in `PanProps/EvaluateResultInvariant.lean`; bead `flapjack-4ac.5.83` tracks
coordinator review of this completed theorem path.
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

/-- Same-module canonical relation witness for the multi-carrier
    `fmap_as_finite_support_relation` qualifier. It forwards the canonical
    finite-support roundtrip of `PanToCrepContextExact`, the carrier owning the
    finite-map field traversed by HOL `locals_rel_def` (`vars`). -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

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

/-- The `state_rel` conjunct of HOL `call_preserve_state_code_locals_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2355`) is preserved by
    the call-entry clock decrement and arbitrary replacement of the source
    and target locals. The source theorem's `state_rel_def` (`:45-58`) does not
    mention locals; its only clock condition is equality. Both HOL
    `dec_clock_def` declarations decrement equal clocks identically. This is
    only that one projected conjunct: the code, exception, and locals relation
    conjuncts are not established here, and this helper deliberately has no
    `@[hol]` tag for the full Call theorem. -/
theorem panToCrepCallStateRelFiniteExactLocalUpdate
    {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (hstate : panToCrepStateRelFiniteExact source target) :
    panToCrepStateRelFiniteExact
      ({source.decClockHOLFinite with locals := sourceLocals})
      ({decClockCrepSemHOL target with locals := targetLocals}) := by
  rcases hstate with
    ⟨hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
      hbe, hffi, hbaseAddr, htopAddr⟩
  simp [panToCrepStateRelFiniteExact,
    PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL,
    hmemory, hmemaddrs, hshmemaddrs, hstructs, hglobals, hclock,
    hbe, hffi, hbaseAddr, htopAddr]

/-- Exact port of HOL `locals_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:71-78`). The relation
    traverses exactly three finite-map values: `context.vars` (the owning
    `PanToCrepContextExact` field) and the two standalone exact-map parameters
    `sourceLocals`/`targetLocals`, which the qualifier records as bare entries.
    The remaining HOL side conditions (`no_overlap`, `ctxt_max`, `shape_of`,
    `OPT_MMAP`, `flatten`, `is_wf_shape_nil`) are rendered clause-for-clause. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_def"
  (fmap_as_finite_support_relation :=
    [PanToCrepContextExact.vars, sourceLocals, targetLocals])]
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

/-- Exact port of HOL `excp_rel_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:16-23`). Both maps are
    standalone exact finite-map parameters, so the qualifier records them as
    bare entries: `compilerCodes` is HOL's `ceids : eid |-> 'a word` and
    `sourceShapes` is HOL's `seids`, the source `eshapes : eid |-> shape`. HOL
    `FDOM seids = FDOM ceids` is rendered pointwise on the canonical
    `HolFiniteMapExact` lookup (equality of definedness), and `FLOOKUP` becomes
    `.lookup`. The source map's values are not related to the compiler's; only
    the domains and the injectivity of the compiler codes are asserted. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "excp_rel_def"
  (fmap_as_finite_support_relation := [compilerCodes, sourceShapes])]
def panToCrepExcpRelFiniteExact {width : Nat} [NeZero width]
    (compilerCodes : HolFiniteMapExact MlS (BitVec width))
    (sourceShapes : HolFiniteMapExact MlS ShapeHOL) : Prop :=
  (∀ key, (sourceShapes.lookup key).isSome =
    (compilerCodes.lookup key).isSome) ∧
    ∀ exception exception' code code',
      compilerCodes.lookup exception = some code →
      compilerCodes.lookup exception' = some code' →
      code = code' → exception = exception'

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

/-- Exact port of HOL `locals_rel_wf_shape` at
    `pan_to_crepProofScript.sml:2345`: the same `locals_rel` and present-local
    lookup premises imply `is_wf_shape_v_nil` for that value. The result is the
    exact value-level predicate; its only representation translation is the
    three named finite-map carriers. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_wf_shape" 2345
  (fmap_as_finite_support_relation :=
    [PanToCrepContextExact.vars, sourceLocals, targetLocals])]
theorem panToCrepLocalsRelWfShapeFiniteExact {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (sourceLocals : HolFiniteMapExact MlS (ValueHOL width))
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (value : ValueHOL width)
    (hrel : panToCrepLocalsRelFiniteExact context sourceLocals targetLocals)
    (hlookup : sourceLocals.lookup name = some value) :
    isWfShapeValueHOLExact [] value = true :=
  panToCrepLocalsRelFiniteExact_valueShapeProjection
    context sourceLocals targetLocals name value hrel hlookup

/-- Exact port of HOL `state_rel_structs[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:59-63`), the
    structural-context projection of `state_rel_def`. The relation qualifier
    records the same `PanSemStateFiniteExact.globals` translation as the parent
    relation (this projection does not read that field, but the tagged
    declaration is stated over the reviewed exact relation). -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_structs"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals])]
theorem panToCrepStateRelFiniteExact_structs {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.structs = [] := hrel.2.2.2.1

/-- Exact port of HOL `state_rel_globals[local]`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:65-69`), the globals
    projection of `state_rel_def`. HOL concludes `s.globals = FEMPTY`; the
    canonical `HolFiniteMapExact` translation renders `FEMPTY` pointwise as
    `lookup = fun _ => none`, exactly as in the tagged parent relation. The
    relation qualifier records the traversed `PanSemStateFiniteExact.globals`
    field. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_globals"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals])]
theorem panToCrepStateRelFiniteExact_globals {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    (target : CrepSemHOLState width σ)
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.globals.lookup = (fun _ => none) := hrel.2.2.2.2.1

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
    have hshape := panToCrepLocalsRelWfShapeFiniteExact
      context source.locals targetLocals name value hlocals hlookup
    have hstruct := panToCrepStateRelFiniteExact_structs source target hstate
    simpa [hstruct] using hshape
  · intro name value hlookup
    have hglobals : source.globals.lookup = (fun _ => none) := hstate.2.2.2.2.1
    rw [hglobals] at hlookup
    simp at hlookup

/-- Flapjack-specific call-entry invariant for HOL
    `evaluate_shape_invariant_ret_inst2` (`pan_to_crepProofScript.sml:3031-3044`).
    The successful exact `evalListHOLFinite` premise is HOL's
    `OPT_MMAP (eval s) argexps = SOME args`, and `hlookup` is the exact
    `lookup_code` result over the same finite-support code carrier. Existing
    `lookupCodeHOLExact_calleeLocalsWf` proves that the successful lookup binds
    only shape-valid locals; `panToCrepExactInitialShapeInvariant` supplies the
    source locals/globals facts from the exact `state_rel`/`locals_rel`
    premises. The conclusion is precisely the locals/globals invariant for
    `dec_clock s with locals := newlocals` used by the body evaluator. Lean's
    implicit decidability dictionary for `s.memaddrs` is implementation
    plumbing for `eval`; callers supply it classically, so it adds no
    proposition to the HOL premises. This is proof infrastructure rather than
    a standalone HOL declaration, so it has no `@[hol]` tag and does not assume
    any body-evaluation result. -/
theorem panToCrepCallEntryShapeInvariantFiniteExact {width : Nat} {σ : Type}
    [NeZero width] (source : PanSemStateFiniteExact width σ)
    [DecidablePred source.memaddrs]
    (target : CrepSemHOLState width σ)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab width))
    (relationContext : PanToCrepContextExact width)
    (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (fname : MlS) (body : ProgHOL width)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext
      source.locals targetLocals)
    (hargs : source.evalListHOLFinite arguments = some values)
    (hlookup : Flapjack.lookupCodeHOLExact source.code.lookup fname values =
      some (body, newlocals.lookup, returnShape)) :
    (∀ name value, newlocals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) ∧
    (∀ name value, source.globals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) := by
  have hinitial := panToCrepExactInitialShapeInvariant source target
    targetLocals relationContext hstate hlocals
  have hcallee := lookupCodeHOLExact_calleeLocalsWf source arguments values
    fname body newlocals.lookup returnShape hargs hlookup hinitial.1 hinitial.2
  exact ⟨hcallee, hinitial.2⟩

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

/-- Exact port of HOL `tlc_def`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2317-2319`):
    `tlc ns args = FEMPTY |++ ZIP (ns, FLAT (MAP flatten args))`. Keys are
    `num` (`Nat`) and values are `'a word_lab` (`HolWordLab width`), so the
    result carrier is the canonical finite-support
    `HolFiniteMapExact Nat (HolWordLab width)`; `|++` is the reviewed
    `HolFiniteMapExact.updateListEq` rendering of HOL `FUPDATE_LIST` (HOL `=`),
    and HOL `flatten` is the tagged `flattenHOL`. The standalone
    `fmap_as_finite_support_result` qualifier records only that finite-support
    representation; the same-module witness below states the unconditional
    lookup-level correspondence to the raw `FUPDATE_LIST_HOL` operation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "tlc_def"
  (fmap_as_finite_support_result)]
def tlcHOL {width : Nat} [NeZero width] (slots : List Nat)
    (arguments : List (ValueHOL width)) : HolFiniteMapExact Nat (HolWordLab width) :=
  HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
    (slots.zip ((arguments.map flattenHOL).flatten))

/-- Canonical standalone finite-map witness for `tlcHOL`: its `lookup` is
    exactly the HOL-shaped raw `FUPDATE_LIST_HOL` operation applied to the
    everywhere-undefined function, with no premises. -/
theorem holFmapAsFiniteSupportResultWitness_tlcHOL {width : Nat} [NeZero width]
    (slots : List Nat) (arguments : List (ValueHOL width)) (key : Nat) :
    ((tlcHOL slots arguments : HolFiniteMapExact Nat (HolWordLab width))).lookup key =
      FUPDATE_LIST_HOL (fun _ => none)
        (slots.zip ((arguments.map flattenHOL).flatten)) key := rfl
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

    The premise is semantically the successful-result clause of HOL
    `evaluate`, not merely a pair-shaped assumption. The wrapper is
    noncomputable only because classical choice supplies decidable membership
    procedures for `memaddrs` and `shMemaddrs`; these are implementation
    witnesses, not extra theorem premises. Its `getD (none, state)` fallback
    is unreachable by `evalPanSemRecursiveCallFiniteContext_total` and
    `evaluateHOLFinite_ne_none`. `evaluateHOLFiniteResult_eq_iff` proves that
    equality of this pair view is equivalent to a successful output of the
    assembly-marked evaluator. The 66-case
    `evalPanSemRecursiveCallFiniteContext_projection`, exposed through
    `evaluateHOLFinite_toExact`, then identifies that output and post-state
    with `evalPanSemRecursiveCallContextHOLExact` on the canonical `toExact`
    state. Its 21 recursive clauses were reviewed against HOL
    `evaluate_def` (`panSemScript.sml:556-761`); each nonrecursive clause calls
    the corresponding reviewed exact clause helper and reconstructs the
    finite-support post-state. The theorem tag therefore rests on the reviewed
    successful-evaluation semantics and the explicit finite-map translations;
    it does not tag the evaluator definition itself. -/
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
  let resultSource := PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite source
  let resultPost := PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite postState
  have hinitial := panToCrepExactInitialShapeInvariant
    source target targetLocals.targetLocals relationContext hstate hlocals
  have hsourceLocals : ∀ name value, resultSource.locals.lookup name = some value →
      isWfShapeValueHOLExact resultSource.structs value = true := by
    intro name value hlookup
    exact hinitial.1 name value (by
      simpa [resultSource, PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite,
        PanPropsShapeInvariantStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact] using hlookup)
  have hsourceGlobals : ∀ name value, resultSource.globals.lookup name = some value →
      isWfShapeValueHOLExact resultSource.structs value = true := by
    intro name value hlookup
    exact hinitial.2 name value (by
      simpa [resultSource, PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite,
        PanPropsShapeInvariantStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact] using hlookup)
  have hevalInvariant :
      PanPropsShapeInvariantStateFiniteExact.evaluateHOLFinite resultSource program =
        (some result, resultPost) := by
    have hmap := congrArg
      (fun output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
        (output.1, PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite output.2)) heval
    simpa [PanPropsShapeInvariantStateFiniteExact.evaluateHOLFinite, resultSource,
      resultPost] using hmap
  have hinvariant := evaluateIsWfShapeInvariantFiniteExact program resultSource
    (some result) resultPost hevalInvariant hsourceLocals hsourceGlobals
  have hresultWf : Flapjack.panSemResultHOLWf source.structs (some result) := by
    simpa [resultSource, PanPropsShapeInvariantStateFiniteExact.ofPanSemFinite,
      PanPropsShapeInvariantStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact] using
      hinvariant.2.2
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

/-- Exact port of HOL `slc_def` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2313-2315`):
    `slc vshs args = FEMPTY |++ ZIP (MAP FST vshs, args)`. The keys are the
    `varname` components (`MlS`) of the `(varname # shape)` pairs and the values
    are the `panSem$v` arguments (`ValueHOL width`), so the result is the
    canonical finite-support map over exact carriers. The
    `fmap_as_finite_support_result` qualifier records only that finite-support
    representation; the same-module witness below states the unconditional
    lookup-level correspondence to the raw `FUPDATE_LIST_HOL` operation. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "slc_def"
  (fmap_as_finite_support_result)]
def slcHOL {width : Nat} [NeZero width] (variables : List (MlS × ShapeHOL))
    (arguments : List (ValueHOL width)) : HolFiniteMapExact MlS (ValueHOL width) :=
  HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
    ((variables.map Prod.fst).zip arguments)

/-- Canonical standalone finite-map witness for `slcHOL`: its `lookup` is
    exactly the HOL-shaped raw `FUPDATE_LIST_HOL` operation applied to the
    everywhere-undefined function, with no premises. -/
theorem holFmapAsFiniteSupportResultWitness_slcHOL {width : Nat} [NeZero width]
    (variables : List (MlS × ShapeHOL)) (arguments : List (ValueHOL width))
    (key : MlS) :
    ((slcHOL variables arguments : HolFiniteMapExact MlS (ValueHOL width))).lookup key =
      FUPDATE_LIST_HOL (fun _ => none)
        ((variables.map Prod.fst).zip arguments) key := rfl

/-- Flapjack-only analogue of HOL `slc_tlc_rw`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:2321-2326`):
    `FEMPTY |++ ZIP (MAP FST vsh,args) = slc vsh args ∧
     FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)) = tlc ns args`.
    Both conjuncts state that the raw finite-map update on `FEMPTY` is
    definitionally the named `slc`/`tlc` constructor, over the exact
    `MlS`/`ShapeHOL`/`ValueHOL`/`HolWordLab` carriers, matching `slcHOL`/`tlcHOL`
    clause-for-clause.

    NOT an exact tagged HOL port: HOL `slc_tlc_rw` is a `Prop`-level
    two-conjunct theorem, whereas the `fmap_as_finite_support_result` qualifier
    is defined for declarations whose own result/input carrier is
    `HolFiniteMapExact`. Applying that qualifier here would only certify a lookup
    correspondence for one map and cannot express the two-equality statement, so
    the `@[hol]` tag and its witness were withdrawn (bead flapjack-4ac.5.86).
    Restoring an exact tag needs a theorem-level finite-map qualifier with
    genuine witnesses for BOTH map equalities, tracked by flapjack-4ac.5.86.1. -/
theorem slcTlcRwHOL {width : Nat} [NeZero width]
    (variables : List (MlS × ShapeHOL)) (slots : List Nat)
    (arguments : List (ValueHOL width)) :
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        ((variables.map Prod.fst).zip arguments) = slcHOL variables arguments) ∧
    (HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
        (slots.zip ((arguments.map flattenHOL).flatten)) = tlcHOL slots arguments) := by
  constructor <;> rfl

end Flapjack
