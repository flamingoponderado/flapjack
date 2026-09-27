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
  (MlS ShapeHOL ExpHOL StructContextExact isWfShapeExactHOL)

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
    (context : PanToCrepContextExact width)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact context source.locals target.locals) :
    (∀ name value, source.locals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) ∧
    (∀ name value, source.globals.lookup name = some value →
      isWfShapeValueHOLExact source.structs value = true) := by
  constructor
  · intro name value hlookup
    have hshape := panToCrepLocalsRelFiniteExact_valueShapeProjection
      context source.locals target.locals name value hlocals hlookup
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
    (relationContext : PanToCrepContextExact width)
    (evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (expression : ExpHOL width) (value : ValueHOL width)
    (output : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (hcontext : evaluationContext.state = source)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext source.locals target.locals)
    (heval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
      (.return expression) evaluationContext = some (some (.returned value), output)) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  have hinitial := panToCrepExactInitialShapeInvariant
    source target relationContext hstate hlocals
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
    (relationContext : PanToCrepContextExact width)
    (evaluationContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (exception : MlS) (expression : ExpHOL width) (value : ValueHOL width)
    (output : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (hcontext : evaluationContext.state = source)
    (hstate : panToCrepStateRelFiniteExact source target)
    (hlocals : panToCrepLocalsRelFiniteExact relationContext source.locals target.locals)
    (heval : PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
      (.raise exception expression) evaluationContext = some (some (.exception exception value), output)) :
    isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
  have hinitial := panToCrepExactInitialShapeInvariant
    source target relationContext hstate hlocals
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

end Flapjack
