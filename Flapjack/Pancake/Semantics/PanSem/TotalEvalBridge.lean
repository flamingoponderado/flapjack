import Flapjack.Pancake.Semantics.PanSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.StateBridge
import Flapjack.Pancake.Semantics.ShMemBytesBridge
import Flapjack.FfiBridge

/-!
# Production/exact agreement interface for the total `panSem$evaluate`

`Flapjack/Pancake/Semantics/PanSem/TotalEval.lean` carries the measured,
well-founded total production evaluator `panSemTotalEvaluate` over the complete
production `Prog`/`PanSemState` carrier, while
`PanSemStateFiniteExact.evaluateHOLFiniteState`
(`StateExactFiniteMap.lean`) is the total result × state evaluator over the
exact HOL carriers that the tagged line-780 `evaluate_def` equations describe.

`pc_compile_correct` (`pcCompileCorrectAt`, `PcCompileCorrect.lean`) runs the
source program with `evaluateHOLFiniteState`.  Connecting it to the executable
production evaluator needs an agreement statement: under a state relation, the
production evaluator and `evaluateHOLFiniteState` return corresponding results
and corresponding post-states.

This module supplies that interface, untagged (it is Flapjack-specific
infrastructure; there is no single HOL declaration for a production/exact
codec):

* `PanSemHOLResultRel` relates the production `PanSemHOLResult` to the exact
  `PanSemResultExact` (word payloads through `panValueToHOL`, identifiers through
  `ofString`, FFI final events through `FfiFinalEventRel`);
* `PanSemStateRelExec` is the executed-carrier counterpart of the reviewed
  `PanSemStateRel` (`StateBridge.lean`): the same 13 field conjuncts, but the
  production state carries the executed `FfiState σ` and the `ffi` field is
  compared by the checked `FfiStateRel` instead of equality.  This is the
  "correspondence for the production carrier" the assembly needs, because the
  executable evaluator is instantiated at `FfiState σ`, not `HolFfiState σ`;
* `PanSemStateRelExec.emptyLocals` / `.decClock` preserve the relation across
  the two state updates used by the no-expression leaf clauses;
* `panSemTotalEvaluate_*_agree` are the first constructor slices of the
  agreement: `Skip`, `Break`, `Continue`, `Tick`, and `Annot`.  Each returns a
  `PanSemHOLResultOptionRel` on the results and a `PanSemStateRelExec` on the
  post-states, with no fuel, target-run, or successful-result premise.

The remaining constructors are not assembled here.  They require the
production/exact expression-evaluation agreement
(`evalPanSemStateExp state e` versus `evalHOLExact exact (expToHOL e)` under
`PanSemStateRelExec`), which does not exist yet, and per-clause update
preservation for locals/globals/memory/FFI.  Those prerequisites are tracked by
child beads of `flapjack-pxn.18.4.3.77.2`; this file deliberately does not
pretend to cover a constructor whose expression path is unproved.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

/-- Result correspondence between the production `PanSemHOLResult` and the exact
    `PanSemResultExact`.  Nullary constructors match one-to-one; word payloads
    compare through `panValueToHOL`; exception identifiers through `ofString`;
    FFI final events through the checked `FfiFinalEventRel`. -/
def PanSemHOLResultRel {width : Nat} [NeZero width] :
    PanSemHOLResult (RiscV.Word width) → PanSemResultExact width → Prop
  | .error, .error => True
  | .timeOut, .timeOut => True
  | .break, .break => True
  | .continue, .continue => True
  | .returned value, .returned exactValue => panValueToHOL value = exactValue
  | .exception identifier value, .exception exactIdentifier exactValue =>
      ofString identifier = exactIdentifier ∧ panValueToHOL value = exactValue
  | .finalFfi event, .finalFfi exactEvent => FfiFinalEventRel event exactEvent
  | _, _ => False

/-- Lift `PanSemHOLResultRel` to the semantic result option (`none` is normal
    completion on both sides). -/
def PanSemHOLResultOptionRel {width : Nat} [NeZero width] :
    Option (PanSemHOLResult (RiscV.Word width)) →
      Option (PanSemResultExact width) → Prop
  | none, none => True
  | some result, some exactResult => PanSemHOLResultRel result exactResult
  | _, _ => False

/-- Executed-carrier state relation between the production `PanSemState` over
    `FfiState σ` and the exact `PanSemStateExact`.  It repeats the 13 reviewed
    conjuncts of `PanSemStateRel` (`StateBridge.lean`) but compares the `ffi`
    field through `FfiStateRel`, since the executable evaluator is instantiated
    at `FfiState σ` rather than `HolFfiState σ`. -/
def PanSemStateRelExec {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateExact 64 σ) : Prop :=
  (∀ name, NameRanged name →
      Option.map panValueToHOL (production.locals name) = exact.locals (ofString name)) ∧
  (∀ name, NameRanged name →
      Option.map panValueToHOL (production.globals name) = exact.globals (ofString name)) ∧
  panStructContextToHOL production.structs = exact.structs ∧
  (∀ name, NameRanged name →
      Option.map panLangEntryToHOL (panSemCodeLookup production.code name) =
        exact.code (ofString name)) ∧
  (∀ name, NameRanged name →
      Option.map shapeToHOL (production.exceptionShapes name) = exact.eshapes (ofString name)) ∧
  PanSemMemoryRel production.memaddrs production.memory exact.memory ∧
  (∀ address, production.memaddrs address = true ↔ exact.memaddrs address) ∧
  (∀ address, production.sharedMemaddrs address = true ↔ exact.shMemaddrs address) ∧
  exact.clock = production.clock ∧
  exact.be = production.be ∧
  FfiStateRel production.ffi exact.ffi ∧
  exact.baseAddr = production.baseAddress ∧
  exact.topAddr = production.topAddress

/-- The relation is preserved by clearing the production locals, matching HOL
    `empty_locals` (`panSemScript.sml:436`) and `emptyLocalsHOLExact`. -/
theorem PanSemStateRelExec.emptyLocals {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact) :
    PanSemStateRelExec { production with locals := fun _ => none }
      (emptyLocalsHOLExact exact) := by
  obtain ⟨_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨?_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro name _
  simp only [emptyLocalsHOLExact, Option.map_none]

/-- The relation is preserved by decrementing the production clock, matching
    HOL `dec_clock` (`panSemScript.sml:441`) and `decClockHOLExact`. -/
theorem PanSemStateRelExec.decClock {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact) :
    PanSemStateRelExec { production with clock := production.clock - 1 }
      (decClockHOLExact exact) := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨hl, hg, hs, hc, he, hm, hmd, hsm, ?_, hbe, hffi, hb, ht⟩
  show exact.clock - 1 = production.clock - 1
  rw [hck]

/-! ## Local/global value-map update preservation

The production evaluator writes `locals`/`globals` through the Boolean-keyed
`updatePanValueMap`/`resVar`, while the exact evaluator writes the same fields
through the canonical finite-map updates `setVarHOLFinite`/`setGlobalHOLFinite`
and `HolFiniteMapExact.resVarEq`.  This section proves that `PanSemStateRelExec`
is preserved by each write, comparing the lookup at the written key (the
related value is installed) and at every other key (the old related value is
kept).

The comparison needs the `Bool` key tests to agree: on byte-ranged identifiers,
the production `==` on `String` and the exact `==`/`=` on `MlS` agree through
`ofString`.  The side conditions are exactly `NameRanged name` for the written
key and `NameRanged query` for a queried key; the post-state relation is never
assumed.  Everything here is untagged Flapjack-specific bridge infrastructure. -/

/-- `ofString` is injective on byte-ranged strings. -/
theorem ofString_injective_of_ranged {a b : String} (ha : NameRanged a) (hb : NameRanged b)
    (h : ofString a = ofString b) : a = b := by
  have h' := congrArg toStringOfBytes h
  rwa [toStringOfBytes_ofString_of_bytes a ha,
    toStringOfBytes_ofString_of_bytes b hb] at h'

/-- On byte-ranged identifiers, the exact `MlS` key test of `HolFiniteMapExact`
    agrees with the production `String` key test under `ofString`. -/
theorem ofString_beq_eq_beq {a b : String} (ha : NameRanged a) (hb : NameRanged b) :
    (ofString a == ofString b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact beq_iff_eq.mpr (ofString_injective_of_ranged ha hb (beq_iff_eq.mp h))
  · intro h
    exact beq_iff_eq.mpr (by rw [beq_iff_eq.mp h])

/-- Pointwise agreement of the production `updatePanValueMap` and the exact
    `HolFiniteMapExact.update` under the value-map conjunct of
    `PanSemStateRelExec`: the written key receives the related value and every
    other key keeps its related value.  This is the lookup-level heart of
    `PanSemStateRelExec.updateLocals`/`.updateGlobals`. -/
theorem updatePanValueMap_agree (values : VarName → Option (PanValue (RiscV.Word 64)))
    (exactMap : HolFiniteMapExact MlS (ValueHOL 64))
    (hmap : ∀ query, NameRanged query →
      Option.map panValueToHOL (values query) = exactMap.lookup (ofString query))
    (name : VarName) (hname : NameRanged name) (value : PanValue (RiscV.Word 64)) :
    ∀ query, NameRanged query →
      Option.map panValueToHOL (updatePanValueMap values name value query)
        = (exactMap.update (ofString name, panValueToHOL value)).lookup (ofString query) := by
  intro query hquery
  have hold := hmap query hquery
  rw [updatePanValueMap, HolFiniteMapExact.lookup_update]
  simp only [FUPDATE]
  by_cases hq : (query == name) = true
  · have hof : (ofString name == ofString query) = true := by
      apply beq_iff_eq.mpr
      rw [beq_iff_eq.mp hq]
    simp only [hq, hof, if_true, Option.map_some]
  · have hq' : (query == name) = false := Bool.eq_false_iff.mpr hq
    have hne : query ≠ name := fun hh => hq (beq_iff_eq.mpr hh)
    have hof : (ofString name == ofString query) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro hh
      exact hne (ofString_injective_of_ranged hname hquery hh).symm
    simp only [hq', hof]
    exact hold

/-- Pointwise agreement of the production `resVar` and the exact
    `HolFiniteMapExact.resVarEq` under the value-map conjunct of
    `PanSemStateRelExec`.  Both the delete (`none`) and overwrite (`some`)
    branches are covered, at the written key and at every other key. -/
theorem resVar_agree (values : VarName → Option (PanValue (RiscV.Word 64)))
    (exactMap : HolFiniteMapExact MlS (ValueHOL 64))
    (hmap : ∀ query, NameRanged query →
      Option.map panValueToHOL (values query) = exactMap.lookup (ofString query))
    (name : VarName) (hname : NameRanged name)
    (oldValue : Option (PanValue (RiscV.Word 64))) :
    ∀ query, NameRanged query →
      Option.map panValueToHOL (resVar values (name, oldValue) query)
        = (HolFiniteMapExact.resVarEq exactMap
            (ofString name, Option.map panValueToHOL oldValue)).lookup (ofString query) := by
  intro query hquery
  have hold := hmap query hquery
  cases oldValue with
  | none =>
      simp only [Option.map_none, resVar, HolFiniteMapExact.lookup_resVarEq_none,
        FDOMSUB, FDOMSUB_HOL]
      by_cases hq : (name == query) = true
      · have hof : (ofString query = ofString name) := by
          rw [beq_iff_eq.mp hq]
        simp only [hq, hof, if_true, Option.map_none]
      · have hq' : (name == query) = false := Bool.eq_false_iff.mpr hq
        have hne : name ≠ query := fun hh => hq (beq_iff_eq.mpr hh)
        have hof : ¬ (ofString query = ofString name) :=
          fun hh => hne (ofString_injective_of_ranged hquery hname hh).symm
        simp only [hq', hof, if_false]
        exact hold
  | some v =>
      simp only [Option.map_some]
      rw [resVar, HolFiniteMapExact.lookup_resVarEq_some]
      simp only [FUPDATE, FUPDATE_HOL]
      by_cases hq : (name == query) = true
      · have hof : (ofString query = ofString name) := by
          rw [beq_iff_eq.mp hq]
        simp only [hq, hof, if_true, Option.map_some]
      · have hq' : (name == query) = false := Bool.eq_false_iff.mpr hq
        have hne : name ≠ query := fun hh => hq (beq_iff_eq.mpr hh)
        have hof : ¬ (ofString query = ofString name) :=
          fun hh => hne (ofString_injective_of_ranged hquery hname hh).symm
        simp only [hq', hof]
        exact hold

/-- `PanSemStateRelExec` is preserved by a production local assignment: the
    production `updatePanValueMap` on `locals` is paired with the exact
    `setVarHOLFinite` at the `ofString` image of the written name. -/
theorem PanSemStateRelExec.updateLocals {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact)
    (name : VarName) (hname : NameRanged name) (value : PanValue (RiscV.Word 64)) :
    PanSemStateRelExec
      { production with locals := updatePanValueMap production.locals name value }
      (setVarHOLFinite (ofString name) (panValueToHOL value) exact).toExact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨?_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro query hquery
  exact updatePanValueMap_agree production.locals exact.locals hl name hname value query hquery

/-- `PanSemStateRelExec` is preserved by a production global assignment, paired
    with the exact `setGlobalHOLFinite`. -/
theorem PanSemStateRelExec.updateGlobals {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact)
    (name : VarName) (hname : NameRanged name) (value : PanValue (RiscV.Word 64)) :
    PanSemStateRelExec
      { production with globals := updatePanValueMap production.globals name value }
      (setGlobalHOLFinite (ofString name) (panValueToHOL value) exact).toExact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨hl, ?_, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro query hquery
  exact updatePanValueMap_agree production.globals exact.globals hg name hname value query hquery

/-- `PanSemStateRelExec` is preserved by a production `resVar` restore on
    `locals`, paired with the exact `HolFiniteMapExact.resVarEq`.  The saved
    value is compared through `panValueToHOL`, covering both the delete and
    overwrite branches. -/
theorem PanSemStateRelExec.resVarLocals {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateFiniteExact 64 σ}
    (h : PanSemStateRelExec production exact.toExact)
    (name : VarName) (hname : NameRanged name)
    (oldValue : Option (PanValue (RiscV.Word 64))) :
    PanSemStateRelExec
      { production with locals := resVar production.locals (name, oldValue) }
      ({ exact with
        locals := HolFiniteMapExact.resVarEq exact.locals
          (ofString name, Option.map panValueToHOL oldValue) }).toExact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨?_, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
  intro query hquery
  exact resVar_agree production.locals exact.locals hl name hname oldValue query hquery

/-- Production/exact agreement for the `Assign` constructor's state path: given
    the evaluated value correspondence and the validity correspondence supplied
    by `TotalEvalExpBridge` (the expression agreement and the production/exact
    validity parity), the production `Assign` clause and the exact
    `evaluateHOLFiniteState` `Assign` equation return corresponding results and
    related post-states.  The local and global preservation lemmas are the only
    state-update ingredients. -/
theorem panSemTotalAssignClause_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (kind : VarKind) (name : VarName) (hname : NameRanged name)
    (e : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp production e = some value)
    (hexactEval : @evalHOLExact 64 σ _ exact.toExact
        (fun address => Classical.propDecidable (exact.memaddrs address)) (expToHOL e)
      = some (panValueToHOL value))
    (hvalid : panValueAssignmentValid production.structs production.locals
      production.globals kind name value = true)
    (hexactValid : isValidValueHOLFinite exact kind (ofString name)
      (panValueToHOL value) = true) :
    PanSemHOLResultOptionRel
        (panSemTotalAssignClause production kind name e).1
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).1 ∧
      PanSemStateRelExec
        (panSemTotalAssignClause production kind name e).2
        (evaluateHOLFiniteState exact (.assign kind (ofString name) (expToHOL e))).2.toExact := by
  rw [panSemTotalAssignClause_normal production kind name e value heval hvalid]
  rw [evaluateHOLFiniteState_assign, hexactEval]
  simp only [hexactValid, if_true]
  constructor
  · trivial
  · cases kind
    · exact PanSemStateRelExec.updateLocals hrel name hname value
    · exact PanSemStateRelExec.updateGlobals hrel name hname value

/-- Production/exact agreement for the `Primitive` clause.  Under the state
    relation, the evaluated argument-list correspondence, and the handler
    correspondence — the production handler `primitive` maps, through
    `panValueToHOL`, to the exact `panPrimopHOLExact` on the encoded argument
    list, with the assignment-validity tests agreeing on the produced value — the
    production `panSemTotalPrimitiveClause` and the exact
    `evaluateHOLFiniteState` `Primitive` equation (`panSemScript.sml:573-582`,
    `evaluateHOLFiniteState_primitive`) return corresponding results and related
    post-states on the successful-valid, successful-invalid, and handler-`none`
    branches.  Neither a target run, nor a target result, nor a post-state
    relation is assumed: the handler correspondence and the validity parity are
    the input side conditions, exactly as `panSemTotalAssignClause_agree` takes
    the evaluated value and its validity parity.  Flapjack-only bridge; no HOL
    declaration. -/
theorem panSemTotalPrimitiveClause_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (name : VarName) (hname : NameRanged name) (operator : PrimOp)
    (arguments : List (Exp (RiscV.Word 64)))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (values : List (PanValue (RiscV.Word 64)))
    (heval : evalPanSemStateExps production arguments = some values)
    (hexactEval : @evalListHOLExact 64 σ _ exact.toExact
        (fun address => Classical.propDecidable (exact.memaddrs address))
        (arguments.map expToHOL)
      = some (values.map panValueToHOL))
    (hprim : Option.map panValueToHOL (primitive operator values)
      = panPrimopHOLExact operator (values.map panValueToHOL))
    (hvalid : ∀ value, primitive operator values = some value →
      panValueAssignmentValid production.structs production.locals production.globals
          .local name value
        = isValidValueHOLFinite exact .local (ofString name) (panValueToHOL value)) :
    PanSemHOLResultOptionRel
        (panSemTotalPrimitiveClause production name operator arguments primitive).1
        (evaluateHOLFiniteState exact
          (.primitive (ofString name) operator (arguments.map expToHOL))).1 ∧
      PanSemStateRelExec
        (panSemTotalPrimitiveClause production name operator arguments primitive).2
        (evaluateHOLFiniteState exact
          (.primitive (ofString name) operator (arguments.map expToHOL))).2.toExact := by
  simp only [evaluateHOLFiniteState_primitive, hexactEval]
  cases hprimOpt : primitive operator values with
  | none =>
      have hexactNone : panPrimopHOLExact operator (values.map panValueToHOL) = none := by
        rw [← hprim, hprimOpt]
        rfl
      rw [panSemTotalPrimitiveClause_primNone production name operator arguments primitive
        values heval hprimOpt, hexactNone]
      exact ⟨trivial, hrel⟩
  | some value =>
      have hexactSome : panPrimopHOLExact operator (values.map panValueToHOL)
          = some (panValueToHOL value) := by
        rw [← hprim, hprimOpt]
        rfl
      simp only [hexactSome]
      have hv := hvalid value hprimOpt
      by_cases hvalidProd : panValueAssignmentValid production.structs production.locals
          production.globals .local name value = true
      · have hvalidExact : isValidValueHOLFinite exact .local (ofString name)
            (panValueToHOL value) = true := by
          rw [← hv]
          exact hvalidProd
        rw [panSemTotalPrimitiveClause_ok production name operator arguments primitive
          values value heval hprimOpt hvalidProd, hvalidExact]
        exact ⟨trivial, PanSemStateRelExec.updateLocals hrel name hname value⟩
      · have hvalidProdFalse : panValueAssignmentValid production.structs production.locals
            production.globals .local name value = false := Bool.eq_false_iff.mpr hvalidProd
        have hvalidExactFalse : isValidValueHOLFinite exact .local (ofString name)
            (panValueToHOL value) = false := by
          rw [← hv]
          exact hvalidProdFalse
        rw [panSemTotalPrimitiveClause_invalid production name operator arguments primitive
          values value heval hprimOpt hvalidProdFalse, hvalidExactFalse]
        exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `Skip` clause: both sides return normal
    completion and carry the state unchanged. -/
theorem panSemTotalEvaluate_skip_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.skip : Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.skip : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.skip : Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.skip : ProgHOL 64)).2.toExact := by
  rw [panSemTotalEvaluate]
  simp only [panSemEvaluateClockLeaf_skip, evaluateHOLFiniteState_skip]
  exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `Break` clause. -/
theorem panSemTotalEvaluate_break_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.break : Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.break : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.break : Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.break : ProgHOL 64)).2.toExact := by
  rw [panSemTotalEvaluate]
  simp only [panSemEvaluateClockLeaf_break, evaluateHOLFiniteState_break]
  exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `Continue` clause. -/
theorem panSemTotalEvaluate_continue_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.continue : Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.continue : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.continue : Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.continue : ProgHOL 64)).2.toExact := by
  rw [panSemTotalEvaluate]
  simp only [panSemEvaluateClockLeaf_continue, evaluateHOLFiniteState_continue]
  exact ⟨trivial, hrel⟩

/-- Production/exact agreement for the `Tick` clause: both sides clear the locals
    and time out at clock zero, and otherwise decrement the clock. -/
theorem panSemTotalEvaluate_tick_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive (.tick : Prog (RiscV.Word 64)) production).1
        (evaluateHOLFiniteState exact (.tick : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive (.tick : Prog (RiscV.Word 64)) production).2
        (evaluateHOLFiniteState exact (.tick : ProgHOL 64)).2.toExact := by
  have hrelKeep := hrel
  obtain ⟨_, _, _, _, _, _, _, _, hclock, _, _, _, _⟩ := hrel
  have hcl : exact.clock = production.clock := by simpa using hclock
  rw [panSemTotalEvaluate]
  by_cases h : production.clock = 0
  · have he : exact.clock = 0 := by rw [hcl, h]
    rw [panSemEvaluateClockLeaf_tick_zero production h,
      evaluateHOLFiniteState_tick, if_pos he]
    refine ⟨trivial, ?_⟩
    simpa only [toExact_emptyLocalsHOLFinite] using PanSemStateRelExec.emptyLocals hrelKeep
  · have he : exact.clock ≠ 0 := by rw [hcl]; exact h
    rw [panSemEvaluateClockLeaf_tick_positive production h,
      evaluateHOLFiniteState_tick, if_neg he]
    refine ⟨trivial, ?_⟩
    simpa only [toExact_decClockHOLFinite] using PanSemStateRelExec.decClock hrelKeep

/-- Production/exact agreement for the `Annot` clause: both sides return normal
    completion and carry the state unchanged. -/
theorem panSemTotalEvaluate_annot_agree {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact) (tag text : MlS) :
    PanSemHOLResultOptionRel
        (panSemTotalEvaluate primitive
          (.annot (toStringOfBytes tag) (toStringOfBytes text) : Prog (RiscV.Word 64))
          production).1
        (evaluateHOLFiniteState exact (.annot tag text : ProgHOL 64)).1 ∧
      PanSemStateRelExec
        (panSemTotalEvaluate primitive
          (.annot (toStringOfBytes tag) (toStringOfBytes text) : Prog (RiscV.Word 64))
          production).2
        (evaluateHOLFiniteState exact (.annot tag text : ProgHOL 64)).2.toExact := by
  rw [panSemTotalEvaluate]
  simp only [evaluateHOLFiniteState_annot]
  exact ⟨trivial, hrel⟩

/-! ## Production memory `Store` and HOL `mem_stores`

The production `Store` clause (`panSemTotalStoreClause`) writes the flattened
value with `panValueStoreWithAccess` and the state-derived word store; the exact
`Store` clause writes `flatten v` with the tagged `panMemStoresHOL` (HOL
`mem_stores`, `panSemScript.sml:379-386`). The lemmas below show the two agree
on success/failure and preserve `PanSemStateRelExec` with the memories
updated (bead `flapjack-pxn.18.4.3.77.2.13.2.1`); the next use is the `Store`
constructor agreement once expression agreement is unconditional. Flapjack-only
bridge infrastructure, no HOL declaration. -/

private theorem panValueFlatWordsFuel_toHOL {width : Nat} [NeZero width] :
    ∀ n : Nat,
      (∀ v : PanValue (BitVec width), 2 * panValueFlatValueFuel v ≤ n + 1 →
        (panValueFlatWordsFuel n v).map HolWordLab.word = flattenHOL (panValueToHOL v)) ∧
      (∀ vs : List (PanValue (BitVec width)),
        2 * panValueFlatValueFuel.panValueFlatValueListFuel vs ≤ n →
        (panValueFlatWordsFuel.panValueFlatWordsListFuel n vs).map HolWordLab.word =
          (vs.map (fun v => flattenHOL (panValueToHOL v))).flatten) ∧
      (∀ fs : List (FieldName × PanValue (BitVec width)),
        2 * panValueFlatValueFuel.panValueFlatValueFieldListFuel fs ≤ n →
        (panValueFlatWordsFuel.panValueFlatWordsFieldListFuel n fs).map HolWordLab.word =
          (fs.map (fun f => flattenHOL (panValueToHOL f.2))).flatten)
  | 0 => by
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        cases v <;> simp [panValueFlatValueFuel] at hv <;> omega
      · intro vs hvs
        cases vs with
        | nil => simp [panValueFlatWordsFuel.panValueFlatWordsListFuel]
        | cons v vs =>
            have : 1 ≤ panValueFlatValueFuel v := by cases v <;> simp [panValueFlatValueFuel]
            simp [panValueFlatValueFuel.panValueFlatValueListFuel] at hvs
            omega
      · intro fs hfs
        cases fs with
        | nil => simp [panValueFlatWordsFuel.panValueFlatWordsFieldListFuel]
        | cons f fs =>
            have : 1 ≤ panValueFlatValueFuel f.2 := by
              cases f.2 <;> simp [panValueFlatValueFuel]
            simp [panValueFlatValueFuel.panValueFlatValueFieldListFuel] at hfs
            omega
  | n + 1 => by
      obtain ⟨ihv, ihl, ihf⟩ := panValueFlatWordsFuel_toHOL (width := width) n
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        cases v with
        | word w =>
            unfold panValueToHOL flattenHOL
            simp [panValueFlatWordsFuel]
        | rStruct fields =>
            simp only [panValueFlatValueFuel] at hv
            rw [panValueFlatWordsFuel, ihl fields (by omega), panValueToHOL.eq_2, flattenHOL.eq_2]
            simp [List.map_map, Function.comp_def]
        | nStruct name fields =>
            simp only [panValueFlatValueFuel] at hv
            rw [panValueFlatWordsFuel, ihf fields (by omega), panValueToHOL.eq_3, flattenHOL.eq_3]
            simp [List.map_map, Function.comp_def]
      · intro vs hvs
        cases vs with
        | nil => simp [panValueFlatWordsFuel.panValueFlatWordsListFuel]
        | cons v vs =>
            have h1 : 1 ≤ panValueFlatValueFuel v := by cases v <;> simp [panValueFlatValueFuel]
            simp only [panValueFlatValueFuel.panValueFlatValueListFuel] at hvs
            rw [panValueFlatWordsFuel.panValueFlatWordsListFuel, List.map_append,
              ihv v (by omega), ihl vs (by omega)]
            simp
      · intro fs hfs
        cases fs with
        | nil => simp [panValueFlatWordsFuel.panValueFlatWordsFieldListFuel]
        | cons f fs =>
            obtain ⟨name, v⟩ := f
            have h1 : 1 ≤ panValueFlatValueFuel v := by cases v <;> simp [panValueFlatValueFuel]
            simp only [panValueFlatValueFuel.panValueFlatValueFieldListFuel] at hfs
            rw [panValueFlatWordsFuel.panValueFlatWordsFieldListFuel, List.map_append,
              ihv v (by omega), ihf fs (by omega)]
            simp

/-- The production flattening `panValueFlatWords` is the exact HOL `flatten` of the
    `panValueToHOL` image, word by word. -/
theorem panValueFlatWords_map_word {width : Nat} [NeZero width] (v : PanValue (BitVec width)) :
    (panValueFlatWords v).map HolWordLab.word = flattenHOL (panValueToHOL v) :=
  (panValueFlatWordsFuel_toHOL (width := width) _).1 v (by omega)

/-- Outcome agreement of a production memory update with an exact one: both
    fail, or both succeed with related memories. -/
private def panStoreOutcomeRel {width : Nat} [NeZero width]
    (memaddrs : RiscV.Word width → Bool) :
    Option (RiscV.Word width → Option (PanValue (BitVec width))) →
      Option (RiscV.Word width → HolWordLab width) → Prop
  | some m, some m' => PanSemMemoryRel memaddrs m m'
  | none, none => True
  | _, _ => False

/-- Storing a word list through the production state-derived word store agrees
    with HOL `mem_stores` (`panSemScript.sml:379-386`) at the related memory. -/
private theorem panValueFlatStoreWords_rel {ffiState : Type}
    (state : PanSemState (RiscV.Word 64) ffiState)
    (D : RiscV.Word 64 → Prop) [DecidablePred D]
    (hdom : ∀ a, state.memaddrs a = true ↔ D a) :
    ∀ (ws : List (RiscV.Word 64)) (addr : RiscV.Word 64)
      (mem : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
      (emem : RiscV.Word 64 → HolWordLab 64),
      PanSemMemoryRel state.memaddrs mem emem →
      panStoreOutcomeRel state.memaddrs
        (panValueFlatStoreWords
          (fun memory address value =>
            (panSemBitVec64MemoryAccess state).storeWord
              (panSemBitVec64MemoryAccess state).domain memory panSemBitVec64BytesInWord
              address value)
          panSemBitVec64BytesInWord mem addr ws)
        (panMemStoresHOL addr (ws.map HolWordLab.word) D emem)
  | [], addr, mem, emem, hrel => by
      simp [panValueFlatStoreWords, panStoreOutcomeRel, hrel]
  | w :: ws, addr, mem, emem, hrel => by
      by_cases hd : state.memaddrs addr = true
      · have hD : D addr := (hdom addr).mp hd
        have hstep := panSemMemoryRel_update state.memaddrs mem emem hrel addr w
        have ih := panValueFlatStoreWords_rel state D hdom ws (addr + panSemBitVec64BytesInWord)
          _ _ hstep
        have hb : panBytesInWord 64 = panSemBitVec64BytesInWord := rfl
        simp only [panValueFlatStoreWords, List.map_cons, panMemStoresHOL,
          panMemStoreHOL, if_pos hD, hb]
        simpa [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel, hd,
          panValueFlatOffset] using ih
      · have hD : ¬ D addr := fun h => hd ((hdom addr).mpr h)
        simp [panValueFlatStoreWords, panMemStoresHOL, panMemStoreHOL, hD,
          panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel, hd, panStoreOutcomeRel]

/-- `PanSemStateRelExec` through the production `Store` memory update
    (`panValueStoreWithAccess` with the state-derived word store, as used by
    `panSemTotalStoreClause`) and the exact HOL `mem_stores (flatten v)`
    (`panSemScript.sml:379-386`, the tagged `panMemStoresHOL`) used by the exact
    `Store` clause: either both fail, or both succeed and the relation holds with
    the two memories updated. Flapjack-only bridge; no HOL declaration. -/
theorem panSemStateRelExec_storeWithAccess {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (exact : PanSemStateExact 64 σ)
    (h : PanSemStateRelExec state exact) (addr : RiscV.Word 64)
    (v : PanValue (RiscV.Word 64)) :
    match panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr v
        (some (panSemBitVec64MemoryAccess state)),
      @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
        (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory with
    | some m, some m' =>
        PanSemStateRelExec { state with memory := m } { exact with memory := m' }
    | none, none => True
    | _, _ => False := by
  classical
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  have L := @panValueFlatStoreWords_rel _ state exact.memaddrs
    (fun a => Classical.propDecidable (exact.memaddrs a)) hmd (panValueFlatWords v) addr
    state.memory exact.memory hm
  rw [panValueFlatWords_map_word] at L
  simp only [panValueStoreWithAccess]
  revert L
  cases panValueFlatStoreWords
      (fun memory address value =>
        (panSemBitVec64MemoryAccess state).storeWord
          (panSemBitVec64MemoryAccess state).domain memory panSemBitVec64BytesInWord
          address value)
      panSemBitVec64BytesInWord state.memory addr (panValueFlatWords v) <;>
    cases @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
      (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory <;>
    simp [panStoreOutcomeRel]
  intro hrel
  exact ⟨hl, hg, hs, hc, he, hrel, hmd, hsm, hck, hbe, hffi, hb, ht⟩

/-- Destructured form of `panSemStateRelExec_storeWithAccess`: the production
    store and the exact HOL `mem_stores (flatten v)` either both fail
    (`none`/`none`) or both succeed (`some m`/`some m'`) with the relation
    preserved on the updated memories.  This is the case analysis the `Store`
    clause agreement consumes.  Flapjack-only bridge; no HOL declaration. -/
private theorem panStoreWithAccess_outcome {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (h : PanSemStateRelExec state exact.toExact) (addr : RiscV.Word 64)
    (v : PanValue (RiscV.Word 64)) :
    (panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr v
        (some (panSemBitVec64MemoryAccess state)) = none ∧
      @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
        (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory = none) ∨
    (∃ m m', panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr v
        (some (panSemBitVec64MemoryAccess state)) = some m ∧
      @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
        (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory = some m' ∧
      PanSemStateRelExec { state with memory := m } { exact.toExact with memory := m' }) := by
  have hb := panSemStateRelExec_storeWithAccess state exact.toExact h addr v
  cases hs : panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr v
      (some (panSemBitVec64MemoryAccess state)) with
  | none =>
      rw [hs] at hb
      cases he : @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
          (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some m' => rw [he] at hb; exact False.elim hb
  | some m =>
      rw [hs] at hb
      cases he : @panMemStoresHOL 64 _ addr (flattenHOL (panValueToHOL v)) exact.memaddrs
          (fun a => Classical.propDecidable (exact.memaddrs a)) exact.memory with
      | none => rw [he] at hb; exact False.elim hb
      | some m' => exact Or.inr ⟨m, m', rfl, rfl, by rw [he] at hb; exact hb⟩

/-- Production/exact agreement for the `Store` clause.  Under the state
    relation and the evaluated destination (a word `addr`) and source
    (`storedValue`) correspondences — no target run, result, or post-state
    premise — the production `panSemTotalStoreClause` and the exact
    `evaluateHOLFiniteState` `Store` equation (`panSemScript.sml:583-589`,
    `evaluateHOLFiniteState_store`) return corresponding results and related
    post-states.  The success/failure split is exactly
    `panSemStateRelExec_storeWithAccess`.  Flapjack-only bridge; no HOL
    declaration. -/
theorem panSemTotalStoreClause_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (address value : Exp (RiscV.Word 64)) (addr : RiscV.Word 64)
    (storedValue : PanValue (RiscV.Word 64))
    (hevalAddr : evalPanSemStateExp production address = some (.word addr))
    (hevalValue : evalPanSemStateExp production value = some storedValue)
    (hexactAddr : @evalHOLExact 64 σ _ exact.toExact
        (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL address)
      = some (.val (.word addr)))
    (hexactValue : @evalHOLExact 64 σ _ exact.toExact
        (fun a => Classical.propDecidable (exact.memaddrs a)) (expToHOL value)
      = some (panValueToHOL storedValue)) :
    PanSemHOLResultOptionRel
        (panSemTotalStoreClause production address value).1
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).1 ∧
      PanSemStateRelExec
        (panSemTotalStoreClause production address value).2
        (evaluateHOLFiniteState exact (.store (expToHOL address) (expToHOL value))).2.toExact := by
  simp only [evaluateHOLFiniteState_store, hexactAddr, hexactValue]
  have hout := panStoreWithAccess_outcome production exact hrel addr storedValue
  rcases hout with ⟨hs, he⟩ | ⟨m, m', hs, he, hrel'⟩
  · have hclause : panSemTotalStoreClause production address value = (some .error, production) := by
      simp [panSemTotalStoreClause, panSemTotalExprStep, hevalAddr, hevalValue, hs]
    rw [hclause, he]
    exact ⟨trivial, hrel⟩
  · have hclause := panSemTotalStoreClause_ok production address value addr storedValue m
        hevalAddr hevalValue hs
    rw [hclause, he]
    exact ⟨trivial, hrel'⟩

/-- `PanSemStateRelExec` through the production `StoreByte` memory update (the
    state-derived `storeByte` used by `panSemTotalStoreByteClause`) and the exact
    HOL `mem_store_byte s.memory s.memaddrs s.be adr (w2w w)`
    (`panSemScript.sml:300-307`, the tagged `panMemStoreByteWord8HOL`) used by
    the exact `StoreByte` clause: either both fail, or both succeed and the
    relation holds with the memories updated. The production store writes the
    full word into `set_byte`, which uses only its low byte, so it agrees with
    HOL's `w2w` truncation. Flapjack-only bridge; no HOL declaration. -/
theorem panSemStateRelExec_storeByte {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (exact : PanSemStateExact 64 σ)
    (h : PanSemStateRelExec state exact) (addr w : RiscV.Word 64) :
    match (panSemBitVec64MemoryAccess state).storeByte (panSemBitVec64MemoryAccess state).domain
        state.memory panSemBitVec64BytesInWord addr w,
      @panMemStoreByteWord8HOL 64 _ exact.memory exact.memaddrs
        (fun a => Classical.propDecidable (exact.memaddrs a)) exact.be addr
        (BitVec.ofNat 8 w.toNat) with
    | some m, some m' =>
        PanSemStateRelExec { state with memory := m } { exact with memory := m' }
    | none, none => True
    | _, _ => False := by
  classical
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  have hbyte : panSetByteHOL addr w (holWordLabBits (exact.memory (panByteAlignHOL addr)))
      state.be =
      panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 w.toNat).toNat)
        (holWordLabBits (exact.memory (panByteAlignHOL addr))) exact.be := by
    rw [hbe]
    unfold panSetByteHOL
    congr 3
    simp [BitVec.toNat_ofNat]
  by_cases hd : state.memaddrs (panByteAlignHOL addr) = true
  · have hD : exact.memaddrs (panByteAlignHOL addr) := (hmd _).mp hd
    have hcell := hm _ hd
    have hupd := panSemMemoryRel_update state.memaddrs state.memory exact.memory hm
      (panByteAlignHOL addr)
      (panSetByteHOL addr w (holWordLabBits (exact.memory (panByteAlignHOL addr))) state.be)
    cases hex : exact.memory (panByteAlignHOL addr) with
    | word bits =>
        rw [hex] at hcell hbyte hupd
        simp only [holWordLabBits_word] at hcell hbyte hupd
        simp only [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
          panSemBitVec64WordModel, panSemWordModel, panMemStoreByteWord8HOL, hex, hd, hD,
          if_true, hcell]
        refine ⟨hl, hg, hs, hc, he, ?_, hmd, hsm, hck, hbe, hffi, hb, ht⟩
        rw [← hbyte]
        exact hupd
  · have hD : ¬ exact.memaddrs (panByteAlignHOL addr) := fun h => hd ((hmd _).mpr h)
    cases hex : exact.memory (panByteAlignHOL addr) with
    | word bits =>
        simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
          panSemBitVec64WordModel, panSemWordModel, panMemStoreByteWord8HOL, hd, hD]

/-! ## Clock and FFI post-state preservation

The agreement proofs for the recursive clauses need `PanSemStateRelExec` to
survive the production state updates they perform.  `fixClock` covers the
`panSemFixClock` clamp applied after a recursive call, and the `ffi`-field
lemmas cover the `ExtCall`/shared-memory FFI branches: `setFfi` is the generic
`ffi` replacement, `ffiReturned` consumes a `FfiResultRel` whose production side
is `FfiResult.returned` and exact side is `HolFfiResult.ret` (the shape every
`Flapjack/FfiBridge.lean` `..._success_bridge`/`..._oracleFinal`/`..._lengthFailure`
bridge and the identity `callFfi_empty_extCall_bridge` produce), and `ffiFinal`
records that a finalising result installs no new FFI state.  All are untagged
Flapjack-specific bridge infrastructure. -/

/-- `PanSemStateRelExec` is preserved by the production fix-clock
    `panSemFixClock` (`Total.lean:453`), which clamps the returned clock with
    `min`, and by clamping the exact clock by the same `min`.  Only the clock
    conjunct changes; every other field is carried over unchanged. -/
theorem PanSemStateRelExec.fixClock {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (entryClock : Nat) (h : PanSemStateRelExec production exact) :
    PanSemStateRelExec (panSemFixClock entryClock production)
      { exact with clock := min entryClock exact.clock } := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  refine ⟨hl, hg, hs, hc, he, hm, hmd, hsm, ?_, hbe, hffi, hb, ht⟩
  simp only [panSemFixClock]
  show min entryClock exact.clock = min entryClock production.clock
  rw [hck]

/-- Installing new FFI states on both sides preserves `PanSemStateRelExec`
    whenever they are related by `FfiStateRel`.  Every non-`ffi` field of the
    premise is carried over, so only the `ffi` conjunct is re-established. -/
theorem PanSemStateRelExec.setFfi {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact)
    {newProduction : FfiState σ} {newExact : HolFfiState σ}
    (hffi : FfiStateRel newProduction newExact) :
    PanSemStateRelExec { production with ffi := newProduction }
      { exact with ffi := newExact } := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, _, hb, ht⟩ := h
  exact ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩

/-- The returned/`ret` FFI branch.  Whenever a production `FfiResult.returned`
    is related to an exact `HolFfiResult.ret` by `FfiResultRel`, the production
    state installs the returned production FFI state, the exact state installs
    the returned exact FFI state, and `PanSemStateRelExec` is preserved.  The
    `FfiStateRel` of the returned states is the first component of the
    `FfiResultRel`, so this covers the external-call, shared-memory and
    empty-extCall successes without re-proving any byte or event equality. -/
theorem PanSemStateRelExec.ffiReturned {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact)
    {prodResult : FfiResult σ} {exactResult : HolFfiResult σ}
    (hbridge : FfiResultRel prodResult exactResult)
    {newProduction : FfiState σ} {newExact : HolFfiState σ}
    {prodBytes : List UInt8} {exactBytes : List (BitVec 8)}
    (hprod : prodResult = .returned newProduction prodBytes)
    (hexact : exactResult = .ret newExact exactBytes) :
    PanSemStateRelExec { production with ffi := newProduction }
      { exact with ffi := newExact } := by
  rw [hprod, hexact] at hbridge
  exact PanSemStateRelExec.setFfi h hbridge.1

/-- The returned/`ret` branch specialised to the executed `callFfi` against the
    exact `callFFIHOL`, so a `Flapjack/FfiBridge.lean` bridge
    (`callFfi_extCall_success_bridge`, `callFfi_sharedMem_success_bridge`,
    `callFfi_empty_extCall_bridge`, …) plugs in directly as `hbridge`. -/
theorem PanSemStateRelExec.callFfiReturned {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact)
    (name : FfiName) (holName : HolFfiName)
    (configuration bytes : List UInt8)
    (holConfiguration holBytes : List (BitVec 8))
    {newProduction : FfiState σ} {newExact : HolFfiState σ}
    {prodBytes : List UInt8} {exactBytes : List (BitVec 8)}
    (hbridge : FfiResultRel
      (callFfi production.ffi name configuration bytes)
      (callFFIHOL exact.ffi holName holConfiguration holBytes))
    (hprod : callFfi production.ffi name configuration bytes =
      .returned newProduction prodBytes)
    (hexact : callFFIHOL exact.ffi holName holConfiguration holBytes =
      .ret newExact exactBytes) :
    PanSemStateRelExec { production with ffi := newProduction }
      { exact with ffi := newExact } :=
  PanSemStateRelExec.ffiReturned h hbridge hprod hexact

/-- The finalising FFI branch (oracle finalisation or returned-length failure).
    A finalising `callFfi`/`callFFIHOL` installs no new FFI state, so both `ffi`
    fields stay as they were and `PanSemStateRelExec` is preserved.  The
    `FfiResultRel` `.final`/`.final` port is exactly the `FfiFinalEventRel` of
    the emitted final event and constrains no state. -/
theorem PanSemStateRelExec.ffiFinal {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    {event : FfiFinalEvent} {holEvent : HolFinalEvent}
    (h : PanSemStateRelExec production exact)
    (hbridge : FfiResultRel (.final event : FfiResult σ)
      (.final holEvent : HolFfiResult σ)) :
    FfiFinalEventRel event holEvent ∧ PanSemStateRelExec production exact :=
  ⟨hbridge, h⟩

/-- The identity empty-`extCall` branch of
    `callFfi_empty_extCall_bridge`: `callFfi` and `callFFIHOL` both return their
    FFI state unchanged, so the post-state relation is the pre-state relation.
    This is the branch where the appended event list is empty on both sides. -/
theorem PanSemStateRelExec.callFfi_empty_extCall {σ : Type}
    {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ}
    (h : PanSemStateRelExec production exact)
    (configuration bytes : List UInt8) :
    FfiResultRel (callFfi production.ffi (.extCall "") configuration bytes)
      (callFFIHOL exact.ffi (.extCall (.implode []))
        (configuration.map byteToBits) (bytes.map byteToBits)) ∧
      PanSemStateRelExec production exact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  exact ⟨callFfi_empty_extCall_bridge production.ffi exact.ffi hffi configuration bytes,
    ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩⟩

private theorem panSetByteHOL_congr' {width : Nat} {a a' b b' c c' : RiscV.Word width}
    (be : Bool) (ha : a = a') (hb : b.toNat % 256 = b'.toNat % 256) (hc : c = c') :
    panSetByteHOL a b c be = panSetByteHOL a' b' c' be := by
  subst ha; subst hc
  unfold panSetByteHOL
  rw [hb]

/-- Byte `k` of the executed store (little-endian byte `k` of the 64-bit value)
    is HOL's `get_byte i (w2w w) be` byte, modulo 256, for the endianness-mapped
    index. -/
private theorem store32_byte_eq (w : RiscV.Word 64) (be : Bool) (i : Nat) (hi : i < 4) :
    (BitVec.ofNat 64
        (panGetByteWord8HOL (BitVec.ofNat 64 (if be then 3 - i else i)) w false).toNat).toNat
        % 256 =
      (BitVec.ofNat 64
        (panGetByteHOL (width := 32) (BitVec.ofNat 32 i) (BitVec.ofNat 32 w.toNat) be).toNat).toNat
        % 256 := by
  unfold panGetByteWord8HOL panGetByteHOL
  have hw := w.isLt
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    cases be <;>
    simp [BitVec.toNat_ofNat, UInt8.toNat_ofNat'] <;> omega

private theorem memRel_update_eq {width : Nat} [NeZero width]
    (memaddrs : RiscV.Word width → Bool)
    (memory : RiscV.Word width → Option (PanValue (BitVec width)))
    (exactMemory : RiscV.Word width → HolWordLab width)
    (hrel : PanSemMemoryRel memaddrs memory exactMemory)
    (address : RiscV.Word width) (v v' : BitVec width) (hv : v = v') :
    PanSemMemoryRel memaddrs
      (fun current => if current == address then some (.word v) else memory current)
      (fun current => if current = address then .word v' else exactMemory current) := by
  subst hv
  exact panSemMemoryRel_update memaddrs memory exactMemory hrel address v

/-- `PanSemStateRelExec` through the production `Store32` memory update (the
    state-derived `store32` used by `panSemTotalStore32Clause`) and the exact
    HOL `mem_store_32 s.memory s.memaddrs s.be adr (w2w w)`
    (`panSemScript.sml`, the tagged `panMemStore32HOL`) used by the exact
    `Store32` clause: both fail on a misaligned address or an out-of-domain
    aligned cell, or both succeed and the relation holds with the memories
    updated. The four production byte writes agree with HOL's
    `get_byte i (w2w w) be` modulo 256 in both endiannesses
    (bead `flapjack-pxn.18.4.3.77.2.13.2.3`, after the executed Store32 fix
    `.2.3.1`). Flapjack-only bridge; no HOL declaration. -/
theorem panSemStateRelExec_store32 {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (exact : PanSemStateExact 64 σ)
    (h : PanSemStateRelExec state exact) (addr w : RiscV.Word 64) :
    match (panSemBitVec64MemoryAccess state).store32 (panSemBitVec64MemoryAccess state).domain
        state.memory panSemBitVec64BytesInWord addr w,
      @panMemStore32HOL 64 _ exact.memory exact.memaddrs
        (fun a => Classical.propDecidable (exact.memaddrs a)) exact.be addr
        (BitVec.ofNat 32 w.toNat) with
    | some m, some m' =>
        PanSemStateRelExec { state with memory := m } { exact with memory := m' }
    | none, none => True
    | _, _ => False := by
  classical
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ := h
  by_cases hal : addr.toNat % 4 = 0
  · by_cases hd : state.memaddrs (panByteAlignHOL addr) = true
    · have hD : exact.memaddrs (panByteAlignHOL addr) := (hmd _).mp hd
      have hcell := hm _ hd
      cases hex : exact.memory (panByteAlignHOL addr) with
      | word bits =>
          rw [hex] at hcell
          simp only [holWordLabBits_word] at hcell
          simp only [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
            panSemBitVec64WordModel, panSemWordModel, RiscV.panRiscVMemoryModel,
            RiscV.aligned, panMemStore32HOL, hex, hd, hD, hal, hcell, if_true,
            decide_true]
          rw [hbe]
          have key : ∀ be : Bool, ∀ i, i < 4 →
              (BitVec.ofNat 64 (panGetByteWord8HOL
                (BitVec.ofNat 64 (if be then 3 - i else i)) w false).toNat).toNat % 256 =
              (BitVec.ofNat 64 (panGetByteHOL (width := 32) (BitVec.ofNat 32 i)
                (BitVec.ofNat 32 w.toNat) be).toNat).toNat % 256 :=
            fun be i hi => store32_byte_eq w be i hi
          by_cases hB : state.be = true
          · simp only [hB, if_true]
            refine ⟨hl, hg, hs, hc, he, memRel_update_eq _ _ _ hm _ _ _ ?_, hmd, hsm, hck,
              ?_, hffi, hb, ht⟩
            rotate_left
            · simp
            refine panSetByteHOL_congr' _ rfl (key true 3 (by omega)) ?_
            refine panSetByteHOL_congr' _ rfl (key true 2 (by omega)) ?_
            refine panSetByteHOL_congr' _ rfl (key true 1 (by omega)) ?_
            exact panSetByteHOL_congr' _ (by simp) (key true 0 (by omega)) rfl
          · have hF : state.be = false := by simpa using hB
            simp only [hF, Bool.false_eq_true, if_false]
            refine ⟨hl, hg, hs, hc, he, memRel_update_eq _ _ _ hm _ _ _ ?_, hmd, hsm, hck,
              ?_, hffi, hb, ht⟩
            rotate_left
            · simp
            refine panSetByteHOL_congr' _ rfl (key false 3 (by omega)) ?_
            refine panSetByteHOL_congr' _ rfl (key false 2 (by omega)) ?_
            refine panSetByteHOL_congr' _ rfl (key false 1 (by omega)) ?_
            exact panSetByteHOL_congr' _ (by simp) (key false 0 (by omega)) rfl
    · have hD : ¬ exact.memaddrs (panByteAlignHOL addr) := fun h => hd ((hmd _).mpr h)
      cases hex : exact.memory (panByteAlignHOL addr) with
      | word bits =>
          simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
            panSemBitVec64WordModel, panSemWordModel, RiscV.panRiscVMemoryModel,
            RiscV.aligned, panMemStore32HOL, hd, hD, hal]
  · simp [panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
      panSemBitVec64WordModel, panSemWordModel, RiscV.panRiscVMemoryModel,
      RiscV.aligned, panMemStore32HOL, hal]

/-! ## Production/exact shared-memory FFI byte-codec and result correspondence

The executed `ShMemLoad`/`ShMemStore` clauses call the shared-memory FFI through
`panShMemLoad` with the canonical RISC-V 64 target context
`riscv64PanValueFfiContext` (byte codec `riscv64GetByte`/`riscv64PutBytes`,
`panRiscVByteAlign`), while the exact evaluator calls `callFFIHOL` with the HOL
standard-library codec `panWordToBytesHOL`/`panWordOfBytesHOL` (`panGetByteHOL`,
`panSetByteHOL`) and `panByteAlignHOL`.  The lemmas below record that the two
byte representations agree under `BytesRel`, that the executed and exact
shared-memory calls agree under `FfiStateRel`, and that decoding the returned
bytes yields the same word.  They are Flapjack-specific bridge infrastructure;
no HOL declaration corresponds to a production carrier.  Everything here is
untagged. -/

/-- The production shared-memory width mapping is the exact tagged HOL port
    `nbOpHOL` (`nb_op_def`). -/
theorem panValueFfiWidth_eq_nbOpHOL : panValueFfiWidth = nbOpHOL := by
  funext size
  cases size <;> rfl

/-- The total shared-memory context exposes the production shared-memory address
    predicate as its FFI domain. -/
theorem panSemTotalShMemContext_sharedDomain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (address : RiscV.Word 64) :
    (panSemTotalShMemContext state).sharedDomain address = state.sharedMemaddrs address :=
  rfl

/-- The canonical RISC-V 64 context byte alignment is HOL `byte_align` at width
    64. -/
theorem riscv64PanValueFfiContext_byteAlign_eq_panByteAlignHOL
    (domain : RiscV.Word 64 → Bool) (address : RiscV.Word 64) :
    (riscv64PanValueFfiContext domain).byteAlign address =
      panByteAlignHOL (width := 64) address := by
  simp only [riscv64PanValueFfiContext, RiscV.panRiscVByteAlign, panByteAlignHOL,
    show (BitVec.toNat (8 : RiscV.Word 64)) = 8 by decide,
    show (64 / 8 : Nat) = 8 by decide,
    show (Nat.log2 8) = 3 by decide,
    show (2 ^ 3 : Nat) = 8 by decide,
    show (8 : Nat) = 0 ↔ False by decide, if_false]

/-- The executed RISC-V byte alignment at byte count 8 is HOL `byte_align`. -/
theorem panRiscVByteAlign_eight_eq_panByteAlignHOL (address : RiscV.Word 64) :
    RiscV.panRiscVByteAlign (8 : RiscV.Word 64) address =
      panByteAlignHOL (width := 64) address :=
  (panSemBitVec64ByteAlign_eq_panRiscV address).symm.trans
    (panSemBitVec64ByteAlign_eq_panByteAlignHOL address)

/-- A successful shared-memory `callFfi` returns bytes of the same length as the
    request bytes, because the non-identity oracle branch checks that length. -/
theorem callFfi_sharedMem_returned_length {σ : Type} (state : FfiState σ)
    (op : FfiShmemOp) (configuration bytes nextBytes : List UInt8) (nextState : FfiState σ)
    (h : callFfi state (.sharedMem op) configuration bytes = .returned nextState nextBytes) :
    nextBytes.length = bytes.length := by
  have hne : (FfiName.sharedMem op) ≠ .extCall "" := by intro hh; cases hh
  unfold callFfi at h
  rw [if_neg hne] at h
  split at h
  · rename_i ns nb hor
    by_cases hl : nb.length = bytes.length
    · rw [if_pos hl] at h
      injection h with _ hb
      rw [← hb]
      exact hl
    · rw [if_neg hl] at h
      exact absurd h (by simp)
  · rename_i outcome hor
    exact absurd h (by simp)

/-- The executed shared-memory byte extraction is the HOL byte helper at the
    production width. -/
theorem riscv64GetByte_eq_panRiscVGetByte (index : Nat) (address : RiscV.Word 64) :
    riscv64GetByte index address =
      UInt8.ofNat (RiscV.panRiscVGetByte (8 : RiscV.Word 64)
        (BitVec.ofNat 64 index) address).toNat :=
  rfl

/-- The canonical RISC-V 64 context byte encoding agrees with the exact HOL
    `word_to_bytes` codec under `BytesRel`. -/
theorem riscv64PanValueFfiContext_wordToBytes_bytesRel
    (domain : RiscV.Word 64 → Bool) (address : RiscV.Word 64) :
    BytesRel ((riscv64PanValueFfiContext domain).wordToBytes address false)
      (panWordToBytesHOL (width := 64) address false) := by
  unfold BytesRel riscv64PanValueFfiContext panWordToBytesHOL
  simp only [List.map_map]
  rw [show (64 / 8 : Nat) = 8 by decide]
  apply List.map_congr_left
  intro index hindex
  simp only [Function.comp_apply]
  have hidx : (BitVec.ofNat 64 index : RiscV.Word 64).toNat = index := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := List.mem_range.mp hindex; omega)]
  have hget : riscv64GetByte index address =
      UInt8.ofNat (RiscV.panRiscVGetByteEndian (8 : RiscV.Word 64)
        (BitVec.ofNat 64 index) address false).toNat := by
    unfold riscv64GetByte
    simp only [RiscV.panRiscVGetByteEndian, RiscV.panRiscVGetByte, RiscV.panRiscVByteIndex,
      Bool.false_eq_true, if_false, hidx]
  have hbridge := panGetByteHOL_eq_panRiscVGetByteEndian
    (BitVec.ofNat 64 index) address false
  rw [hget, hbridge]
  simp only [BitVec.toNat_ofNat, UInt8.toNat_ofNat', Nat.mod_mod,
    show (2 ^ 8 : Nat) = 256 by decide]

/-- `BytesRel` is preserved by list concatenation. -/
theorem BytesRel_append {prod₁ prod₂ : List UInt8} {hol₁ hol₂ : List (BitVec 8)}
    (h₁ : BytesRel prod₁ hol₁) (h₂ : BytesRel prod₂ hol₂) :
    BytesRel (prod₁ ++ prod₂) (hol₁ ++ hol₂) := by
  unfold BytesRel at h₁ h₂ ⊢
  rw [List.map_append, List.map_append, h₁, h₂]

/-- `BytesRel` is preserved by truncating both lists to a common prefix. -/
theorem BytesRel_take {prod : List UInt8} {hol : List (BitVec 8)}
    (h : BytesRel prod hol) (n : Nat) : BytesRel (prod.take n) (hol.take n) := by
  unfold BytesRel at h ⊢
  rw [List.map_take, List.map_take, h]

/-- Extraction-side `RiscV.panRiscVSetByte` at byte count 8 is the exact HOL
    `panSetByteHOL` little-endian write. -/
theorem panRiscVSetByte_eq_panSetByteHOL (address byte value : RiscV.Word 64) :
    RiscV.panRiscVSetByte (8 : RiscV.Word 64) address byte value =
      panSetByteHOL address byte value false := by
  simp only [RiscV.panRiscVSetByte, RiscV.panRiscVByteIndex, panSetByteHOL,
    Bool.false_eq_true, if_false]
  rw [show (BitVec.toNat (8 : RiscV.Word 64)) = 8 by decide]
  simp only [show (8 : Nat) = 0 ↔ False by decide, if_false,
    show (64 / 8 : Nat) = 8 by decide]

/-- Writing byte `k` of a word whose bytes below `k` are the value itself (no
    higher set bytes) adds `b * 256^k`, matching `panSetByteHOL` at a small
    address. -/
theorem panSetByteHOL_ofNat_lt (k : Nat) (hk8 : k < 8) (b : BitVec 8) (V : Nat)
    (hV : V < 256 ^ k) :
    panSetByteHOL (BitVec.ofNat 64 k) (BitVec.ofNat 64 b.toNat)
        (BitVec.ofNat 64 V) false =
      BitVec.ofNat 64 (V + b.toNat * 256 ^ k) := by
  have hk : k < 2 ^ 64 := by omega
  have hV64 : V < 2 ^ 64 := by
    have hle : 256 ^ k ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have h8 : 256 ^ 8 = 2 ^ 64 := by decide
    omega
  have hb64 : b.toNat < 2 ^ 64 := by have := b.isLt; omega
  have hlow : V % 256 ^ k = V := Nat.mod_eq_of_lt hV
  have hhigh : V / (256 ^ k * 256) = 0 := by
    apply Nat.div_eq_of_lt
    have hle : 256 ^ k ≤ 256 ^ k * 256 :=
      Nat.le_mul_of_pos_right (m := 256) (256 ^ k) (by decide)
    omega
  simp only [panSetByteHOL, Bool.false_eq_true, if_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hV64,
    Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt b.isLt,
    show (64 / 8 : Nat) = 8 by decide, Nat.mod_eq_of_lt hk8,
    hlow, hhigh, Nat.zero_mul, Nat.add_zero]

/-- Word-cell form of `panSetByteHOL_ofNat_lt`. -/
theorem panSetByteHOL_word_lt (k : Nat) (hk8 : k < 8) (b : BitVec 8)
    (v : RiscV.Word 64) (hv : v.toNat < 256 ^ k) :
    panSetByteHOL (BitVec.ofNat 64 k) (BitVec.ofNat 64 b.toNat) v false =
      BitVec.ofNat 64 (v.toNat + b.toNat * 256 ^ k) := by
  have hv_eq : v = BitVec.ofNat 64 v.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  conv => lhs; rw [hv_eq]
  exact panSetByteHOL_ofNat_lt k hk8 b v.toNat hv

/-- The executed `riscv64PutBytes` decoder is the little-endian byte sum used by
    the exact HOL decoder, provided the written window fits the word. -/
theorem riscv64PutBytes_eq_ofNat_leSumB (i : Nat) (bytes : List UInt8)
    (v : RiscV.Word 64) (hi : i + bytes.length ≤ 8) (hv : v.toNat < 256 ^ i) :
    riscv64PutBytes false i bytes v =
      BitVec.ofNat 64 (v.toNat + leSumB i (bytes.map byteToBits)) := by
  induction bytes generalizing i v with
  | nil =>
      simp only [riscv64PutBytes, List.map_nil, leSumB, List.zipIdx_nil,
        List.foldl_nil, Nat.add_zero]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]
  | cons b bs ih =>
      simp only [riscv64PutBytes, List.map_cons]
      rw [panRiscVSetByte_eq_panSetByteHOL]
      have hi8 : i < 8 := by simp only [List.length_cons] at hi; omega
      have hstep := panSetByteHOL_word_lt i hi8 (byteToBits b) v hv
      rw [byteToBits_toNat] at hstep
      rw [hstep]
      have hb : b.toNat < 256 := b.toNat_lt
      have hb' : b.toNat * 256 ^ i ≤ 255 * 256 ^ i :=
        Nat.mul_le_mul_right (256 ^ i) (by omega)
      have hlt : v.toNat + b.toNat * 256 ^ i < 256 ^ (i + 1) := by
        rw [Nat.pow_succ]
        calc v.toNat + b.toNat * 256 ^ i < 256 ^ i + 255 * 256 ^ i :=
              Nat.add_lt_add_of_lt_of_le hv hb'
          _ = 256 ^ i * 256 := by omega
      have hS : v.toNat + b.toNat * 256 ^ i < 2 ^ 64 := by
        have hp : 256 ^ (i + 1) ≤ 2 ^ 64 := by
          calc 256 ^ (i + 1) ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
            _ = 2 ^ 64 := by decide
        omega
      have hv' : (BitVec.ofNat 64 (v.toNat + b.toNat * 256 ^ i)).toNat < 256 ^ (i + 1) := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS]
        exact hlt
      rw [ih (i + 1) _ (by simp only [List.length_cons] at hi; omega) hv']
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS, leSumB_cons, byteToBits_toNat]
      congr 1
      omega

/-- `leSumB` depends only on the natural values of the bytes. -/
theorem leSumB_eq_of_map_toNat_eq (k : Nat) (l₂ : List (BitVec 8))
    {l₁ : List (BitVec 8)} (h : l₁.map BitVec.toNat = l₂.map BitVec.toNat) :
    leSumB k l₁ = leSumB k l₂ := by
  induction l₁ generalizing k l₂ with
  | nil => cases l₂ <;> simp_all [leSumB]
  | cons a t ih =>
      cases l₂ with
      | nil => simp at h
      | cons b u =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨ha, ht⟩ := h
          rw [leSumB_cons, leSumB_cons, ha, ih (k + 1) u ht]

/-- The executed shared-memory decoder `riscv64PutBytes` computes the same word
    as the exact HOL `word_of_bytes` decoder when the returned byte lists are
    `BytesRel`-related and the returned list fits the 64-bit word. -/
theorem riscv64PutBytes_eq_panWordOfBytesHOL (bytes : List UInt8)
    (holBytes : List (BitVec 8)) (h : BytesRel bytes holBytes)
    (hlen : bytes.length = 8) :
    riscv64PutBytes false 0 bytes 0 =
      panWordOfBytesHOL (width := 64) false 0 holBytes := by
  have hlenH' : holBytes.length = 8 := by
    have := congrArg List.length h
    simpa [BytesRel, List.length_map, hlen] using this
  have hsum : leSumB 0 (bytes.map byteToBits) = leSumB 0 holBytes := by
    apply leSumB_eq_of_map_toNat_eq 0 holBytes
    rw [List.map_map]
    have hb : (List.map (BitVec.toNat ∘ byteToBits) bytes) = bytes.map UInt8.toNat := by
      apply List.map_congr_left
      intro b _
      exact byteToBits_toNat b
    rw [hb]
    exact h.symm
  rw [riscv64PutBytes_eq_ofNat_leSumB 0 bytes 0 (by omega) (by decide)]
  have hp : panWordOfBytesHOL (width := 64) false (0 : RiscV.Word 64) holBytes
      = BitVec.ofNat 64 (leSumB 0 holBytes) := by
    have h' := panWordOfBytesHOL_eq_ofNat_le (width := 64) 0 holBytes (by rw [hlenH']; decide)
    simpa using h'
  rw [hp, show (BitVec.toNat (0 : RiscV.Word 64)) = 0 by decide, Nat.zero_add, hsum]

/-- Production/exact shared-memory FFI calls agree under `FfiStateRel` for
    `BytesRel`-related byte and configuration lists.  This covers the oracle
    returned (matching and mismatched length) and finalised branches without
    assuming any particular oracle run: the correspondence follows from the
    persistent `OracleRel` inside `FfiStateRel`. -/
theorem ffiResultRel_callFfi_sharedMem {σ : Type} (prod : FfiState σ)
    (exact : HolFfiState σ) (hffi : FfiStateRel prod exact)
    (op : FfiShmemOp) (holOp : HolShmemOp) (hop : ShmemOpRel op holOp)
    (configuration : List UInt8) (holConfiguration : List (BitVec 8))
    (bytes : List UInt8) (holBytes : List (BitVec 8))
    (hcfg : BytesRel configuration holConfiguration) (hbytes : BytesRel bytes holBytes) :
    FfiResultRel (callFfi prod (.sharedMem op) configuration bytes)
      (callFFIHOL exact (.sharedMem holOp) holConfiguration holBytes) := by
  obtain ⟨hstate, hevents, horacle⟩ := hffi
  have hne : (FfiName.sharedMem op) ≠ .extCall "" := by intro h; cases h
  have hneH : (HolFfiName.sharedMem holOp) ≠
      .extCall (Flapjack.Basis.Pure.MlString.MlString.implode []) := by intro h; cases h
  have hcorr := horacle (.sharedMem op) (.sharedMem holOp) hop prod.state
    configuration holConfiguration bytes holBytes hcfg hbytes
  have hlen_of (a : List UInt8) (b : List (BitVec 8)) (h : BytesRel a b) :
      b.length = a.length := by
    have := congrArg List.length h
    simpa [BytesRel, List.length_map] using this
  cases hprod : prod.oracle (.sharedMem op) prod.state configuration bytes with
  | final outcome =>
      have hcorr' := hcorr
      rw [hprod, ← hstate] at hcorr'
      cases hexa : exact.oracle (.sharedMem holOp) exact.ffiState
          holConfiguration holBytes with
      | final holOutcome =>
          rw [hexa] at hcorr'
          rw [callFfi_nonextCall_final prod _ hne _ _ outcome hprod,
            callFFIHOL_final exact _ _ _ holOutcome hneH hexa]
          exact ⟨hop, hcfg, hbytes, hcorr'⟩
      | ret hs hb =>
          rw [hexa] at hcorr'
          exact hcorr'.elim
  | returned nextState nextBytes =>
      have hcorr' := hcorr
      rw [hprod, ← hstate] at hcorr'
      cases hexa : exact.oracle (.sharedMem holOp) exact.ffiState
          holConfiguration holBytes with
      | final holOutcome =>
          rw [hexa] at hcorr'
          exact hcorr'.elim
      | ret hState hBytes =>
          rw [hexa] at hcorr'
          obtain ⟨hst, hbytesRel⟩ := hcorr'
          by_cases hlen : nextBytes.length = bytes.length
          · have hlenH : hBytes.length = holBytes.length := by
              rw [hlen_of nextBytes hBytes hbytesRel, hlen,
                ← hlen_of bytes holBytes hbytes]
            rw [callFfi_nonextCall_success prod _ hne _ _ nextState nextBytes hprod hlen,
              callFFIHOL_ret exact _ _ _ hState hBytes hneH hexa, if_pos hlenH]
            exact ⟨⟨hst.symm,
              ffiEventListRel_append hevents
                ⟨⟨hop, hcfg, bytesPairRel_zip hbytes hbytesRel⟩, trivial⟩,
              horacle⟩, hbytesRel⟩
          · have hlenHf : ¬ hBytes.length = holBytes.length := by
              intro hh
              apply hlen
              calc nextBytes.length = hBytes.length :=
                    (hlen_of nextBytes hBytes hbytesRel).symm
                _ = holBytes.length := hh
                _ = bytes.length := hlen_of bytes holBytes hbytes
            rw [callFfi_nonextCall_return_lengthFailure prod _ hne _ _ nextState nextBytes
                hprod hlen, callFFIHOL_ret exact _ _ _ hState hBytes hneH hexa,
              if_neg hlenHf]
            exact ⟨hop, hcfg, hbytes, Or.inl ⟨rfl, rfl⟩⟩


/-- Production/exact agreement for the executed shared-memory load body
    (`panShMemLoad` against the exact `shMemLoadHOLFiniteExact`), including the
    destination local/global write and the FFI state update.  The domain test,
    the `callFfi`/`callFFIHOL` result correspondence (via
    `ffiResultRel_callFfi_sharedMem`), the returned-byte decoding
    (`riscv64PutBytes_eq_panWordOfBytesHOL`) and the resulting
    `PanSemStateRelExec` are all established here; no oracle run is assumed. -/
theorem panShMemLoad_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (kind : VarKind) (name : MlS) (hname : NameRanged (toStringOfBytes name))
    (size : OpSize) (addr : RiscV.Word 64) :
    PanSemHOLResultOptionRel
        (panSemTotalShMemLoadResult production
          (panShMemLoad (panSemTotalShMemContext production)
            (panSemTotalShMemState production) kind (toStringOfBytes name) size addr)).1
        (@shMemLoadHOLFiniteExact 64 σ _ exact
          (fun current => Classical.propDecidable (exact.shMemaddrs current))
          kind name addr (nbOpHOL size)).1 ∧
      PanSemStateRelExec
        (panSemTotalShMemLoadResult production
          (panShMemLoad (panSemTotalShMemContext production)
            (panSemTotalShMemState production) kind (toStringOfBytes name) size addr)).2
        (@shMemLoadHOLFiniteExact 64 σ _ exact
          (fun current => Classical.propDecidable (exact.shMemaddrs current))
          kind name addr (nbOpHOL size)).2.toExact := by
  obtain ⟨hlocals, hglobals, hstructs, hcode, heshapes, hmem, hmemaddrs, hshared,
    hclock, hbe, hffiRel, hbase, htop⟩ := hrel
  have hrelRaw : PanSemStateRelExec production exact.toExact :=
    ⟨hlocals, hglobals, hstructs, hcode, heshapes, hmem, hmemaddrs, hshared,
      hclock, hbe, hffiRel, hbase, htop⟩
  have hcfgRel : BytesRel [UInt8.ofNat (panValueFfiWidth size)]
      [BitVec.ofNat 8 (nbOpHOL size)] := by
    rw [panValueFfiWidth_eq_nbOpHOL]
    simp [BytesRel, UInt8.toNat_ofNat',
      show (2 ^ 8 : Nat) = 256 by decide]
  have hbytesRel := riscv64PanValueFfiContext_wordToBytes_bytesRel
    production.sharedMemaddrs addr
  have hFFI : FfiResultRel
      (callFfi production.ffi (.sharedMem .mappedRead)
        [UInt8.ofNat (panValueFfiWidth size)]
        ((riscv64PanValueFfiContext production.sharedMemaddrs).wordToBytes addr false))
      (callFFIHOL exact.ffi (.sharedMem .mappedRead)
        [BitVec.ofNat 8 (nbOpHOL size)]
        (panWordToBytesHOL (width := 64) addr false)) :=
    ffiResultRel_callFfi_sharedMem production.ffi exact.ffi hffiRel
      .mappedRead .mappedRead (Or.inl ⟨rfl, rfl⟩) _ _ _ _ hcfgRel hbytesRel
  rw [riscv64PanValueFfiContext_wordToBytes_eq_getByte] at hFFI
  rw [panValueFfiWidth_eq_nbOpHOL] at hFFI
  simp only [panShMemLoad, panSemTotalShMemLoadResult, shMemLoadHOLFiniteExact,
    panValueFfiWidth_eq_nbOpHOL, panSemTotalShMemContext, panSemTotalShMemState,
    panSemTotalShMemStateBack, riscv64PanValueFfiContext]
  by_cases h0 : nbOpHOL size = 0
  · simp only [h0, if_true] at *
    by_cases hs : exact.shMemaddrs addr
    · have hp : production.sharedMemaddrs addr = true := (hshared addr).mpr hs
      simp only [hp, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true] at *
      cases hcall : callFfi production.ffi (.sharedMem .mappedRead) [UInt8.ofNat 0]
          (List.map (fun index => riscv64GetByte index addr) (List.range 8)) with
      | returned nextFfi bytes =>
          rw [hcall] at hFFI
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0]
              (panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi newBytes =>
              rw [hcallH] at hFFI
              obtain ⟨hffiNew, hbytesRel'⟩ := hFFI
              have hlen : bytes.length = 8 := by
                have h := callFfi_sharedMem_returned_length production.ffi .mappedRead
                  [UInt8.ofNat 0]
                  (List.map (fun index => riscv64GetByte index addr) (List.range 8))
                  bytes nextFfi hcall
                simpa using h
              have hloaded := riscv64PutBytes_eq_panWordOfBytesHOL bytes newBytes hbytesRel' hlen
              have hloaded' : riscv64PutBytes false 0 bytes (0#64) =
                  panWordOfBytesHOL false (0#64) newBytes := by
                simpa using hloaded
              constructor
              · cases kind <;> simp only [PanSemHOLResultOptionRel]
              · cases kind
                · have h1 : PanSemStateRelExec { production with ffi := nextFfi }
                      ({ exact with ffi := newFfi }).toExact := by
                    simpa using PanSemStateRelExec.setFfi hrelRaw hffiNew
                  have h2 := PanSemStateRelExec.updateLocals
                    (exact := { exact with ffi := newFfi }) h1
                    (toStringOfBytes name) hname (.word (riscv64PutBytes false 0 bytes 0))
                  rw [toExact_setKvarFfiHOLFinite]
                  simp only [toExact_setVarHOLFinite] at h2
                  simpa [hloaded, hloaded', panValueToHOL_word, ofString_toStringOfBytes,
                    setKvarHOLExact, setVarHOLExact, PanSemStateFiniteExact.toExact] using h2
                · have h1 : PanSemStateRelExec { production with ffi := nextFfi }
                      ({ exact with ffi := newFfi }).toExact := by
                    simpa using PanSemStateRelExec.setFfi hrelRaw hffiNew
                  have h2 := PanSemStateRelExec.updateGlobals
                    (exact := { exact with ffi := newFfi }) h1
                    (toStringOfBytes name) hname (.word (riscv64PutBytes false 0 bytes 0))
                  rw [toExact_setKvarFfiHOLFinite]
                  simpa [hloaded, hloaded', panValueToHOL_word, ofString_toStringOfBytes,
                    setKvarHOLExact, setGlobalHOLExact, PanSemStateFiniteExact.toExact] using h2
          | final exactEvent =>
              rw [hcallH] at hFFI
              exact False.elim hFFI
      | final event =>
          rw [hcall] at hFFI
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0]
              (panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi newBytes =>
              rw [hcallH] at hFFI
              exact False.elim hFFI
          | final exactEvent =>
              rw [hcallH] at hFFI
              constructor
              · exact hFFI
              · simp only [toExact_emptyLocalsHOLFinite]
                exact PanSemStateRelExec.emptyLocals hrelRaw

    · have hp : production.sharedMemaddrs addr = false := by
        cases hb : production.sharedMemaddrs addr with
        | false => rfl
        | true => exact absurd ((hshared addr).mp hb) hs
      simp only [hp, Bool.not_false, if_true, hs, if_false] at *
      exact ⟨trivial, hrelRaw⟩
  · simp only [if_neg h0] at *
    rw [panRiscVByteAlign_eight_eq_panByteAlignHOL] at *
    by_cases hs : exact.shMemaddrs (panByteAlignHOL addr)
    · have hp : production.sharedMemaddrs (panByteAlignHOL addr) = true :=
        (hshared (panByteAlignHOL addr)).mpr hs
      simp only [hp, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true] at *
      cases hcall : callFfi production.ffi (.sharedMem .mappedRead) [UInt8.ofNat (nbOpHOL size)]
          (List.map (fun index => riscv64GetByte index addr) (List.range 8)) with
      | returned nextFfi bytes =>
          rw [hcall] at hFFI
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 (nbOpHOL size)]
              (panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi newBytes =>
              rw [hcallH] at hFFI
              obtain ⟨hffiNew, hbytesRel'⟩ := hFFI
              have hlen : bytes.length = 8 := by
                have h := callFfi_sharedMem_returned_length production.ffi .mappedRead
                  [UInt8.ofNat (nbOpHOL size)]
                  (List.map (fun index => riscv64GetByte index addr) (List.range 8))
                  bytes nextFfi hcall
                simpa using h
              have hloaded := riscv64PutBytes_eq_panWordOfBytesHOL bytes newBytes hbytesRel' hlen
              have hloaded' : riscv64PutBytes false 0 bytes (0#64) =
                  panWordOfBytesHOL false (0#64) newBytes := by
                simpa using hloaded
              constructor
              · cases kind <;> simp only [PanSemHOLResultOptionRel]
              · cases kind
                · have h1 : PanSemStateRelExec { production with ffi := nextFfi }
                      ({ exact with ffi := newFfi }).toExact := by
                    simpa using PanSemStateRelExec.setFfi hrelRaw hffiNew
                  have h2 := PanSemStateRelExec.updateLocals
                    (exact := { exact with ffi := newFfi }) h1
                    (toStringOfBytes name) hname (.word (riscv64PutBytes false 0 bytes 0))
                  rw [toExact_setKvarFfiHOLFinite]
                  simp only [toExact_setVarHOLFinite] at h2
                  simpa [hloaded, hloaded', panValueToHOL_word, ofString_toStringOfBytes,
                    setKvarHOLExact, setVarHOLExact, PanSemStateFiniteExact.toExact] using h2
                · have h1 : PanSemStateRelExec { production with ffi := nextFfi }
                      ({ exact with ffi := newFfi }).toExact := by
                    simpa using PanSemStateRelExec.setFfi hrelRaw hffiNew
                  have h2 := PanSemStateRelExec.updateGlobals
                    (exact := { exact with ffi := newFfi }) h1
                    (toStringOfBytes name) hname (.word (riscv64PutBytes false 0 bytes 0))
                  rw [toExact_setKvarFfiHOLFinite]
                  simpa [hloaded, hloaded', panValueToHOL_word, ofString_toStringOfBytes,
                    setKvarHOLExact, setGlobalHOLExact, PanSemStateFiniteExact.toExact] using h2
          | final exactEvent =>
              rw [hcallH] at hFFI
              exact False.elim hFFI
      | final event =>
          rw [hcall] at hFFI
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 (nbOpHOL size)]
              (panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi newBytes =>
              rw [hcallH] at hFFI
              exact False.elim hFFI
          | final exactEvent =>
              rw [hcallH] at hFFI
              constructor
              · exact hFFI
              · simp only [toExact_emptyLocalsHOLFinite]
                exact PanSemStateRelExec.emptyLocals hrelRaw

    · have hp : production.sharedMemaddrs (panByteAlignHOL addr) = false := by
        cases hb : production.sharedMemaddrs (panByteAlignHOL addr) with
        | false => rfl
        | true => exact absurd ((hshared (panByteAlignHOL addr)).mp hb) hs
      simp only [hp, Bool.not_false, if_true, hs, if_false] at *
      exact ⟨trivial, hrelRaw⟩

/-- Production/exact agreement for the executed shared-memory store body
    (`panShMemStore` against the exact `shMemStoreHOLExact`), including the
    installed FFI state.  The domain test, the `callFfi`/`callFFIHOL` result
    correspondence (via `ffiResultRel_callFfi_sharedMem`) and the request-byte
    `BytesRel` correspondence (value and address words, with the word-width
    `take`) are all established here; no oracle run is assumed. -/
theorem panShMemStore_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec production exact.toExact)
    (size : OpSize) (addr bytes : RiscV.Word 64) :
    PanSemHOLResultOptionRel
        (panSemTotalShMemStoreResult production
          (panShMemStore (panSemTotalShMemContext production)
            (panSemTotalShMemState production) bytes addr size)).1
        (@shMemStoreHOLExact 64 σ _ exact.toExact
          (fun current => Classical.propDecidable (exact.shMemaddrs current))
          bytes addr (nbOpHOL size)).1 ∧
      PanSemStateRelExec
        (panSemTotalShMemStoreResult production
          (panShMemStore (panSemTotalShMemContext production)
            (panSemTotalShMemState production) bytes addr size)).2
        (@shMemStoreHOLExact 64 σ _ exact.toExact
          (fun current => Classical.propDecidable (exact.shMemaddrs current))
          bytes addr (nbOpHOL size)).2 := by
  obtain ⟨hlocals, hglobals, hstructs, hcode, heshapes, hmem, hmemaddrs, hshared,
    hclock, hbe, hffiRel, hbase, htop⟩ := hrel
  have hrelRaw : PanSemStateRelExec production exact.toExact :=
    ⟨hlocals, hglobals, hstructs, hcode, heshapes, hmem, hmemaddrs, hshared,
      hclock, hbe, hffiRel, hbase, htop⟩
  have hcfgRel0 : BytesRel [UInt8.ofNat 0] [BitVec.ofNat 8 0] := by
    simp [BytesRel, show (2 ^ 8 : Nat) = 256 by decide]
  have hcfgRelN : BytesRel [UInt8.ofNat (nbOpHOL size)] [BitVec.ofNat 8 (nbOpHOL size)] := by
    simp [BytesRel, UInt8.toNat_ofNat', show (2 ^ 8 : Nat) = 256 by decide]
  have hbytesValRel0 : BytesRel
      (List.map (fun index => riscv64GetByte index bytes) (List.range 8))
      (panWordToBytesHOL (width := 64) bytes false) := by
    simpa [riscv64PanValueFfiContext] using
      riscv64PanValueFfiContext_wordToBytes_bytesRel production.sharedMemaddrs bytes
  have hbytesAddrRel0 : BytesRel
      (List.map (fun index => riscv64GetByte index addr) (List.range 8))
      (panWordToBytesHOL (width := 64) addr false) := by
    simpa [riscv64PanValueFfiContext] using
      riscv64PanValueFfiContext_wordToBytes_bytesRel production.sharedMemaddrs addr
  simp only [panShMemStore, panSemTotalShMemStoreResult, shMemStoreHOLExact,
    panValueFfiWidth_eq_nbOpHOL, panSemTotalShMemContext, panSemTotalShMemState,
    panSemTotalShMemStateBack, riscv64PanValueFfiContext]
  by_cases h0 : nbOpHOL size = 0
  · simp only [h0, if_true] at *
    have hFFIw : FfiResultRel
        (callFfi production.ffi (.sharedMem .mappedWrite) [UInt8.ofNat 0]
          (List.map (fun index => riscv64GetByte index bytes) (List.range 8)
            ++ List.map (fun index => riscv64GetByte index addr) (List.range 8)))
        (callFFIHOL exact.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
          (panWordToBytesHOL (width := 64) bytes false
            ++ panWordToBytesHOL (width := 64) addr false)) :=
      ffiResultRel_callFfi_sharedMem production.ffi exact.ffi hffiRel
        .mappedWrite .mappedWrite (Or.inr ⟨rfl, rfl⟩) _ _ _ _
        hcfgRel0 (BytesRel_append hbytesValRel0 hbytesAddrRel0)
    by_cases hs : exact.shMemaddrs addr
    · have hp : production.sharedMemaddrs addr = true := (hshared addr).mpr hs
      simp only [hp, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true] at *
      cases hcall : callFfi production.ffi (.sharedMem .mappedWrite) [UInt8.ofNat 0]
          (List.map (fun index => riscv64GetByte index bytes) (List.range 8)
            ++ List.map (fun index => riscv64GetByte index addr) (List.range 8)) with
      | returned nextFfi _ =>
          rw [hcall] at hFFIw
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 0]
              (panWordToBytesHOL (width := 64) bytes false
                ++ panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi _ =>
              rw [hcallH] at hFFIw
              obtain ⟨hffiNew, _⟩ := hFFIw
              constructor
              · simp only [PanSemHOLResultOptionRel]
              · exact PanSemStateRelExec.setFfi (exact := exact.toExact) hrelRaw hffiNew
          | final exactEvent =>
              rw [hcallH] at hFFIw
              exact False.elim hFFIw
      | final event =>
          rw [hcall] at hFFIw
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 0]
              (panWordToBytesHOL (width := 64) bytes false
                ++ panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi _ =>
              rw [hcallH] at hFFIw
              exact False.elim hFFIw
          | final exactEvent =>
              rw [hcallH] at hFFIw
              exact ⟨hFFIw, hrelRaw⟩
    · have hp : production.sharedMemaddrs addr = false := by
        cases hb : production.sharedMemaddrs addr with
        | false => rfl
        | true => exact absurd ((hshared addr).mp hb) hs
      simp only [hp, Bool.not_false, if_true, hs, if_false] at *
      exact ⟨trivial, hrelRaw⟩
  · simp only [if_neg h0] at *
    rw [panRiscVByteAlign_eight_eq_panByteAlignHOL] at *
    have hFFIw : FfiResultRel
        (callFfi production.ffi (.sharedMem .mappedWrite) [UInt8.ofNat (nbOpHOL size)]
          (List.take (nbOpHOL size)
              (List.map (fun index => riscv64GetByte index bytes) (List.range 8))
            ++ List.map (fun index => riscv64GetByte index addr) (List.range 8)))
        (callFFIHOL exact.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 (nbOpHOL size)]
          ((panWordToBytesHOL (width := 64) bytes false).take (nbOpHOL size)
            ++ panWordToBytesHOL (width := 64) addr false)) :=
      ffiResultRel_callFfi_sharedMem production.ffi exact.ffi hffiRel
        .mappedWrite .mappedWrite (Or.inr ⟨rfl, rfl⟩) _ _ _ _
        hcfgRelN
        (BytesRel_append (BytesRel_take hbytesValRel0 (nbOpHOL size)) hbytesAddrRel0)
    by_cases hs : exact.shMemaddrs (panByteAlignHOL addr)
    · have hp : production.sharedMemaddrs (panByteAlignHOL addr) = true :=
        (hshared (panByteAlignHOL addr)).mpr hs
      simp only [hp, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true] at *
      cases hcall : callFfi production.ffi (.sharedMem .mappedWrite) [UInt8.ofNat (nbOpHOL size)]
          (List.take (nbOpHOL size)
              (List.map (fun index => riscv64GetByte index bytes) (List.range 8))
            ++ List.map (fun index => riscv64GetByte index addr) (List.range 8)) with
      | returned nextFfi _ =>
          rw [hcall] at hFFIw
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 (nbOpHOL size)]
              ((panWordToBytesHOL (width := 64) bytes false).take (nbOpHOL size)
                ++ panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi _ =>
              rw [hcallH] at hFFIw
              obtain ⟨hffiNew, _⟩ := hFFIw
              constructor
              · simp only [PanSemHOLResultOptionRel]
              · exact PanSemStateRelExec.setFfi (exact := exact.toExact) hrelRaw hffiNew
          | final exactEvent =>
              rw [hcallH] at hFFIw
              exact False.elim hFFIw
      | final event =>
          rw [hcall] at hFFIw
          cases hcallH : callFFIHOL exact.ffi (.sharedMem .mappedWrite)
              [BitVec.ofNat 8 (nbOpHOL size)]
              ((panWordToBytesHOL (width := 64) bytes false).take (nbOpHOL size)
                ++ panWordToBytesHOL (width := 64) addr false) with
          | ret newFfi _ =>
              rw [hcallH] at hFFIw
              exact False.elim hFFIw
          | final exactEvent =>
              rw [hcallH] at hFFIw
              exact ⟨hFFIw, hrelRaw⟩
    · have hp : production.sharedMemaddrs (panByteAlignHOL addr) = false := by
        cases hb : production.sharedMemaddrs (panByteAlignHOL addr) with
        | false => rfl
        | true => exact absurd ((hshared (panByteAlignHOL addr)).mp hb) hs
      simp only [hp, Bool.not_false, if_true, hs, if_false] at *
      exact ⟨trivial, hrelRaw⟩
end Flapjack
