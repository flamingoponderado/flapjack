import Flapjack.Pancake.Semantics.PanSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.StateBridge
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

end Flapjack
