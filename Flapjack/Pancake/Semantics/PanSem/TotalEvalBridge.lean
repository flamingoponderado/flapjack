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

/-- Explicit next use of `panSemStateRelExec_store32`: when production and exact
    expression evaluation agree on the two word operands, the actual production
    `Store32` clause agrees with the exact finite-state HOL `Store32` clause,
    including its error result and unchanged state on misalignment or an
    out-of-domain address. The expression premises are kept explicit because
    the general production/exact expression-evaluation bridge is a separate
    open prerequisite. This is Flapjack-only constructor bridge infrastructure,
    not an HOL theorem port. -/
theorem panSemTotalStore32Clause_agree {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (address source : Exp (RiscV.Word 64)) (addr value : RiscV.Word 64)
    (hprodAddr : evalPanSemStateExp production address = some (.word addr))
    (hprodValue : evalPanSemStateExp production source = some (.word value))
    (hexactAddr : @evalHOLExact 64 σ _ exact.toExact
        (fun a => Classical.propDecidable (exact.toExact.memaddrs a))
        (expToHOL address) = some (.val (.word addr)))
    (hexactValue : @evalHOLExact 64 σ _ exact.toExact
        (fun a => Classical.propDecidable (exact.toExact.memaddrs a))
        (expToHOL source) = some (.val (.word value))) :
    PanSemHOLResultOptionRel
        (panSemTotalStore32Clause production address source).1
        (evaluateHOLFiniteState exact (.store32 (expToHOL address) (expToHOL source))).1 ∧
      PanSemStateRelExec
        (panSemTotalStore32Clause production address source).2
        (evaluateHOLFiniteState exact
          (.store32 (expToHOL address) (expToHOL source))).2.toExact := by
  classical
  let productionStore := (panSemBitVec64MemoryAccess production).store32
    (panSemBitVec64MemoryAccess production).domain production.memory
    panSemBitVec64BytesInWord addr value
  let exactStore := @panMemStore32HOL 64 _ exact.toExact.memory exact.toExact.memaddrs
    (fun a => Classical.propDecidable (exact.toExact.memaddrs a)) exact.toExact.be addr
    (BitVec.ofNat 32 value.toNat)
  have hstores := panSemStateRelExec_store32 production exact.toExact hrel addr value
  have hwidth : BitVec.ofNat 32 value.toNat = BitVec.setWidth 32 value := by simp
  rw [hwidth] at hstores
  dsimp only [productionStore, exactStore] at hstores
  cases hprod : (panSemBitVec64MemoryAccess production).store32
      (panSemBitVec64MemoryAccess production).domain production.memory
      panSemBitVec64BytesInWord addr value with
  | none =>
      cases hexact : @panMemStore32HOL 64 _ exact.toExact.memory exact.toExact.memaddrs
          (fun a => Classical.propDecidable (exact.toExact.memaddrs a)) exact.toExact.be addr
          (BitVec.setWidth 32 value) with
      | none =>
          have hproduction : panSemTotalStore32Clause production address source =
              (some .error, production) := by
            simp [panSemTotalStore32Clause, panSemTotalExprStep,
              hprodAddr, hprodValue, hprod]
          have hexactRun : evaluateHOLFiniteState exact
              (.store32 (expToHOL address) (expToHOL source)) = (some .error, exact) := by
            rw [evaluateHOLFiniteState_store32]
            simp [hexactAddr, hexactValue, hexact]
          rw [hproduction, hexactRun]
          exact ⟨trivial, hrel⟩
      | some memory =>
          simp [hprod, hexact] at hstores
  | some memory =>
      cases hexact : @panMemStore32HOL 64 _ exact.toExact.memory exact.toExact.memaddrs
          (fun a => Classical.propDecidable (exact.toExact.memaddrs a)) exact.toExact.be addr
          (BitVec.setWidth 32 value) with
      | none =>
          simp [hprod, hexact] at hstores
      | some exactMemory =>
          have hproduction : panSemTotalStore32Clause production address source =
              (none, { production with memory := memory }) :=
            panSemTotalStore32Clause_ok production address source addr value memory
              hprodAddr hprodValue hprod
          have hexactRun : evaluateHOLFiniteState exact
              (.store32 (expToHOL address) (expToHOL source)) =
                (none, { exact with memory := exactMemory }) := by
            rw [evaluateHOLFiniteState_store32]
            simp [hexactAddr, hexactValue, hexact]
          have hpost : PanSemStateRelExec
              { production with memory := memory }
              { exact.toExact with memory := exactMemory } := by
            simpa [hprod, hexact] using hstores
          rw [hproduction, hexactRun]
          exact ⟨trivial, by simpa using hpost⟩

end Flapjack
