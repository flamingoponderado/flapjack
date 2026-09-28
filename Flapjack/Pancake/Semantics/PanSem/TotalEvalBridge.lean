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

end Flapjack
