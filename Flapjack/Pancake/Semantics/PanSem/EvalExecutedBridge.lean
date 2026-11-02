module

public import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
public import Flapjack.PanSteppedSemantics

@[expose] public section

namespace Flapjack

open Flapjack.Pancake.PanLang
  (ExpByteRanged ExpHOL expToHOL expOfHOL expToHOL_expOfHOL StructContextExact
    StructContextByteRanged StructInfoByteRanged ListParamByteRanged ParamByteRanged
    structContextOfHOL structInfoOfHOL paramOfHOL)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

/-- Values decoded from HOL contain only byte-ranged names. -/
theorem panValueOfHOL_byteRanged {width : Nat} [NeZero width] (v : ValueHOL width) :
    PanValueByteRanged (panValueOfHOL v) := by
  induction v using panValueOfHOL.induct with
  | case1 w => simp [panValueOfHOL, PanValueByteRanged]
  | case2 values ih =>
      simp only [panValueOfHOL, PanValueByteRanged, List.mem_map]
      intro v hv
      obtain ⟨source, hsource, rfl⟩ := hv
      exact ih source hsource
  | case3 name fields ih =>
      simp only [panValueOfHOL, PanValueByteRanged]
      refine ⟨nameRanged_toStringOfBytes_bridge name, ?_⟩
      intro field hf
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hf
      exact ⟨nameRanged_toStringOfBytes_bridge source.1, ih source hsource⟩

/-- A HOL structure context decodes to byte-ranged production identifiers. -/
theorem panStructContextOfHOL_byteRanged (c : StructContextExact) :
    StructContextByteRanged (panStructContextOfHOL c).toHOL := by
  rw [toHOL_panStructContextOfHOL]
  intro entry hentry
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hentry
  refine ⟨nameRanged_toStringOfBytes_bridge source.1, ?_⟩
  change ListParamByteRanged (source.2.fields.map paramOfHOL)
  intro field hfield
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hfield
  exact ⟨nameRanged_toStringOfBytes_bridge original.1,
    shapeOfHOL_byteRanged_bridge original.2⟩

/-- Decode the finite HOL state to the executable state carrier, using an
    explicitly supplied executable FFI state. The finite code support and
    decidable domains come from the HOL state and its caller. -/
noncomputable def panSemExecStateOfHOL {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  let state := panSemStateOfExact exact.toExact exact.code.finiteSupport
  { locals := state.locals, globals := state.globals, structs := state.structs,
    code := state.code, exceptionShapes := state.exceptionShapes, memory := state.memory,
    memaddrs := state.memaddrs, sharedMemaddrs := state.sharedMemaddrs,
    clock := state.clock, be := state.be, ffi := ffi,
    baseAddress := state.baseAddress, topAddress := state.topAddress }

/-- The decoded state has a related executable representation when the FFI
    states are related; no additional code-support premise is needed. -/
theorem panSemExecStateOfHOL_rel {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) :
    PanSemStateRelExec (panSemExecStateOfHOL exact ffi) exact.toExact := by
  have h := panSemStateRel_ofExact exact.toExact exact.code.finiteSupport
  rcases h with ⟨hloc, hglob, hstruct, hcode, hshapes, hmem, hdom, hshared,
    hclock, hbe, _, hbase, htop⟩
  simpa [PanSemStateRelExec, panSemExecStateOfHOL, panSemStateOfExact] using
    And.intro hloc (And.intro hglob (And.intro hstruct (And.intro hcode
      (And.intro hshapes (And.intro hmem (And.intro hdom (And.intro hshared
        (And.intro hclock (And.intro hbe (And.intro hffi (And.intro hbase htop)))))))))))

/-- Decoding a HOL state establishes the runtime range invariant for its
    stored values and structure context, including at non-ranged lookup keys. -/
theorem panSemExecStateOfHOL_ranged {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) : PanSemStateRelExecRanged (panSemExecStateOfHOL exact ffi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value hvalue
    simp only [panSemExecStateOfHOL, panSemStateOfExact, Option.map_eq_some_iff] at hvalue
    obtain ⟨v, _, rfl⟩ := hvalue
    exact panValueOfHOL_byteRanged v
  · intro name value hvalue
    simp only [panSemExecStateOfHOL, panSemStateOfExact, Option.map_eq_some_iff] at hvalue
    obtain ⟨v, _, rfl⟩ := hvalue
    exact panValueOfHOL_byteRanged v
  · exact panStructContextOfHOL_byteRanged exact.structs

/-- The clocked production evaluator uses `evalPanValueExpCounted` for
    expression results. After discarding its Flapjack step count and encoding
    the value, its state-derived RV64 result agrees with HOL evaluation under
    the same representation and byte-range conditions as
    `evalPanValueExp_agree`. This does not claim that the step count is a HOL
    clock or extend the result to the optional no-access compatibility path. -/
theorem evalPanValueExpCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite (expToHOL e) := by
  simpa [evalPanValueExpCounted, Option.map_map, Function.comp_def] using
    evalPanValueExp_agree state exact hrel hranged e he

/-- An expression decoded from the HOL carrier is automatically byte-ranged;
    no separate syntax-rangedness assumption is needed at this boundary. -/
theorem evalPanValueExpCounted_agree_ofHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state) (e : ExpHOL 64) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  simpa only [expToHOL_expOfHOL] using
    evalPanValueExpCounted_agree state exact hrel hranged (expOfHOL e)
      (expOfHOL_byteRanged_bridge e)

/-- Every finite HOL state and HOL expression can be evaluated by the
    state-owned production evaluator after decoding. Finite code support and
    all expression/value/context byte-range obligations are discharged by the
    codecs; the supplied executable FFI state must still be related to HOL's. -/
theorem evalPanSemStateExp_decode_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (e : ExpHOL 64) :
    Option.map panValueToHOL (evalPanSemStateExp (panSemExecStateOfHOL exact ffi) (expOfHOL e)) =
      exact.evalHOLFinite e := by
  simpa only [expToHOL_expOfHOL] using
    evalPanSemStateExp_agree (panSemExecStateOfHOL exact ffi) exact
      (panSemExecStateOfHOL_rel exact ffi hffi) (panSemExecStateOfHOL_ranged exact ffi)
      (expOfHOL e) (expOfHOL_byteRanged_bridge e)

/-- The counted evaluator used by the clocked source runner has the same
    HOL-origin correspondence after discarding the instrumentation count. -/
theorem evalPanValueExpCounted_decode_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (e : ExpHOL 64) :
    let state := panSemExecStateOfHOL exact ffi
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  exact evalPanValueExpCounted_agree_ofHOL (panSemExecStateOfHOL exact ffi) exact
    (panSemExecStateOfHOL_rel exact ffi hffi) (panSemExecStateOfHOL_ranged exact ffi) e

/-- The same correspondence for the counted argument-list evaluator used by
    clocked calls and primitives, including list evaluation failure. -/
theorem evalPanValueExpsCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (es : List (Exp (RiscV.Word 64))) (he : ∀ e ∈ es, ExpByteRanged e) :
    Option.map (fun result => result.1.map panValueToHOL)
        (evalPanValueExpsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord es
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalListHOLFinite (es.map expToHOL) := by
  have h := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state)) exact es
    (fun e hmem => evalPanValueExp_agree state exact hrel hranged e (he e hmem))
  simpa [evalPanValueExpsCounted, evalPanValueExps, Option.map_map, Function.comp_def] using h

/-- Counted named-field evaluation also uses the state-derived memory access;
    field expressions may themselves contain loads or word operations. -/
theorem evalPanValueFieldsCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (he : ∀ p ∈ fields, ExpByteRanged p.2) :
    Option.map (fun result => result.1.map (fun p => (ofString p.1, panValueToHOL p.2)))
        (evalPanValueFieldsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord fields
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalListFieldsHOLFinite (fields.map (fun p => (ofString p.1, expToHOL p.2))) := by
  have h := evalPanValueFields_eq_evalListFieldsHOLExact_of state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state)) exact fields
    (fun p hp => evalPanValueExp_agree state exact hrel hranged p.2 (he p hp))
  simpa [evalPanValueFieldsCounted, Option.map_map, Function.comp_def] using h

end Flapjack
