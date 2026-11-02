module

public import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
public import Flapjack.PanSteppedSemantics

@[expose] public section

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS ExpByteRanged ExpHOL expToHOL expOfHOL expToHOL_expOfHOL StructContextExact
    StructContextByteRanged StructInfoByteRanged ListParamByteRanged ParamByteRanged
    structContextOfHOL structInfoOfHOL paramOfHOL shapeToHOL_shapeOfHOL)
open Flapjack.Basis.Pure.MlString
  (ofString toStringOfBytes toStringOfBytes_ofString_of_bytes ofString_toStringOfBytes)

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

/-- Executable state decoding with an explicit code-key list. Completeness of
    that list is a proof obligation only; no choice is used to run the codec. -/
def panSemExecStateOfHOLWithKeys {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (keys : List MlS) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemStateOfExactWithKeys exact.toExact ffi keys

/-- A complete explicit key list yields a state related to the HOL state. -/
theorem panSemExecStateOfHOLWithKeys_rel {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys) :
    PanSemStateRelExec (panSemExecStateOfHOLWithKeys exact ffi keys) exact.toExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hffi, ?_, ?_⟩
  · intro name _
    cases h : exact.locals.lookup (ofString name) <;>
      simp [panSemExecStateOfHOLWithKeys, h]
  · intro name _
    cases h : exact.globals.lookup (ofString name) <;>
      simp [panSemExecStateOfHOLWithKeys, h]
  · simp [panSemExecStateOfHOLWithKeys]
  · intro name hname
    have hn : name = toStringOfBytes (ofString name) :=
      (toStringOfBytes_ofString_of_bytes name hname).symm
    simp only [panSemExecStateOfHOLWithKeys, panSemCodeLookup]
    rw [hn, ofString_toStringOfBytes]
    rw [lookupInfo_mlFunctionToInfoMap _ keys (ofString name) (fun hq =>
      hkeys (ofString name) (by intro hc; exact hq (by rw [hc]; rfl)))]
    cases h : exact.code.lookup (ofString name) <;> simp
  · intro name _
    cases h : exact.eshapes.lookup (ofString name) <;>
      simp [panSemExecStateOfHOLWithKeys, h, shapeToHOL_shapeOfHOL]
  · intro address _
    simp [panSemExecStateOfHOLWithKeys]
  · intro address; simp [panSemExecStateOfHOLWithKeys]
  · intro address; simp [panSemExecStateOfHOLWithKeys]
  · rfl
  · rfl
  · rfl
  · rfl

/-- The executable codec always yields byte-ranged values and structures. -/
theorem panSemExecStateOfHOLWithKeys_ranged {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (keys : List MlS) :
    PanSemStateRelExecRanged (panSemExecStateOfHOLWithKeys exact ffi keys) := by
  refine ⟨?_, ?_, ?_⟩
  · intro name value hvalue
    simp only [panSemExecStateOfHOLWithKeys, Option.map_eq_some_iff] at hvalue
    obtain ⟨v, _, rfl⟩ := hvalue
    exact panValueOfHOL_byteRanged v
  · intro name value hvalue
    simp only [panSemExecStateOfHOLWithKeys, Option.map_eq_some_iff] at hvalue
    obtain ⟨v, _, rfl⟩ := hvalue
    exact panValueOfHOL_byteRanged v
  · exact panStructContextOfHOL_byteRanged exact.structs

/-- Give the executable state a HOL FFI carrier without changing any source
    expression inputs. This is infrastructure for the forward state codec. -/
def panSemExecStateWithHolFfi {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ) :
    PanSemState (RiscV.Word 64) (HolFfiState σ) where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  exceptionShapes := state.exceptionShapes
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  clock := state.clock
  be := state.be
  ffi := ffi
  baseAddress := state.baseAddress
  topAddress := state.topAddress

/-- The finite HOL view of a production state. The caller supplies the actual
    finite-support property for the projected maps; no arbitrary infinite map
    is represented as a HOL finite map. -/
def panSemFiniteViewOfExec {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport) : PanSemStateFiniteExact 64 σ :=
  PanSemStateFiniteExact.ofExact
    (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem) hfinite

instance panSemFiniteViewOfExec_decidableMemaddrs {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport) :
    DecidablePred (panSemFiniteViewOfExec state ffi hmem hfinite).memaddrs :=
  fun address => inferInstanceAs (Decidable (state.memaddrs address = true))

/-- The forward finite view is related to its production state. FFI agreement,
    finite map support, and defined word memory on the domain are explicit. -/
theorem panSemFiniteViewOfExec_rel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hffi : FfiStateRel state.ffi ffi)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport) :
    PanSemStateRelExec state (panSemFiniteViewOfExec state ffi hmem hfinite).toExact := by
  have h := panSemStateRel_toExact (panSemExecStateWithHolFfi state ffi)
    (panSemMemoryExactOf state.memory) hmem
  rcases h with ⟨hloc, hglob, hstruct, hcode, hshapes, hmemory, hdom, hshared,
    hclock, hbe, _, hbase, htop⟩
  simpa [PanSemStateRelExec, panSemFiniteViewOfExec, PanSemStateFiniteExact.ofExact,
    panSemStateToExact, panSemExecStateWithHolFfi] using
    And.intro hloc (And.intro hglob (And.intro hstruct (And.intro hcode
      (And.intro hshapes (And.intro hmemory (And.intro hdom (And.intro hshared
        (And.intro hclock (And.intro hbe (And.intro hffi (And.intro hbase htop)))))))))))

/-- Code and exception shapes do not occur in expression evaluation. Clearing
    them lets the finite expression view require support only for locals and
    globals, while retaining every field actually read by the evaluator. -/
def panSemExpressionShadow {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with code := [], exceptionShapes := fun _ => none }

/-- Expression evaluation never invokes FFI, so the isolated view can use a
    fixed failing oracle without constraining the production state's oracle. -/
def panSemExpressionIsolated {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with ffi := trivialFfiState σ state.ffi.state }

def panSemExpressionHolFfi {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) : HolFfiState σ :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := state.ffi.state, ioEvents := [] }

theorem panSemExpressionIsolated_ffiRel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    FfiStateRel (panSemExpressionIsolated state).ffi (panSemExpressionHolFfi state) := by
  unfold FfiStateRel
  refine ⟨rfl, ?_, ?_⟩
  · simp [panSemExpressionIsolated, panSemExpressionHolFfi, trivialFfiState, FfiEventListRel]
  · intro name holName hname ffiState configuration holConfiguration bytes holBytes hconf hbytes
    simp [panSemExpressionIsolated, panSemExpressionHolFfi, trivialFfiState, OracleResultRel,
      OutcomeRel]

/-- Finite support of a production lookup at the byte-representable keys
    that correspond to HOL `mlstring` values. -/
def PanSemByteKeyFiniteSupport {α : Type} (lookup : String → Option α) : Prop :=
  ∃ keys : List MlS, ∀ key, lookup (toStringOfBytes key) ≠ none → key ∈ keys

/-- Local and global support suffice for the shadow's four HOL finite maps. -/
theorem panSemExpressionShadow_finite {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals) :
    (panSemStateToExact (panSemExecStateWithHolFfi (panSemExpressionShadow state) ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport := by
  obtain ⟨localKeys, hlocalKeys⟩ := hloc
  obtain ⟨globalKeys, hglobalKeys⟩ := hglob
  refine ⟨⟨localKeys, ?_⟩, ⟨globalKeys, ?_⟩, ⟨[], ?_⟩, ⟨[], ?_⟩⟩
  · intro key h
    apply hlocalKeys key
    intro hnone
    apply h
    simp [panSemStateToExact, panSemExecStateWithHolFfi, panSemExpressionShadow, hnone]
  · intro key h
    apply hglobalKeys key
    intro hnone
    apply h
    simp [panSemStateToExact, panSemExecStateWithHolFfi, panSemExpressionShadow, hnone]
  · simp [panSemStateToExact, panSemExecStateWithHolFfi, panSemExpressionShadow,
      panSemCodeLookup, lookupInfo]
  · simp [panSemStateToExact, panSemExecStateWithHolFfi, panSemExpressionShadow]

/-- Decode the finite HOL state to the executable state carrier, using an
    explicitly supplied executable FFI state. The finite code support and
    decidable domains come from the HOL state and its caller. -/
noncomputable def panSemExecStateOfHOL {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemExecStateOfHOLWithKeys exact ffi (Classical.choose exact.code.finiteSupport)

/-- The decoded state has a related executable representation when the FFI
    states are related; no additional code-support premise is needed. -/
theorem panSemExecStateOfHOL_rel {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) :
    PanSemStateRelExec (panSemExecStateOfHOL exact ffi) exact.toExact := by
  exact panSemExecStateOfHOLWithKeys_rel exact ffi hffi _
    (Classical.choose_spec exact.code.finiteSupport)

/-- Decoding a HOL state establishes the runtime range invariant for its
    stored values and structure context, including at non-ranged lookup keys. -/
theorem panSemExecStateOfHOL_ranged {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) : PanSemStateRelExecRanged (panSemExecStateOfHOL exact ffi) := by
  exact panSemExecStateOfHOLWithKeys_ranged exact ffi _

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

/-- Agreement for an existing production state and its constructed finite HOL
    view. The assumptions describe the representation boundary itself: finite
    support of the four maps, word-valued memory on the source domain, related
    FFI states, and byte-ranged names in the state and expression. -/
theorem evalPanSemStateExp_finiteView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hffi : FfiStateRel state.ffi ffi)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map panValueToHOL (evalPanSemStateExp state e) =
      (panSemFiniteViewOfExec state ffi hmem hfinite).evalHOLFinite (expToHOL e) := by
  exact evalPanSemStateExp_agree state (panSemFiniteViewOfExec state ffi hmem hfinite)
    (panSemFiniteViewOfExec_rel state ffi hffi hmem hfinite) hranged e he

/-- An existing production state's expression evaluation has a finite HOL
    view when its local and global maps have finite support. No support
    condition on code or exception shapes is needed for expressions. -/
theorem evalPanSemStateExp_expressionView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hffi : FfiStateRel state.ffi ffi)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map panValueToHOL (evalPanSemStateExp state e) =
      @PanSemStateFiniteExact.evalHOLFinite 64 σ _
        (panSemFiniteViewOfExec (panSemExpressionShadow state) ffi hmem
          (panSemExpressionShadow_finite state ffi hmem hloc hglob))
        (fun address => inferInstanceAs (Decidable (state.memaddrs address = true))) (expToHOL e) := by
  exact evalPanSemStateExp_finiteView_agree (panSemExpressionShadow state) ffi hffi hmem
    (panSemExpressionShadow_finite state ffi hmem hloc hglob) hranged e he

/-- Construct the finite expression-only view without relying on the source
    code map, exception shapes, or FFI oracle. -/
def panSemExpressionView {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals) : PanSemStateFiniteExact 64 σ :=
  panSemFiniteViewOfExec (panSemExpressionShadow (panSemExpressionIsolated state))
    (panSemExpressionHolFfi state) hmem
    (panSemExpressionShadow_finite (panSemExpressionIsolated state)
      (panSemExpressionHolFfi state) hmem hloc hglob)

/-- Executable decision procedure for the expression view's memory domain. -/
@[instance_reducible] def panSemExpressionViewMemDecider {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals) :
    DecidablePred (panSemExpressionView state hmem hloc hglob).memaddrs :=
  panSemFiniteViewOfExec_decidableMemaddrs
    (panSemExpressionShadow (panSemExpressionIsolated state)) (panSemExpressionHolFfi state) hmem
    (panSemExpressionShadow_finite (panSemExpressionIsolated state)
      (panSemExpressionHolFfi state) hmem hloc hglob)

/-- Production expression evaluation agrees with its finite HOL expression
    view without any premise on code, exception shapes, or FFI. Local/global
    support, word-valued domain memory, and byte-ranged names remain explicit. -/
theorem evalPanSemStateExp_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map panValueToHOL (evalPanSemStateExp state e) =
      @PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (expToHOL e) := by
  exact evalPanSemStateExp_expressionView_agree (panSemExpressionIsolated state)
    (panSemExpressionHolFfi state) (panSemExpressionIsolated_ffiRel state)
    hmem hloc hglob hranged e he

/-- Execute a production expression through the finite HOL evaluator and
    decode its result back to `PanValue`. The support and memory proofs are
    erased at runtime; the executable state and expression supply the data. -/
def evalPanSemStateExpViaHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  (@PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) (expToHOL e)).map
      panValueOfHOL

/-- Re-encoding the adapter's result recovers the HOL evaluator's full
    optional result, including failure, without a byte-range premise. -/
theorem evalPanSemStateExpViaHOL_toHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (e : Exp (RiscV.Word 64)) :
    Option.map panValueToHOL (evalPanSemStateExpViaHOL state hmem hloc hglob e) =
      @PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (expToHOL e) := by
  simp [evalPanSemStateExpViaHOL, Option.map_map, Function.comp_def]

/-- The HOL-backed executable adapter and the state-owned production
    evaluator return exactly the same optional production value. -/
theorem evalPanSemStateExpViaHOL_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    evalPanSemStateExpViaHOL state hmem hloc hglob e = evalPanSemStateExp state e := by
  unfold evalPanSemStateExpViaHOL
  have hagree := congrArg (Option.map panValueOfHOL)
    (evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged e he)
  cases hresult : evalPanSemStateExp state e with
  | none => simpa only [hresult, Option.map_none] using hagree.symm
  | some value =>
      have hr := evalPanSemStateExp_byteRanged state hranged e he value hresult
      simpa only [hresult, Option.map_some, panValueOfHOL_panValueToHOL value hr] using hagree.symm

/-- The clocked evaluator's counted expression result agrees with the same
    expression-only HOL view after removing the instrumentation count. -/
theorem evalPanValueExpCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (expToHOL e) := by
  simp only [evalPanValueExpCounted, Option.map_map, Function.comp_def]
  change Option.map panValueToHOL
    (evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord e
      (memoryAccess := some (panSemBitVec64MemoryAccess state))) = _
  rw [← evalPanSemStateExp_64_eq_previous]
  exact evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged e he

/-- The same constructed finite view covers the counted expression result
    consumed by the clocked production evaluator. -/
theorem evalPanValueExpCounted_finiteView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hffi : FfiStateRel state.ffi ffi)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      (panSemFiniteViewOfExec state ffi hmem hfinite).evalHOLFinite (expToHOL e) := by
  exact evalPanValueExpCounted_agree state (panSemFiniteViewOfExec state ffi hmem hfinite)
    (panSemFiniteViewOfExec_rel state ffi hffi hmem hfinite) hranged e he

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

/-- For a finite HOL state with a supplied complete code-key list, the
    executable state codec and production evaluator agree with HOL for every
    HOL expression. No classical code-support choice is used by the codec. -/
theorem evalPanSemStateExp_decodeWithKeys_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys) (e : ExpHOL 64) :
    Option.map panValueToHOL
        (evalPanSemStateExp (panSemExecStateOfHOLWithKeys exact ffi keys) (expOfHOL e)) =
      exact.evalHOLFinite e := by
  simpa only [expToHOL_expOfHOL] using
    evalPanSemStateExp_agree (panSemExecStateOfHOLWithKeys exact ffi keys) exact
      (panSemExecStateOfHOLWithKeys_rel exact ffi hffi keys hkeys)
      (panSemExecStateOfHOLWithKeys_ranged exact ffi keys)
      (expOfHOL e) (expOfHOL_byteRanged_bridge e)

/-- The executable codec also supplies the preconditions for the counted
    expression path used in the clocked evaluator. -/
theorem evalPanValueExpCounted_decodeWithKeys_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys) (e : ExpHOL 64) :
    let state := panSemExecStateOfHOLWithKeys exact ffi keys
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  exact evalPanValueExpCounted_agree_ofHOL (panSemExecStateOfHOLWithKeys exact ffi keys) exact
    (panSemExecStateOfHOLWithKeys_rel exact ffi hffi keys hkeys)
    (panSemExecStateOfHOLWithKeys_ranged exact ffi keys) e

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


/-- Restrict the function-backed source maps to the names used by one
    expression. This expression-only view is finite even if the surrounding
    executable state uses unrestricted lookup functions. -/
def panSemExpressionSlice {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with
    locals := fun name => if name ∈ expLocalVars e then state.locals name else none
    globals := fun name => if name ∈ expGlobalVars e then state.globals name else none }

theorem panSemExpressionSlice_locals_finite {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64)) :
    PanSemByteKeyFiniteSupport (panSemExpressionSlice state e).locals := by
  refine ⟨(expLocalVars e).map ofString, ?_⟩
  intro key hkey
  have hm : toStringOfBytes key ∈ expLocalVars e := by
    by_cases h : toStringOfBytes key ∈ expLocalVars e
    · exact h
    · simp [panSemExpressionSlice, h] at hkey
  exact List.mem_map.mpr ⟨toStringOfBytes key, hm, ofString_toStringOfBytes key⟩

theorem panSemExpressionSlice_globals_finite {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64)) :
    PanSemByteKeyFiniteSupport (panSemExpressionSlice state e).globals := by
  refine ⟨(expGlobalVars e).map ofString, ?_⟩
  intro key hkey
  have hm : toStringOfBytes key ∈ expGlobalVars e := by
    by_cases h : toStringOfBytes key ∈ expGlobalVars e
    · exact h
    · simp [panSemExpressionSlice, h] at hkey
  exact List.mem_map.mpr ⟨toStringOfBytes key, hm, ofString_toStringOfBytes key⟩

theorem panSemExpressionSlice_ranged {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64))
    (hranged : PanSemStateRelExecRanged state) :
    PanSemStateRelExecRanged (panSemExpressionSlice state e) := by
  refine ⟨?_, ?_, hranged.2.2⟩
  · intro name value h
    by_cases hm : name ∈ expLocalVars e
    · exact hranged.1 name value (by simpa [panSemExpressionSlice, hm] using h)
    · simp [panSemExpressionSlice, hm] at h
  · intro name value h
    by_cases hm : name ∈ expGlobalVars e
    · exact hranged.2.1 name value (by simpa [panSemExpressionSlice, hm] using h)
    · simp [panSemExpressionSlice, hm] at h

/-- HOL-backed evaluation using only the finite set of lookups referenced by
    the expression. It does not require finite support of the original maps. -/
def evalPanSemStateExpViaHOLSlice {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  evalPanSemStateExpViaHOL (panSemExpressionSlice state e) hmem
    (panSemExpressionSlice_locals_finite state e)
    (panSemExpressionSlice_globals_finite state e) e

/-- Trimming unused lookup keys does not affect source expression evaluation. -/
theorem evalPanSemStateExp_expressionSlice {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64)) :
    evalPanSemStateExp (panSemExpressionSlice state e) e = evalPanSemStateExp state e := by
  rw [evalPanSemStateExp_64_eq_previous, evalPanSemStateExp_64_eq_previous]
  apply evalPanValueExp_lookup_congr
  · intro name hm
    simp [panSemExpressionSlice, hm]
  · intro name hm
    simp [panSemExpressionSlice, hm]

/-- The finite slice adapter returns the production result under the byte-name
    and memory representation invariants, without map-support assumptions. -/
theorem evalPanSemStateExpViaHOLSlice_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    evalPanSemStateExpViaHOLSlice state hmem e = evalPanSemStateExp state e := by
  exact (evalPanSemStateExpViaHOL_eq (panSemExpressionSlice state e) hmem
    (panSemExpressionSlice_locals_finite state e)
    (panSemExpressionSlice_globals_finite state e)
    (panSemExpressionSlice_ranged state e hranged) e he).trans
      (evalPanSemStateExp_expressionSlice state e)

/-- Convert a byte-keyed lookup with finite support to the canonical HOL map.
    The support witness is erased; the executable lookup remains unchanged. -/
def panSemByteKeyMapToHOL {α : Type}
    (lookup : String → Option α) (encode : α → β)
    (finite : PanSemByteKeyFiniteSupport lookup) : HolFiniteMapExact MlS β where
  lookup key := (lookup (toStringOfBytes key)).map encode
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := finite
    refine ⟨keys, ?_⟩
    intro key hkey
    apply hkeys key
    intro hnone
    simp [hnone] at hkey

/-- Runtime expression view. Memory is totalized as for `panSemMemoryExactOf`;
    correspondence with the production evaluator requires word-valued memory
    on the domain, but no proof is required to construct or execute this view. -/
def panSemExpressionSliceRuntimeView {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : PanSemStateFiniteExact 64 σ where
  locals := panSemByteKeyMapToHOL (panSemExpressionSlice state e).locals panValueToHOL
    (panSemExpressionSlice_locals_finite state e)
  globals := panSemByteKeyMapToHOL (panSemExpressionSlice state e).globals panValueToHOL
    (panSemExpressionSlice_globals_finite state e)
  structs := panStructContextToHOL state.structs
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := panSemMemoryExactOf state.memory
  memaddrs := fun address => state.memaddrs address = true
  shMemaddrs := fun address => state.sharedMemaddrs address = true
  clock := state.clock
  be := state.be
  ffi := panSemExpressionHolFfi state
  baseAddr := state.baseAddress
  topAddr := state.topAddress

/-- The executable view is the existing finite expression view whenever the
    source memory meets the representation invariant. -/
theorem panSemExpressionSliceRuntimeView_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (e : Exp (RiscV.Word 64)) :
    panSemExpressionSliceRuntimeView state e =
      panSemExpressionView (panSemExpressionSlice state e) hmem
        (panSemExpressionSlice_locals_finite state e)
        (panSemExpressionSlice_globals_finite state e) := by
  rfl

/-- Evaluate an expression via the reviewed HOL evaluator without requiring
    runtime proof arguments or finite support of the original source maps.
    Its memory totalization matches the production evaluator on states with
    word-valued memory throughout the source domain. -/
def evalPanSemStateExpViaHOLRuntime {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  (@PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionSliceRuntimeView state e)
    (fun address => inferInstanceAs (Decidable (state.memaddrs address = true))) (expToHOL e)).map
      panValueOfHOL

/-- The proof-free runtime adapter agrees with production on the reviewed
    memory and byte-name representation boundary. -/
theorem evalPanSemStateExpViaHOLRuntime_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    evalPanSemStateExpViaHOLRuntime state e = evalPanSemStateExp state e := by
  exact evalPanSemStateExpViaHOLSlice_eq state hmem hranged e he

/-- For the production partial-memory carrier, retain only domain addresses
    containing a word. The resulting state has a total HOL word-memory view. -/
def panSemExpressionWordDomain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemState (RiscV.Word 64) (FfiState σ) :=
  { state with memaddrs := fun address => state.memaddrs address &&
      match state.memory address with
      | some (.word _) => true
      | _ => false }

theorem panSemExpressionWordDomain_memoryRel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemMemoryRel (panSemExpressionWordDomain state).memaddrs
      (panSemExpressionWordDomain state).memory (panSemMemoryExactOf state.memory) := by
  apply panSemMemoryRel_of_partial
  intro address h
  simp only [panSemExpressionWordDomain, Bool.and_eq_true] at h
  cases hv : state.memory address with
  | none => simp [hv] at h
  | some value =>
      cases value with
      | word bits => exact ⟨bits, hv⟩
      | rStruct fields => simp [hv] at h
      | nStruct name fields => simp [hv] at h

/-- Proof-free expression evaluation via HOL with a domain restricted to
    present word cells. This preserves HOL memory's total-word representation
    while retaining production failure for missing or non-word cells. -/
def evalPanSemStateExpViaHOLWordDomain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  evalPanSemStateExpViaHOLRuntime (panSemExpressionWordDomain state) e

/-- The restricted-domain HOL route agrees with the state-owned evaluator on
    that same domain, for byte-ranged names. -/
theorem evalPanSemStateExpViaHOLWordDomain_eq_restricted {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    evalPanSemStateExpViaHOLWordDomain state e =
      evalPanSemStateExp (panSemExpressionWordDomain state) e := by
  exact evalPanSemStateExpViaHOLRuntime_eq (panSemExpressionWordDomain state)
    (panSemExpressionWordDomain_memoryRel state) hranged e he

/-- Restricting the domain to present word cells does not change any source
    expression result. In particular, failed partial-memory reads remain
    failures instead of becoming reads of the totalized zero cell. -/
private theorem panSemWordDomain_readWord (s : PanSemState (RiscV.Word 64) (FfiState σ)) :
    panValueFlatReadWord s.memory panSemBitVec64BytesInWord
      (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
    panValueFlatReadWord s.memory panSemBitVec64BytesInWord
      (some (panSemWordMemoryAccess s)) := by
  funext a
  simp only [panValueFlatReadWord, panSemWordMemoryAccess, panValueMemoryAccessOfModel,
    panSemExpressionWordDomain]
  by_cases hd : s.memaddrs a = true
  · simp only [hd, Bool.true_and]
    cases hm : s.memory a with
    | none => simp
    | some v => cases v <;> simp
  · simp [hd]
private theorem panSemWordDomain_readByte (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a : RiscV.Word 64) :
    (panSemWordMemoryAccess (panSemExpressionWordDomain s)).readByte
      (panSemWordMemoryAccess (panSemExpressionWordDomain s)).domain s.memory panSemBitVec64BytesInWord a =
    (panSemWordMemoryAccess s).readByte (panSemWordMemoryAccess s).domain s.memory panSemBitVec64BytesInWord a := by
  simp only [panSemWordMemoryAccess, panValueMemoryAccessOfModel,
    panSemExpressionWordDomain, panModelReadByte]
  generalize h : (panSemWordModel (width := 64)).byteAlign panSemBitVec64BytesInWord a = aligned
  by_cases hd : s.memaddrs aligned = true
  · simp only [hd, Bool.true_and]
    cases hm : s.memory aligned with
    | none => simp [hm, panValueWordMemory]
    | some v => cases v <;> simp [hm, panValueWordMemory]
  · simp [hd]
private theorem panSemWordDomain_read32 (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a : RiscV.Word 64) :
    (panSemWordMemoryAccess (panSemExpressionWordDomain s)).read32
      (panSemWordMemoryAccess (panSemExpressionWordDomain s)).domain s.memory panSemBitVec64BytesInWord a =
    (panSemWordMemoryAccess s).read32 (panSemWordMemoryAccess s).domain s.memory panSemBitVec64BytesInWord a := by
  simp only [panSemWordMemoryAccess, panValueMemoryAccessOfModel,
    panSemExpressionWordDomain, panModelRead32]
  split
  · generalize h : (panSemWordModel (width := 64)).byteAlign panSemBitVec64BytesInWord a = aligned
    by_cases hd : s.memaddrs aligned = true
    · simp only [hd, Bool.true_and]
      cases hm : s.memory aligned with
      | none => simp [hm, panValueWordMemory]
      | some v => cases v <;> simp [hm, panValueWordMemory]
    · simp [hd]
  · rfl
theorem evalPanSemStateExp_wordDomain (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) :
    evalPanSemStateExp (panSemExpressionWordDomain s) e = evalPanSemStateExp s e := by
  rw [evalPanSemStateExp_64_eq_previous, evalPanSemStateExp_64_eq_previous]
  have hw := panSemWordDomain_readWord s
  have hb := panSemWordDomain_readByte s
  have hi := panSemWordDomain_read32 s
  have hload : ∀ shape address,
      panValueFlatLoad s.structs s.memory panSemBitVec64BytesInWord address shape
        (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
      panValueFlatLoad s.structs s.memory panSemBitVec64BytesInWord address shape
        (some (panSemWordMemoryAccess s)) := by
    intro shape address
    simp only [panValueFlatLoad, hw]
  change evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
      panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
    evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
      panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess s))
  have hmain : ∀ (e : Exp (RiscV.Word 64)) (access : Option (PanValueMemoryAccess (RiscV.Word 64))),
      evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
        panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
      evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
        panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess s)) := by
    apply evalPanValueExp.induct
      (motive1 := fun es _ =>
        evalPanValueExp.evalPanValueExps s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord es (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
        evalPanValueExp.evalPanValueExps s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord es (some (panSemWordMemoryAccess s)))
      (motive2 := fun e _ =>
        evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
        evalPanValueExp s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord e (some (panSemWordMemoryAccess s)))
      (motive3 := fun fs _ =>
        evalPanValueExp.evalPanValueFields s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord fs (some (panSemWordMemoryAccess (panSemExpressionWordDomain s))) =
        evalPanValueExp.evalPanValueFields s.structs s.locals s.globals s.memory s.baseAddress s.topAddress
          panSemBitVec64BytesInWord fs (some (panSemWordMemoryAccess s)))
    all_goals
      intros
      simp only [evalPanValueExp, evalPanValueExp.evalPanValueExps,
        evalPanValueExp.evalPanValueFields, *]
    all_goals rfl

  exact hmain e none

/-- The proof-free HOL route agrees with the state-owned evaluator for every
    memory map, assuming only the byte-name boundary. -/
theorem evalPanSemStateExpViaHOLWordDomain_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    evalPanSemStateExpViaHOLWordDomain state e = evalPanSemStateExp state e :=
  (evalPanSemStateExpViaHOLWordDomain_eq_restricted state hranged e he).trans
    (evalPanSemStateExp_wordDomain state e)

/-- Execute a list of source expressions through the same finite HOL view as
    `evalPanSemStateExpViaHOL`. This is the adapter needed for call and
    primitive arguments; failure of any expression fails the whole list. -/
def evalPanSemStateExpsViaHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (es : List (Exp (RiscV.Word 64))) : Option (List (PanValue (RiscV.Word 64))) :=
  (@PanSemStateFiniteExact.evalListHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) (es.map expToHOL)).map
      (List.map panValueOfHOL)

/-- Re-encoding the list adapter recovers the exact finite HOL result,
    including failure. -/
theorem evalPanSemStateExpsViaHOL_toHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (es : List (Exp (RiscV.Word 64))) :
    Option.map (List.map panValueToHOL) (evalPanSemStateExpsViaHOL state hmem hloc hglob es) =
      @PanSemStateFiniteExact.evalListHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (es.map expToHOL) := by
  simp [evalPanSemStateExpsViaHOL, Option.map_map, List.map_map, Function.comp_def]

/-- Counted call arguments agree with the isolated finite HOL view of the
    production state. As with the single-expression theorem, this requires no
    assumptions about the code map, exception shapes, or FFI. -/
theorem evalPanValueExpsCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (es : List (Exp (RiscV.Word 64))) (he : ∀ e ∈ es, ExpByteRanged e) :
    Option.map (fun result => result.1.map panValueToHOL)
        (evalPanValueExpsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord es
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalListHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (es.map expToHOL) := by
  have h := @evalPanValueExps_eq_evalListHOLExact_of σ state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state))
    (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) es
    (fun e h => by
      simpa [evalPanSemStateExp_64_eq_previous] using
        evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged e (he e h))
  simpa [evalPanValueExpsCounted, evalPanValueExps, Option.map_map, Function.comp_def] using h

/-- Decoding the finite HOL argument list agrees with the state-owned source
    evaluator when source names and values satisfy the byte-range boundary. -/
theorem evalPanSemStateExpsViaHOL_eq {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (es : List (Exp (RiscV.Word 64))) (he : ∀ e ∈ es, ExpByteRanged e) :
    evalPanSemStateExpsViaHOL state hmem hloc hglob es = evalPanSemStateExps state es := by
  have hagree := evalPanValueExpsCounted_isolatedView_agree state hmem hloc hglob hranged es he
  simp only [evalPanValueExpsCounted, Option.map_map, Function.comp_def] at hagree
  rw [← evalPanSemStateExps_64_eq_previous] at hagree
  unfold evalPanSemStateExpsViaHOL
  have hdecode := congrArg (Option.map (List.map panValueOfHOL)) hagree
  cases hvalues : evalPanSemStateExps state es with
  | none => simpa [hvalues] using hdecode.symm
  | some values =>
      have hstruct : evalPanSemStateExp state (.rStruct es) = some (.rStruct values) := by
        have hvals := hvalues
        rw [evalPanSemStateExps_64_eq_previous] at hvals
        unfold evalPanValueExps at hvals
        rw [evalPanSemStateExp_64_eq_previous]
        simp [evalPanValueExp, hvals]
      have hnames : Flapjack.Pancake.PanLang.ListExpByteRanged es := by
        exact (Flapjack.Pancake.PanLang.listExpByteRanged_iff_forall_mem es).2 he
      have hr := evalPanSemStateExp_byteRanged state hranged (.rStruct es) hnames _ hstruct
      have hv : ∀ value ∈ values, PanValueByteRanged value := by
        simpa [PanValueByteRanged] using hr
      have hround : (values.map panValueToHOL).map panValueOfHOL = values := by
        calc
          (values.map panValueToHOL).map panValueOfHOL = values.map id := by
            rw [List.map_map]
            apply List.map_congr_left
            intro value hvalue
            exact panValueOfHOL_panValueToHOL value (hv value hvalue)
          _ = values := List.map_id values
      simpa [hvalues, Option.map_map, Function.comp_def, hround] using hdecode.symm

/-- Counted named-field expressions agree with the isolated finite HOL view,
    including failures from a field expression. -/
theorem evalPanValueFieldsCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (he : ∀ p ∈ fields, ExpByteRanged p.2) :
    Option.map (fun result => result.1.map (fun p => (ofString p.1, panValueToHOL p.2)))
        (evalPanValueFieldsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord fields
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalListFieldsHOLFinite 64 σ _
        (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob)
        (fields.map (fun p => (ofString p.1, expToHOL p.2))) := by
  have h := @evalPanValueFields_eq_evalListFieldsHOLExact_of σ state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state))
    (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) fields
    (fun p hp => by
      simpa [evalPanSemStateExp_64_eq_previous] using
        evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged p.2 (he p hp))
  simpa [evalPanValueFieldsCounted, Option.map_map, Function.comp_def] using h

end Flapjack
