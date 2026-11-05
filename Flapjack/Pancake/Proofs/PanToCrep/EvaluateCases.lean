import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.PanSem

/-!
Constructor-case evaluator equations used by the `pc_compile_correct`
evaluation induction. These are Flapjack proof infrastructure: the HOL script
proves the cases inside `pc_compile_correct` and does not export these Lean
lemmas as standalone declarations.
-/

namespace Flapjack

/-- The state-owned source evaluator's Skip equation. This uses the actual
`PanSemState.code` boundary and the source state's derived fuel. -/
theorem panSemEvaluateCodeState_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeState context primitive handler bytesInWord state .skip
      (memoryAccess := memoryAccess) =
      some (.control (.normal state.locals state.globals state.memory state.ffi),
        state.clock) := by
  have hpositive : 0 < panSemCodeEvaluateFuel state (.skip : Prog α) := by
    unfold panSemCodeEvaluateFuel
    omega
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  cases hfuel : panSemCodeEvaluateFuel state (.skip : Prog α) with
  | zero => omega
  | succ fuel =>
      simp [evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]

/-- State-boundary Skip case for the source-run-implies-target-run direction
of HOL `pc_compile_correct`.  Both code relations use the code fields owned
by their real runtime states; the source post-state is `panSemCodeStateAfter`
and the target post-state is the result returned by the Crep evaluator.  This
is local case infrastructure and is deliberately untagged: the complete
`pc_compile_correct` induction and its other constructors remain open. The
target side chooses its own fuel existentially, rather than forcing the source
evaluation's fuel or a fixed cutoff onto the target run. -/
theorem panToCrepPcCompileCorrectSkipCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [CrepBytesInWord α] [BEq String]
    (context : PanToCrepProofContext α)
    (sourceModel : PanMemoryModel α) (sourceBytesInWord : α)
    (sourceContext : PanValueFfiContext α)
    (sourcePrimitive : PanPrimitiveHandler α)
    (sourceHandler : PanValueStatefulFfiHandler α σ)
    (targetHandler : CrepRuntimeFfiHandler α σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler α)
    (sourceState : PanSemState α (FfiState σ))
    (targetState : CrepRuntimeState α σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .skip =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetFuel targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive targetFuel targetState
        (compileCodeRelProg context .skip) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .normal ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hsource := panSemEvaluateCodeState_skip sourceContext sourcePrimitive sourceHandler
    sourceBytesInWord sourceState (some (panValueMemoryAccessOfModel sourceModel
      sourceState.memaddrs sourceState.sharedMemaddrs sourceState.be))
  refine ⟨(by simpa [panSemEvaluateCodeStateWithMemoryModel] using hsource), ?_⟩
  have hsourcePost : panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock) = sourceState := by
    cases sourceState
    rfl
  refine ⟨1, .normal, targetState, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp [compileCodeRelProg, compileProgHOL, evalCrepRuntimeResult,
      evalCrepRuntimeProg]
  · simpa [hsourcePost] using hstate
  · simpa [hsourcePost] using hcode
  · simpa [hsourcePost] using hexcp
  · simpa [hsourcePost] using hlocals

/-- Width-indexed, fuel-bounded evaluator bridge for the HOL
    `pc_compile_correct[Skip]` proof branch (`pan_to_crepProofScript.sml:493`).
    It preserves the `state_rel`, width-indexed `code_rel`, `excp_rel`, and
    `locals_rel` clauses, with `codeRelW` at both code boundaries. It derives
    successful source and target runs from the incoming relations; the target
    run uses an existential fuel. This is useful case support, but it is not
    the full HOL Skip case: HOL's `panSem$evaluate` and `crepSem$evaluate` are
    total functions returning `(result, state)`, while these Lean interfaces
    return `Option` results from fuel-indexed evaluators. In particular, the
    Lean target `.normal` result is not itself HOL's `NONE` result. A faithful
    total-evaluator interface and its result/state correspondence are still
    prerequisites for restating the full HOL boundary. Keep this untagged. -/
theorem panToCrepPcCompileCorrectSkipFuelBoundedBridgeW
    (width : Nat)
    [BEq String]
    (context : PanToCrepProofContext (BitVec width))
    (sourceModel : PanMemoryModel (BitVec width)) (sourceBytesInWord : BitVec width)
    (sourceContext : PanValueFfiContext (BitVec width))
    (sourcePrimitive : PanPrimitiveHandler (BitVec width))
    (sourceHandler : PanValueStatefulFfiHandler (BitVec width) σ)
    (targetHandler : CrepRuntimeFfiHandler (BitVec width) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (BitVec width))
    (sourceState : PanSemState (BitVec width) (FfiState σ))
    (targetState : CrepRuntimeState (BitVec width) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRelW width context
      (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateCodeStateWithMemoryModel sourceContext sourcePrimitive sourceHandler
      sourceModel sourceBytesInWord sourceState .skip =
        some (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock) ∧
    ∃ targetFuel targetResult targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive targetFuel targetState
        (compileCodeRelProg context .skip) = some (targetResult, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState
        (.control (.normal sourceState.locals sourceState.globals
          sourceState.memory sourceState.ffi), sourceState.clock)) targetPost ∧
      codeRelW width context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).exceptionShapes ∧
      targetResult = .normal ∧
      localsRel context
        (panSemCodeStateAfter sourceState
          (.control (.normal sourceState.locals sourceState.globals
            sourceState.memory sourceState.ffi), sourceState.clock)).locals
        targetPost.locals := by
  have hcodeGeneric :=
    (codeRelW_iff_codeRel width context
      (panSemCodeAsLookup sourceState.code) targetState.code).mp hcode
  rcases panToCrepPcCompileCorrectSkipCodeState context sourceModel sourceBytesInWord
      sourceContext sourcePrimitive sourceHandler targetHandler targetPrimitive
      sourceState targetState hstate hcodeGeneric hexcp hlocals with
    ⟨hsource, targetFuel, targetResult, targetPost, hrun, hstatePost,
      hcodePost, hexcpPost, hresult, hlocalsPost⟩
  refine ⟨hsource, targetFuel, targetResult, targetPost, hrun, hstatePost, ?_,
    hexcpPost, hresult, hlocalsPost⟩
  exact (codeRelW_iff_codeRel width context
    (panSemCodeAsLookup (panSemCodeStateAfter sourceState
      (.control (.normal sourceState.locals sourceState.globals
        sourceState.memory sourceState.ffi), sourceState.clock)).code)
    targetPost.code).mpr hcodePost

theorem panSemEvaluateRiscV64CodeState_callRaiseOneWordException_ofEntry
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function exception : String) (value : RiscV.Word 64)
    (hentry : panSemCodeLookup state.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : state.exceptionShapes exception = some .one)
    (hclock : state.clock ≠ 0) :
    panSemEvaluateRiscV64CodeState context primitive handler state
      (.call none function [] : Prog (RiscV.Word 64)) =
      some (.control (.raised (fun _ => none) state.globals state.memory
        state.ffi exception (.word value)), decPanClock state.clock) := by
  let program : Prog (RiscV.Word 64) := .call none function []
  have hprogramFuel : panSemProgFuel program = 1 := by
    simp [program, panSemProgFuel, panSemCallInfoFuel, panSemExpListFuel]
  have hclockLower : 2 ≤ state.clock + 1 := by omega
  have hbodyLower : 2 ≤ max (panSemProgFuel program)
      (panSemCodeBodyFuel state.code) + 1 := by omega
  have hfuelLower : 5 ≤ panSemCodeEvaluateFuel state program := by
    unfold panSemCodeEvaluateFuel
    have hmul := Nat.mul_le_mul hclockLower hbodyLower
    omega
  obtain ⟨tail, hfuelLeft⟩ := Nat.exists_eq_add_of_le hfuelLower
  have hfuel : panSemCodeEvaluateFuel state program = tail + 5 := by
    rw [hfuelLeft]
    omega
  have hargs : evalPanValueExps state.structs state.locals state.globals
      state.memory state.baseAddress state.topAddress panSemBitVec64BytesInWord
      ([] : List (Exp (RiscV.Word 64)))
      (memoryAccess := some (panValueMemoryAccessOfModel
        panSemBitVec64WordModel state.memaddrs state.sharedMemaddrs state.be)) = some [] := by
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps]
  have hcallee : lookupPanSemCodeCall state.structs state.code function [] =
      some (.raise exception (.const value), .one, fun _ => none) := by
    unfold lookupPanSemCodeCall
    rw [hentry]
    simp [panSemCodeArgumentsMatch, bindPanValueParameters]
  rw [panSemEvaluateRiscV64CodeState_eq_previous]
  unfold panSemEvaluateCodeStateWithMemoryModel
  unfold panSemEvaluateCodeState panSemEvaluateCodeStateWithFuel
  rw [show panSemCodeEvaluateFuel state program = tail + 5 from hfuel]
  simp [evalPanValueFfiClockCodeProg, evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
    evalPanValueExpWith, evalPanValueExp,
    hargs, hcallee, hexception, hclock, panValueShape, panShapeMatches,
    decPanClock]

/-! Actual-state Call exception propagation with a one-word payload. The
source code entry and compiled target entry are obtained from `code_rel`; the
target exception code comes from the context's exception map, and the payload
is observed through the HOL `globals_lookup` boundary. -/

/-! Two-word continuation of the target `exp_hdl` step. This is still
Flapjack-only induction support: the handler payload occupies consecutive
return-global cells and updates the existing slots in source order. -/
theorem crepRuntimeExpHdlTwoWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (slot0 slot1 : Nat) (value0 value1 : RiscV.Word 64)
    (hvariable : FLOOKUP variables name =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslotsNe : slot0 ≠ slot1)
    (hslot0 : ∃ old, state.locals slot0 = some old)
    (hslot1 : ∃ old, state.locals slot1 = some old)
    (hglobal0 : state.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : state.globals (1 : BitVec 5) = some (.word value1)) :
    evalCrepRuntimeProg handler primitive 4 state
      (expHdlFiniteMap variables name) =
        some (.normal,
          { state with locals :=
            (updateCrepRuntimeLocal
              (updateCrepRuntimeLocal state.locals slot0 (.word value0))
              slot1 (.word value1)) }) := by
  obtain ⟨old0, hslot0⟩ := hslot0
  obtain ⟨old1, hslot1⟩ := hslot1
  have hsetup : expHdlFiniteMap (α := RiscV.Word 64) variables name =
      (.seq (.assign slot0 (.loadGlob (0 : BitVec 5)))
        (.seq (.assign slot1 (.loadGlob (1 : BitVec 5))) .skip) :
          CrepProg (RiscV.Word 64)) := by
    simp [expHdlFiniteMap, hvariable, loadGlobals, panMap2, crepNestedSeq]
  rw [hsetup]
  have hload0 : evalCrepRuntimeExp state (.loadGlob (0 : BitVec 5)) =
      some value0 := by
    simp only [evalCrepRuntimeExp]
    rw [hglobal0]
    rfl
  let stateAfterFirst :=
    { state with locals := updateCrepRuntimeLocal state.locals slot0 (.word value0) }
  let stateAfterBoth :=
    { stateAfterFirst with
      locals := updateCrepRuntimeLocal stateAfterFirst.locals slot1 (.word value1) }
  have hfirst :
      evalCrepRuntimeProg handler primitive 3 state
        (.assign slot0 (.loadGlob (0 : BitVec 5))) =
      some (.normal, stateAfterFirst) := by
    rw [evalCrepRuntimeProg, evalCrepRuntimeExpWordLab_panTheWord]
    rw [hload0]
    rw [hslot0]
    simp only [setCrepRuntimeLocal_eq_update]
    rfl
  have hslot1Value : stateAfterFirst.locals slot1 = some old1 := by
    simp [stateAfterFirst, updateCrepRuntimeLocal, hslotsNe, hslot1]
  have hload1 :
      evalCrepRuntimeExp stateAfterFirst (.loadGlob (1 : BitVec 5)) = some value1 := by
    simp only [evalCrepRuntimeExp, stateAfterFirst]
    rw [hglobal1]
    rfl
  have hassign1 :
      evalCrepRuntimeProg handler primitive 2 stateAfterFirst
        (.assign slot1 (.loadGlob (1 : BitVec 5))) =
      some (.normal, stateAfterBoth) := by
    rw [evalCrepRuntimeProg, evalCrepRuntimeExpWordLab_panTheWord]
    rw [hload1]
    rw [hslot1Value]
    simp only [setCrepRuntimeLocal_eq_update]
    rfl
  have hsecond :
      evalCrepRuntimeProg handler primitive 3 stateAfterFirst
        (.seq (.assign slot1 (.loadGlob (1 : BitVec 5))) .skip) =
      some (.normal, stateAfterBoth) := by
    rw [evalCrepRuntimeProg]
    rw [hassign1]
    simp [evalCrepRuntimeProg, fixCrepRuntimeClock, stateAfterBoth]
  rw [evalCrepRuntimeProg]
  rw [hfirst]
  simp only [fixCrepRuntimeClock]
  have hclockFirst : { stateAfterFirst with
      clock := min state.clock stateAfterFirst.clock } = stateAfterFirst := by
    simp [stateAfterFirst]
  rw [hclockFirst]
  rw [hsecond]

/-! Recursive target-runtime support for `exp_hdl` with an arbitrary list of
global-loaded words. This is Flapjack-only proof infrastructure; the finite-map
wrapper and arbitrary-arity handler-state relation still need to be composed
with the HOL `Call_Ret_Exception` induction hypotheses. -/
def crepRuntimeGlobalWordsRel
    (state : CrepRuntimeState (RiscV.Word 64) σ) :
    BitVec 5 → List Nat → List (RiscV.Word 64) → Prop
  | _, [], [] => True
  | address, _ :: slots, value :: values =>
      evalCrepRuntimeExp state (.loadGlob address) = some value ∧
        crepRuntimeGlobalWordsRel state (address + 1) slots values
  | _, _, _ => False

private theorem crepRuntimeGlobalWordsRel_length
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (hrel : crepRuntimeGlobalWordsRel state address slots values) :
    slots.length = values.length := by
  induction slots generalizing values address with
  | nil => cases values <;> simp [crepRuntimeGlobalWordsRel] at hrel ⊢
  | cons slot slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hrel
      | cons value values =>
          apply congrArg Nat.succ
          exact ih (address + 1) values (by
            simpa [crepRuntimeGlobalWordsRel] using hrel.2)

private theorem crepRuntimeGlobalWordsRel_updateLocal
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (slot : Nat) (value : RiscV.Word 64)
    (hglobals : crepRuntimeGlobalWordsRel state address slots values) :
    crepRuntimeGlobalWordsRel
      { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }
      address slots values := by
  induction slots generalizing values address with
  | nil => cases values <;> simp [crepRuntimeGlobalWordsRel] at hglobals ⊢
  | cons first slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hglobals
      | cons firstValue values =>
          rcases hglobals with ⟨hhead, htail⟩
          constructor
          · simpa [evalCrepRuntimeExp] using hhead
          · exact ih (address + 1) values htail

private theorem crepRuntimeExpHdlNestedWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (address : BitVec 5) (slots : List Nat) (values : List (RiscV.Word 64))
    (hslots : ∀ slot, slot ∈ slots → ∃ old, state.locals slot = some old)
    (hglobals : crepRuntimeGlobalWordsRel state address slots values) :
    evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (crepNestedSeq (panMap2 (fun destination source =>
        .assign destination source) slots
        (loadGlobals address slots.length))) =
      some (.normal,
        { state with locals := ((slots.zip values).foldl
          (fun locals (slot, value) =>
            updateCrepRuntimeLocal locals slot (.word value)) state.locals) }) := by
  induction slots generalizing state values address with
  | nil =>
      cases values with
      | nil =>
          simp [panMap2, crepNestedSeq, evalCrepRuntimeProg]
      | cons value values => simp [crepRuntimeGlobalWordsRel] at hglobals
  | cons slot slots ih =>
      cases values with
      | nil => simp [crepRuntimeGlobalWordsRel] at hglobals
      | cons value values =>
          rcases hglobals with ⟨hhead, htail⟩
          obtain ⟨old, hslot⟩ := hslots slot (by simp)
          let stateAfterFirst :=
            { state with locals := updateCrepRuntimeLocal state.locals slot (.word value) }
          have hfirst :
              evalCrepRuntimeProg handler primitive (slots.length + 2) state
                (.assign slot (.loadGlob address)) =
              some (.normal, stateAfterFirst) := by
            rw [evalCrepRuntimeProg, evalCrepRuntimeExpWordLab_panTheWord, hhead, hslot]
            simp [stateAfterFirst, setCrepRuntimeLocal_eq_update]
          have htailAfterFirst :
              crepRuntimeGlobalWordsRel stateAfterFirst (address + 1) slots values := by
            exact crepRuntimeGlobalWordsRel_updateLocal state (address + 1) slots values
              slot value htail
          have hslotsAfterFirst : ∀ tailSlot, tailSlot ∈ slots →
              ∃ current, stateAfterFirst.locals tailSlot = some current := by
            intro tailSlot htailSlot
            obtain ⟨current, hcurrent⟩ := hslots tailSlot (by simp [htailSlot])
            by_cases heq : tailSlot = slot
            · subst tailSlot
              exact ⟨.word value, by simp [stateAfterFirst, updateCrepRuntimeLocal]⟩
            · exact ⟨current, by
                simp [stateAfterFirst, updateCrepRuntimeLocal, beq_iff_eq,
                  Ne.symm heq, hcurrent]⟩
          have htailRun := ih stateAfterFirst (address + 1) values hslotsAfterFirst
            htailAfterFirst
          have hprogram :
              crepNestedSeq (panMap2 (fun destination
                  (source : CrepExp (RiscV.Word 64)) =>
                (.assign destination source : CrepProg (RiscV.Word 64))) (slot :: slots)
                (loadGlobals address (slot :: slots).length)) =
              .seq (.assign slot (.loadGlob address))
                (crepNestedSeq (panMap2 (fun destination
                    (source : CrepExp (RiscV.Word 64)) =>
                  (.assign destination source : CrepProg (RiscV.Word 64))) slots
                  (loadGlobals (address + 1) slots.length))) := by
            simp [loadGlobals, panMap2, crepNestedSeq]
          rw [hprogram, evalCrepRuntimeProg]
          have hfuel : (slot :: slots).length + 1 = slots.length + 2 := by simp
          rw [hfuel, hfirst]
          have hclock :
              fixCrepRuntimeClock (ε := FfiFinalEvent) state
                (.normal, stateAfterFirst) =
                (.normal, stateAfterFirst) := by
            simp [fixCrepRuntimeClock, stateAfterFirst]
          simp only [hclock, htailRun]
          simp [stateAfterFirst, List.zip_cons_cons, List.foldl_cons]

/-! Arbitrary-list finite-map wrapper for the target `exp_hdl` execution
above. It follows the exact flattened slot list from `FLOOKUP`; its recursive
global-word relation supplies the state-owned values read at each corresponding
return-global address. This is Flapjack-only Call induction support. -/
theorem crepRuntimeExpHdlFiniteMapWords
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (variables : FiniteMap String (Shape × List Nat))
    (name : String) (shape : Shape) (slots : List Nat)
    (values : List (RiscV.Word 64))
    (hvariable : FLOOKUP variables name = some (shape, slots))
    (hslots : ∀ slot, slot ∈ slots → ∃ old, state.locals slot = some old)
    (hglobals : crepRuntimeGlobalWordsRel state 0 slots values) :
    evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (expHdlFiniteMap variables name) =
      some (.normal,
        { state with locals := ((slots.zip values).foldl
          (fun locals (slot, value) =>
            updateCrepRuntimeLocal locals slot (.word value)) state.locals) }) := by
  simpa [expHdlFiniteMap, hvariable] using
    crepRuntimeExpHdlNestedWords handler primitive state 0 slots values
      hslots hglobals

private theorem evalCrepRuntimeExps_vars_eq
    (state : CrepRuntimeState (RiscV.Word 64) σ) (slots : List Nat) :
    evalCrepRuntimeExps state (slots.map CrepExp.var) =
      slots.mapM (fun slot => (state.locals slot).map panTheWord) := by
  induction slots with
  | nil => simp [evalCrepRuntimeExps]
  | cons slot slots ih =>
      simp [evalCrepRuntimeExps, evalCrepRuntimeExp, ih]

private theorem evalCrepRuntimeExps_eq_mapM
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (CrepExp (RiscV.Word 64))) :
    evalCrepRuntimeExps state expressions =
      expressions.mapM (evalCrepRuntimeExp state) := by
  induction expressions with
  | nil => simp [evalCrepRuntimeExps]
  | cons expression expressions ih =>
      simp [evalCrepRuntimeExps, List.mapM_cons, ih]

private theorem evalCrepRuntimeExps_append
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (left right : List (CrepExp (RiscV.Word 64)))
    (leftValues rightValues : List (RiscV.Word 64))
    (hleft : evalCrepRuntimeExps state left = some leftValues)
    (hright : evalCrepRuntimeExps state right = some rightValues) :
    evalCrepRuntimeExps state (left ++ right) = some (leftValues ++ rightValues) := by
  induction left generalizing leftValues with
  | nil =>
      simp [evalCrepRuntimeExps] at hleft
      subst leftValues
      simpa [evalCrepRuntimeExps] using hright
  | cons expression expressions ih =>
      cases heval : evalCrepRuntimeExp state expression with
      | none => simp [evalCrepRuntimeExps, heval] at hleft
      | some value =>
          cases htail : evalCrepRuntimeExps state expressions with
          | none => simp [evalCrepRuntimeExps, heval, htail] at hleft
          | some values =>
              simp [evalCrepRuntimeExps, heval, htail] at hleft
              subst leftValues
              simp only [List.cons_append, evalCrepRuntimeExps, heval]
              rw [ih values htail]
              simp

private theorem evalPanSemStateExps_cons
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (expression : Exp (RiscV.Word 64)) (expressions : List (Exp (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64)) (values : List (PanValue (RiscV.Word 64))) :
    evalPanSemStateExps source (expression :: expressions) = some (value :: values) ↔
      evalPanSemStateExp source expression = some value ∧
      evalPanSemStateExps source expressions = some values := by
  unfold evalPanSemStateExps evalPanSemStateExp evalPanValueExps
  cases hhead : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
    cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
      source.globals source.memory source.baseAddress source.topAddress
      panSemBitVec64BytesInWord expressions
      (some (panSemBitVec64MemoryAccess source)) <;>
    simp [evalPanValueExp.evalPanValueExps, hhead, htail]

private theorem evalPanSemStateExps_member_word
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (expressions : List (Exp (RiscV.Word 64)))
    (words : List (RiscV.Word 64))
    (hsource : evalPanSemStateExps source expressions =
      some (words.map PanValue.word))
    {expression : Exp (RiscV.Word 64)}
    (hmem : expression ∈ expressions) :
    ∃ word, evalPanSemStateExp source expression = some (.word word) := by
  induction expressions generalizing words with
  | nil => simp at hmem
  | cons head tail ih =>
      cases words with
      | nil =>
          have hsourceImpossible :
              evalPanSemStateExps source (head :: tail) ≠ some [] := by
            intro h
            cases hhead : evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
                head (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
              cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
                source.globals source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord tail
                (some (panSemBitVec64MemoryAccess source)) <;>
              simp [evalPanSemStateExps, evalPanValueExps,
                evalPanValueExp.evalPanValueExps, hhead, htail] at h
          exact False.elim (hsourceImpossible (by simpa using hsource))
      | cons word words =>
          have hsource' : evalPanSemStateExps source (head :: tail) =
              some (.word word :: (words.map PanValue.word)) := by
            simpa using hsource
          obtain ⟨hhead, htail⟩ :=
            (evalPanSemStateExps_cons source head tail (.word word)
              (words.map PanValue.word)).mp hsource'
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst expression
            exact ⟨word, hhead⟩
          · exact ih words htail hmem

private theorem panValueFlatten_wordList (words : List (RiscV.Word 64)) :
    (words.map PanValue.word).flatMap panValueFlatten = words := by
  induction words with
  | nil => rfl
  | cons word words ih => simp [panValueFlatten, ih]

/-! Generic list induction for HOL `eval_map_comp_exp_flat_eq`: if every
argument satisfies the per-expression compiled-evaluation relation, successful
state-owned PanSem list evaluation lifts to production Crep evaluation of
`compileArgsHOL` and the flattened source results. The per-expression relation
is an explicit premise; this theorem does not claim its `compile_exp_val_rel`
proof for unsupported constructors or the enclosing Call theorem. -/
theorem compileArgsHOL_eval_flatten_of_each
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hsource : evalPanSemStateExps source expressions = some values)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value)) :
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
      some (values.flatMap panValueFlatten) := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => simp [compileArgsHOL, evalCrepRuntimeExps]
      | cons value values =>
          simp [evalPanSemStateExps, evalPanValueExps,
            evalPanValueExp.evalPanValueExps] at hsource
  | cons expression expressions ih =>
      cases values with
      | nil =>
          have hsourceImpossible :
              evalPanSemStateExps source (expression :: expressions) ≠ some [] := by
            intro h
            cases hhead : evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
                expression (memoryAccess := some (panSemBitVec64MemoryAccess source)) <;>
              cases htail : evalPanValueExp.evalPanValueExps source.structs source.locals
                source.globals source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord expressions
                (some (panSemBitVec64MemoryAccess source)) <;>
              simp [evalPanSemStateExps, evalPanValueExps,
                evalPanValueExp.evalPanValueExps, hhead, htail] at h
          exact False.elim (hsourceImpossible hsource)
      | cons value values =>
          obtain ⟨hhead, htail⟩ :=
            (evalPanSemStateExps_cons source expression expressions value values).mp hsource
          have hcompiledHead := heach expression (by simp) value hhead
          have heachTail : ∀ head, head ∈ expressions → ∀ item,
              evalPanSemStateExp source head = some item →
              evalCrepRuntimeExps target (compileExpHOL compilerContext head).1 =
                some (panValueFlatten item) := by
            intro head hmem item heval
            exact heach head (by simp [hmem]) item heval
          have hcompiledTail := ih values htail heachTail
          have happend := evalCrepRuntimeExps_append target
            (compileExpHOL compilerContext expression).1
            (compileArgsHOL compilerContext expressions)
            (panValueFlatten value) (values.flatMap panValueFlatten)
            hcompiledHead hcompiledTail
          simpa [compileArgsHOL, List.flatMap_cons] using happend

/-! When every operand compiles to one word expression, HOL's `cexp_heads`
projection of `compile_exp_list` is exactly the production `compile_args`
list. This bridges the representation used by the Op constructor to the
generic list-evaluation theorem above. -/
private theorem compileExpListHOL_heads_eq_compileArgs_of_singleton
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64)))
    (hshape : ∀ expression, expression ∈ expressions →
      (compileExpHOL compilerContext expression).2 = .one)
    (hlen : ∀ expression, expression ∈ expressions →
      (compileExpHOL compilerContext expression).1.length = 1) :
    cexpHeads (expressions.map (compileExpHOL compilerContext) |>.map Prod.fst) =
      some (compileArgsHOL compilerContext expressions) := by
  induction expressions with
  | nil => simp [compileArgsHOL, cexpHeads]
  | cons expression expressions ih =>
      have hheadShape := hshape expression (by simp)
      have hheadLength := hlen expression (by simp)
      have htailShape : ∀ item, item ∈ expressions →
          (compileExpHOL compilerContext item).2 = .one := by
        intro item hmem
        exact hshape item (by simp [hmem])
      have htailLength : ∀ item, item ∈ expressions →
          (compileExpHOL compilerContext item).1.length = 1 := by
        intro item hmem
        exact hlen item (by simp [hmem])
      have htail := ih htailShape htailLength
      cases hcompiled : (compileExpHOL compilerContext expression).1 with
      | nil => simp [hcompiled] at hheadLength
      | cons head tail =>
          cases tail with
          | nil =>
              have hcompiledPair : compileExpHOL compilerContext expression =
                  ([head], .one) := by
                apply Prod.ext
                · simp [hcompiled]
                · exact hheadShape
              change cexpHeads
                ((compileExpHOL compilerContext expression).1 ::
                  (expressions.map (compileExpHOL compilerContext)).map Prod.fst) =
                some (compileArgsHOL compilerContext (expression :: expressions))
              rw [hcompiledPair]
              simp only [cexpHeads]
              rw [htail]
              simp [compileArgsHOL, hcompiledPair]
          | cons _ _ => simp [hcompiled] at hheadLength

/-! Source review of HOL `eval_map_comp_exp_flat_eq`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1055`). Its statement
    takes `MAP (eval s) expressions = MAP SOME values`, HOL `state_rel`,
    `code_rel`, `locals_rel`, and `EVERY localised_exp expressions`, then proves
    target evaluation of all flattened `compile_exp` outputs. The theorem below
    is not that port: it quantifies production `PanSemState` and
    `CrepRuntimeState`, uses Flapjack's `stateRel`/`codeRel`/`localsRel`, and
    additionally assumes a per-expression `heach` relation containing target
    evaluation plus shape/length/well-formedness facts. Those stronger premises
    and different state/evaluator carriers change the theorem statement; the
    helper must not receive the HOL tag.

    `compileArgsHOL` is a useful flattening adapter, but it does not close this
    gap. The finite-support PanSem evaluator is now tagged; a faithful port
    still needs exact Pan-to-Crep state/context/local relations, tracked by
    `flapjack-pxn.18.3.5.8.8`. Keep bead `flapjack-4ac.5.22` open until the
    exact HOL premises and conclusion are stated and proved. -/

/-! Source-reviewed disposition for HOL `compile_exp_val_rel`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:130`). HOL quantifies over
the width-polymorphic `panSem$state`, expression `e`, source value `v`,
`crepSem$state`, compiler context and compiled pair. It assumes successful
source evaluation, `state_rel`, `code_rel`, `locals_rel`, `localised_exp`, and
the exact `compile_exp` result; it concludes target evaluation of the compiled
expressions equals `MAP SOME (flatten v)`, plus the output length, shape, and
well-formedness facts.

There is no exact Lean counterpart yet. The nearby compiler-support theorems
use the fixed `RiscV.Word 64` production `Exp`, `PanValue`, `Shape`,
`PanSemState`, `CrepRuntimeState`, and `CrepExp` carriers. HOL instead uses
`ExpHOL width`, `ValueHOL width` (with `word_lab` values), `ShapeHOL`, and
width-polymorphic HOL source/target states; the context and `code_rel`/
`locals_rel` keys are `mlstring` and HOL finite maps. In particular, current
`stateRel` relates optional PanValue memory to total target word memory. The
per-expression helper below also assumes a stronger four-part `heach` fact and
proves only the list-evaluation result, while case lemmas elsewhere cover only
selected constructors (some with an RV64 target invariant). These declarations
must not carry the HOL tag. The faithful theorem replacement is tracked by
`flapjack-4ac.5.81`, blocked on exact compiler/context carriers
(`flapjack-pxn.18.3.5.8.8`, `.8.13`) and exact state relations
(`flapjack-pxn.18.3.7.1.3.1`). The existing compile-expression probe covers
`compile_exp` outputs; it does not establish this evaluation theorem. -/
/-! Adapter from the complete per-expression compiled-evaluation relation to
the `compile_args` evaluator boundary. The target evaluation premise consumed
by the list induction is projected from the relation itself; callers do not
assume target evaluation separately. This list adapter does not prove
`compile_exp_val_rel`. -/
theorem compileArgsHOL_eval_flatten_of_compileExpRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExps source expressions = some values)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heachEval : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    exact (heach expression hmem value heval hstate hcode hlocals
      (hlocalized expression hmem)).1
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions
      values hsource heachEval

private theorem mapM_panTheWord_of_wordLab
    (locals : Nat → Option (PanWordLab (RiscV.Word 64)))
    (slots : List Nat) (words : List (RiscV.Word 64))
    (hslots : slots.mapM (FLOOKUP locals) =
      some (words.map PanWordLab.word)) :
    slots.mapM (fun slot => (FLOOKUP locals slot).map panTheWord) = some words := by
  induction slots generalizing words with
  | nil =>
      cases words with
      | nil => simp
      | cons word words => simp at hslots
  | cons slot slots ih =>
      cases words with
      | nil =>
          simp only [List.mapM_cons] at hslots
          cases hlookup : FLOOKUP locals slot with
          | none => simp [hlookup] at hslots
          | some cell =>
              cases htail : slots.mapM (FLOOKUP locals) <;>
                simp [hlookup, htail] at hslots
      | cons word words =>
          simp only [List.mapM_cons] at hslots
          cases hlookup : FLOOKUP locals slot with
          | none => simp [hlookup] at hslots
          | some cell =>
              cases cell with
                | word cellWord =>
                  cases htail : slots.mapM (FLOOKUP locals) with
                  | none => simp [hlookup, htail] at hslots
                  | some cells =>
                      simp [hlookup, htail] at hslots
                      rcases hslots with ⟨hword, htailWords⟩
                      subst word
                      have htailLookup : slots.mapM (FLOOKUP locals) =
                          some (words.map PanWordLab.word) := by
                        rw [htail, htailWords]
                      have htailEval := ih words htailLookup
                      simp [List.mapM_cons, hlookup, panTheWord, htailEval]

/-! Flapjack-specific local-variable support toward HOL `compile_exp_val_rel`. `locals_rel`
provides the flattened target words for the source value, and target `.var`
evaluation reads those same slots through the production Crep locals map.
This handles one RV64 constructor, but does not state HOL's full case or
claim the general expression theorem `eval_map_comp_exp_flat_eq`. -/
theorem compileExpHOL_local_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (hlocals : localsRel context source.locals target.locals)
    (hsourceEval : evalPanSemStateExp source (.var .local name) = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.var .local name)).1 = some (panValueFlatten value) := by
  have hsource : FLOOKUP source.locals name = some value := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceEval
  obtain ⟨slots, hcontext, _, htargetWords, _⟩ :=
    localsRelLookupCtxt context source.locals target.locals name value hlocals hsource
  have htargetValues : slots.mapM
      (fun slot => (FLOOKUP target.locals slot).map panTheWord) =
      some (panValueFlatten value) := by
    exact mapM_panTheWord_of_wordLab target.locals slots (panValueFlatten value)
      htargetWords
  simp only [compileExpHOL, hcontext]
  rw [evalCrepRuntimeExps_vars_eq]
  exact htargetValues

/-! `mapM` success is preserved by truncating both its input and output at the
same position. This supports `comp_field` projections of flattened locals. -/
private theorem mapM_take_of_success {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) (count : Nat)
    (hmap : inputs.mapM f = some outputs) :
    (inputs.take count).mapM f = some (outputs.take count) := by
  induction inputs generalizing outputs count with
  | nil =>
      simp only [List.mapM_nil] at hmap
      cases hmap
      simp only [List.take_nil, List.mapM_nil]
      rfl
  | cons input inputs ih =>
      cases hhead : f input with
      | none => simp [List.mapM_cons, hhead] at hmap
      | some output =>
          cases htail : inputs.mapM f with
          | none => simp [List.mapM_cons, hhead, htail] at hmap
          | some outputsTail =>
              simp [List.mapM_cons, hhead, htail] at hmap
              cases hmap
              cases count with
              | zero => simp only [List.take_zero, List.mapM_nil]; rfl
              | succ count =>
                  simp only [List.take_succ_cons]
                  simp [List.mapM_cons, hhead, ih outputsTail count htail]

private theorem mapM_drop_of_success {α β : Type} (f : α → Option β)
    (inputs : List α) (outputs : List β) (count : Nat)
    (hmap : inputs.mapM f = some outputs) :
    (inputs.drop count).mapM f = some (outputs.drop count) := by
  induction inputs generalizing outputs count with
  | nil =>
      simp only [List.mapM_nil] at hmap
      cases hmap
      simp
  | cons input inputs ih =>
      cases hhead : f input with
      | none => simp [List.mapM_cons, hhead] at hmap
      | some output =>
          cases htail : inputs.mapM f with
          | none => simp [List.mapM_cons, hhead, htail] at hmap
          | some outputsTail =>
              simp [List.mapM_cons, hhead, htail] at hmap
              cases hmap
              cases count with
              | zero => simp [List.mapM_cons, hhead, htail]
              | succ count =>
                  simpa [List.drop_succ_cons] using ih outputsTail count htail

/-! `compile_exp_val_rel`'s RField case selects the source field's flattened
slice from the compiled inner record. This helper is the list-level bridge for
arbitrary field shapes and indices: successful target evaluation of the whole
record is projected through the same shape-sized drop/take used by
`compileField`. -/
private theorem evalCrepCompileField_panValueField
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (values : List (PanValue (RiscV.Word 64)))
    (shapes : List Shape) (expressions : List (CrepExp (RiscV.Word 64)))
    (index : Nat)
    (hshapes : shapes = values.map (panValueShape []))
    (hfieldsWf : ∀ value, value ∈ values →
      isWfShape [] (panValueShape [] value) = true)
    (hindex : index < values.length)
    (heval : evalCrepRuntimeExps target expressions =
      some (values.flatMap panValueFlatten)) :
    evalCrepRuntimeExps target (compileField index shapes expressions).1 =
      some (panValueFlatten values[index]) := by
  induction values generalizing shapes expressions index with
  | nil => simp at hindex
  | cons value values ih =>
      cases shapes with
      | nil => simp at hshapes
      | cons shape tailShapes =>
          simp only [List.map_cons] at hshapes
          cases hshapes
          have hvalueWf := hfieldsWf value (by simp)
          have hvalueSize : (panValueFlatten value).length =
              Shape.shapeSize (panValueShape [] value) :=
            panValueFlatten_length_eq_shapeSize value hvalueWf
          have heval' : evalCrepRuntimeExps target expressions =
              some (panValueFlatten value ++ values.flatMap panValueFlatten) := by
            simpa [List.flatMap_cons] using heval
          have hmapEval : expressions.mapM (evalCrepRuntimeExp target) =
              some (panValueFlatten value ++ values.flatMap panValueFlatten) := by
            simpa [evalCrepRuntimeExps_eq_mapM] using heval'
          cases index with
          | zero =>
              have hprefix := mapM_take_of_success
                (fun expression => evalCrepRuntimeExp target expression)
                expressions
                (panValueFlatten value ++ values.flatMap panValueFlatten)
                (Shape.shapeSize (panValueShape [] value))
                hmapEval
              have hprefixValues :
                  (panValueFlatten value ++ values.flatMap panValueFlatten).take
                    (Shape.shapeSize (panValueShape [] value)) =
                  panValueFlatten value := by
                rw [← hvalueSize]
                rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
              have hprefixEval : evalCrepRuntimeExps target
                  (expressions.take (Shape.shapeSize (panValueShape [] value))) =
                  some (panValueFlatten value) := by
                simpa [evalCrepRuntimeExps_eq_mapM, hprefixValues] using hprefix
              simpa [compileField] using hprefixEval
          | succ index =>
              have hindexTail : index < values.length := by simpa using hindex
              have hdrop := mapM_drop_of_success
                (fun expression => evalCrepRuntimeExp target expression)
                expressions
                (panValueFlatten value ++ values.flatMap panValueFlatten)
                (Shape.shapeSize (panValueShape [] value))
                hmapEval
              have hdropValues :
                  (panValueFlatten value ++ values.flatMap panValueFlatten).drop
                    (Shape.shapeSize (panValueShape [] value)) =
                  values.flatMap panValueFlatten := by
                rw [← hvalueSize]
                simp
              have hevalTail : evalCrepRuntimeExps target
                  (expressions.drop (Shape.shapeSize (panValueShape [] value))) =
                  some (values.flatMap panValueFlatten) := by
                simpa [evalCrepRuntimeExps_eq_mapM, hdropValues] using hdrop
              have hfieldsWfTail : ∀ item, item ∈ values →
                  isWfShape [] (panValueShape [] item) = true := by
                intro item hmem
                exact hfieldsWf item (by simp [hmem])
              have htail := ih (values.map (panValueShape []))
                (expressions.drop (Shape.shapeSize (panValueShape [] value)))
                index rfl hfieldsWfTail hindexTail hevalTail
              simpa [compileField, List.getElem_cons_succ] using htail

/-! The arbitrary-expression RField step consumes the inner expression's
compiled-evaluation IH and its shape/well-formedness facts. Source evaluation
selects the indexed field; this is the constructor step used by the enclosing
compile_exp_val_rel induction, not a standalone HOL theorem port. -/
private theorem compileExpHOL_rField_eval_flatten_ofInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (index : Nat)
    (fields : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (compiledExpressions : List (CrepExp (RiscV.Word 64)))
    (fieldShapes : List Shape)
    (hsourceInner : evalPanSemStateExp source expression =
      some (.rStruct fields))
    (hsourceField : evalPanSemStateExp source
      (.rField index expression) = some value)
    (hcompileInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expression = (compiledExpressions, .comb fieldShapes))
    (hfieldShapes : fieldShapes = fields.map (panValueShape []))
    (hfieldsWf : ∀ value, value ∈ fields →
      isWfShape [] (panValueShape [] value) = true)
    (hindex : index < fields.length)
    (hinnerIH : evalCrepRuntimeExps target compiledExpressions =
      some (fields.flatMap panValueFlatten)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).1 =
      some (panValueFlatten value) := by
  have hsourceField' : evalPanSemStateExp source
      (.rField index expression) = some fields[index] := by
    have hsourceInner' : evalPanValueExp source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.rStruct fields) := by
      simpa [evalPanSemStateExp] using hsourceInner
    simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
  have hvalue : value = fields[index] := by
    exact Option.some.inj (hsourceField.symm.trans hsourceField')
  subst value
  have hprojection := evalCrepCompileField_panValueField target fields
    fieldShapes compiledExpressions index hfieldShapes hfieldsWf hindex hinnerIH
  have hcompiledField : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      (.rField index expression) =
      compileField index fieldShapes compiledExpressions := by
    simp [compileExpHOL, hcompileInner]
  rw [hcompiledField]
  exact hprojection

/-! The RField constructor wrapper carries the HOL `compile_exp_val_rel`
inner-expression induction hypothesis: source evaluation, state/code/locals
relations, `localised_exp` (expressed here as no global variables), and the
compiled expression tuple. The IH contributes target evaluation plus the
source shape and well-formedness conclusions. -/
private theorem compileExpHOL_rField_eval_flatten_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (index : Nat)
    (fields : List (PanValue (RiscV.Word 64)))
    (value : PanValue (RiscV.Word 64))
    (compiledExpressions : List (CrepExp (RiscV.Word 64)))
    (fieldShapes : List Shape)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceInner : evalPanSemStateExp source expression =
      some (.rStruct fields))
    (hsourceField : evalPanSemStateExp source
      (.rField index expression) = some value)
    (hindex : index < fields.length)
    (hlocalized : expGlobalVars expression = [])
    (hcompileInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expression = (compiledExpressions, .comb fieldShapes))
    (hinnerIH : evalPanSemStateExp source expression = some (.rStruct fields) →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression = (compiledExpressions, .comb fieldShapes) →
        evalCrepRuntimeExps target compiledExpressions =
            some (fields.flatMap panValueFlatten) ∧
        panValueShape [] (.rStruct fields) = .comb fieldShapes ∧
        isWfShape [] (.comb fieldShapes) = true) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index expression)).1 =
      some (panValueFlatten value) := by
  have hshapeIH := hinnerIH hsourceInner hstate hcode hlocals hlocalized hcompileInner
  rcases hshapeIH with ⟨hinnerEval, hshapeValue, hshapeWf⟩
  have hfieldShapes : fieldShapes = fields.map (panValueShape []) := by
    have hcomb : Shape.comb (fields.map (panValueShape [])) =
        Shape.comb fieldShapes := by
      simpa [panValueShape] using hshapeValue
    have hfieldShapes' : fields.map (panValueShape []) = fieldShapes := by
      injection hcomb
    exact hfieldShapes'.symm
  have hfieldsWf : ∀ field, field ∈ fields →
      isWfShape [] (panValueShape [] field) = true := by
    intro field hmem
    have hshapeMem : panValueShape [] field ∈ fieldShapes := by
      rw [hfieldShapes]
      exact List.mem_map.mpr ⟨field, hmem, rfl⟩
    exact isWfShape_of_mem (by simpa [isWfShape] using hshapeWf) hshapeMem
  exact compileExpHOL_rField_eval_flatten_ofInnerIH context source target
    expression index fields value compiledExpressions fieldShapes hsourceInner
    hsourceField hcompileInner hfieldShapes hfieldsWf hindex hinnerEval

/-! Evidence for an arbitrary-expression RField Call argument whose inner
expression is discharged by the HOL-shaped induction hypothesis. -/
inductive compileArgRFieldInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ) :
    Exp (RiscV.Word 64) → Prop where
  | rField (expression : Exp (RiscV.Word 64)) (index : Nat)
      (fields : List (PanValue (RiscV.Word 64)))
      (compiledExpressions : List (CrepExp (RiscV.Word 64)))
      (fieldShapes : List Shape)
      (hsourceInner : evalPanSemStateExp source expression =
        some (.rStruct fields))
      (hindex : index < fields.length)
      (hlocalized : expGlobalVars expression = [])
      (hcompileInner : compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression = (compiledExpressions, .comb fieldShapes))
      (hinnerIH : evalPanSemStateExp source expression = some (.rStruct fields) →
        stateRel source target →
        codeRel context (panSemCodeAsLookup source.code) target.code →
        localsRel context source.locals target.locals →
        expGlobalVars expression = [] →
        compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression = (compiledExpressions, .comb fieldShapes) →
        evalCrepRuntimeExps target compiledExpressions =
            some (fields.flatMap panValueFlatten) ∧
          panValueShape [] (.rStruct fields) = .comb fieldShapes ∧
          isWfShape [] (.comb fieldShapes) = true) :
      compileArgRFieldInnerIH context source target
        (.rField index expression)

/-! State-owned local specialization of the generic RField case above. It
handles any valid field index and any well-formed field shapes, deriving the
inner compiled evaluation from `locals_rel` rather than assuming a target run. -/
private theorem compileExpHOL_rFieldLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (index : Nat) (fields : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsource : FLOOKUP source.locals name = some (.rStruct fields))
    (hindex : index < fields.length) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rField index (.var .local name))).1 =
      some (panValueFlatten fields[index]) := by
  obtain ⟨slots, hcontext, _hslotsLength, htargetWords, _hvalueWf⟩ :=
    localsRelLookupCtxt context source.locals target.locals name
      (.rStruct fields) hlocals hsource
  have hcontext' : FLOOKUP context.vars name =
      some (.comb (fields.map (panValueShape [])), slots) := by
    simpa [panValueShape] using hcontext
  have hfieldsWfValues : panValueIsWfValues [] fields = true := by
    have hvalueWf := localsRelWfShape context source.locals target.locals name
      (.rStruct fields) hlocals hsource
    simpa [panValueIsWf] using hvalueWf
  have hfieldsWf : ∀ value, value ∈ fields →
      isWfShape [] (panValueShape [] value) = true := by
    intro value hmem
    obtain ⟨fieldIndex, hfieldIndex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hget : fields[fieldIndex]? = some value := by
      rw [List.getElem?_eq_getElem hfieldIndex, hvalue]
    exact panValueIsWf_isWfShape_panValueShape [] value
      (panValueIsWfValues_getElem? hfieldsWfValues hget)
  have htargetValues := mapM_panTheWord_of_wordLab target.locals slots
    (panValueFlatten (.rStruct fields)) htargetWords
  have htargetValues' : slots.mapM
      (fun slot => (target.locals slot).map panTheWord) =
      some (panValueFlatten (.rStruct fields)) := by
    simpa [FLOOKUP] using htargetValues
  have hinnerEval : evalCrepRuntimeExps target
      (slots.map CrepExp.var) = some (fields.flatMap panValueFlatten) := by
    rw [evalCrepRuntimeExps_vars_eq]
    simpa [panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using
      htargetValues'
  have hlocal : source.locals name = some (.rStruct fields) := by
    simpa [FLOOKUP] using hsource
  have hsourceInner : evalPanSemStateExp source (.var .local name) =
      some (.rStruct fields) := by
    simp [evalPanSemStateExp, evalPanValueExp, hlocal]
  have hsourceField : evalPanSemStateExp source
      (.rField index (.var .local name)) = some fields[index] := by
    simp [evalPanSemStateExp, evalPanValueExp, hlocal, hindex]
  have hcompiledInner : compileExpHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      (.var .local name) = (slots.map CrepExp.var,
        .comb (fields.map (panValueShape []))) := by
    simp [compileExpHOL, hcontext']
  exact compileExpHOL_rField_eval_flatten_ofInnerIH context source target
    (.var .local name) index fields fields[index] (slots.map CrepExp.var)
    (fields.map (panValueShape [])) hsourceInner hsourceField hcompiledInner rfl hfieldsWf
    hindex hinnerEval

/-! Flapjack-specific RV64 constant support toward HOL `compile_exp_val_rel`;
    the general expression theorem remains open. -/
theorem compileExpHOL_const_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (value : RiscV.Word 64) (sourceValue : PanValue (RiscV.Word 64))
    (hsourceEval : evalPanSemStateExp source (.const value) = some sourceValue) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).1 = some (panValueFlatten sourceValue) := by
  have hsourceValue : sourceValue = .word value := by
    have hword : PanValue.word value = sourceValue := by
      simpa [evalPanSemStateExp, evalPanValueExp] using hsourceEval
    exact hword.symm
  subst sourceValue
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp, panValueFlatten]

/-! The Const constructor base case for the four-part localized-expression
relation used by Call argument induction. This helper is Flapjack proof
infrastructure; it is not tagged as a standalone HOL theorem. -/
theorem compileExpHOL_const_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (value : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.const value) = [])
    (hsource : evalPanSemStateExp source (.const value) = some (.word value)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.const value)).1 = some [value] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).1.length = Shape.shapeSize
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.const value)).2 ∧
      panValueShape [] (.word value) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.const value)).2 = true := by
  have _ := hstate
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have hsource' := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape] at hsource' ⊢

/-! The Local constructor base case for the four-part localized-expression
relation. `locals_rel` supplies the source value's flattened target slots;
their count and value shape establish the compiler's shape conclusions. -/
theorem compileExpHOL_local_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [])
    (hsourceEval : evalPanSemStateExp source (.var .local name) = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target
        (compileExpHOL compilerContext (.var .local name)).1 =
          some (panValueFlatten value) ∧
      (compileExpHOL compilerContext (.var .local name)).1.length =
        Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 ∧
      panValueShape [] value =
        (compileExpHOL compilerContext (.var .local name)).2 ∧
      isWfShape [] (compileExpHOL compilerContext (.var .local name)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsource : FLOOKUP source.locals name = some value := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceEval
  obtain ⟨slots, hcontext, hslotsLength, _htargetWords, hvalueWf⟩ :=
    localsRelLookupCtxt context source.locals target.locals name value hlocals hsource
  have heval : evalCrepRuntimeExps target
      (compileExpHOL compilerContext (.var .local name)).1 =
        some (panValueFlatten value) := by
    simpa [compilerContext] using
      compileExpHOL_local_eval_flatten context source target name value
        hlocals hsourceEval
  have hcompiled : compileExpHOL compilerContext
      (.var .local name : Exp (RiscV.Word 64)) =
      (slots.map CrepExp.var, panValueShape [] value) := by
    simp [compilerContext, compileExpHOL, hcontext]
  have hflatLength := panValueFlatten_length_eq_shapeSize value hvalueWf
  have hlen : (compileExpHOL compilerContext (.var .local name)).1.length =
      Shape.shapeSize (compileExpHOL compilerContext (.var .local name)).2 := by
    rw [hcompiled]
    simpa [List.length_map] using hslotsLength.trans hflatLength
  have hshape : panValueShape [] value =
      (compileExpHOL compilerContext (.var .local name)).2 := by
    rw [hcompiled]
  have hwf : isWfShape []
      (compileExpHOL compilerContext (.var .local name)).2 = true := by
    rw [hcompiled]
    exact hvalueWf
  have _ := hstate
  have _ := hcode
  have _ := hlocalized
  exact ⟨heval, hlen, hshape, hwf⟩

/-! Full localized-expression IH cases for the two address leaves and the
    fixed RV64 word-size leaf. These support general Call-argument induction;
    they are Flapjack-only constructor proofs, not standalone HOL theorem
    ports. -/
theorem compileExpHOL_baseAddr_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.baseAddr : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .baseAddr =
      some (.word source.baseAddress)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .baseAddr).1 = some [source.baseAddress] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .baseAddr).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .baseAddr).2 ∧
      panValueShape [] (.word source.baseAddress) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .baseAddr).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .baseAddr).2 = true := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hbase, _⟩
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape, hbase]

theorem compileExpHOL_topAddr_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.topAddr : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .topAddr =
      some (.word source.topAddress)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .topAddr).1 = some [source.topAddress] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .topAddr).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .topAddr).2 ∧
      panValueShape [] (.word source.topAddress) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .topAddr).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .topAddr).2 = true := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, htop⟩
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panValueShape, isWfShape, htop]

theorem compileExpHOL_bytesInWord_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : expGlobalVars (.bytesInWord : Exp (RiscV.Word 64)) = [])
    (hsource : evalPanSemStateExp source .bytesInWord =
      some (.word panSemBitVec64BytesInWord)) :
    evalCrepRuntimeExps target
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .bytesInWord).1 =
            some [panSemBitVec64BytesInWord] ∧
      (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
        context.vmax context.eids) .bytesInWord).1.length =
          Shape.shapeSize (compileExpHOL (panToCrepMkCtxtHOL context.vars
            context.funcs context.vmax context.eids) .bytesInWord).2 ∧
      panValueShape [] (.word panSemBitVec64BytesInWord) =
        (compileExpHOL (panToCrepMkCtxtHOL context.vars context.funcs
          context.vmax context.eids) .bytesInWord).2 ∧
      isWfShape [] (compileExpHOL (panToCrepMkCtxtHOL context.vars
        context.funcs context.vmax context.eids) .bytesInWord).2 = true := by
  have _ := hstate
  have _ := hcode
  have _ := hlocals
  have _ := hlocalized
  have _ := hsource
  simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
    panSemBitVec64BytesInWord, CrepBytesInWord.bytesInWord,
    panValueShape, isWfShape]

/-! Under HOL `state_rel`, the source struct table is empty. PanSem therefore
    cannot successfully evaluate named-struct construction or field access.
    These full-IH cases discharge that source-inaccessible part of the
    expression induction; they do not claim named structures are supported by
    the target compiler. -/

inductive compileArgConstOrLocal : Exp (RiscV.Word 64) → Prop where
  | const (value : RiscV.Word 64) : compileArgConstOrLocal (.const value)
  | localVar (name : String) : compileArgConstOrLocal (.var .local name)

inductive compileArgConstLocalAddress : Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstOrLocal expression) :
      compileArgConstLocalAddress expression
  | baseAddr : compileArgConstLocalAddress .baseAddr
  | topAddr : compileArgConstLocalAddress .topAddr
  | bytesInWord : compileArgConstLocalAddress .bytesInWord

private theorem compileArgConstLocalAddress_localized
    {expression : Exp (RiscV.Word 64)}
    (supported : compileArgConstLocalAddress expression) :
    expGlobalVars expression = [] := by
  cases supported with
  | existing _ supported => cases supported <;> simp [expGlobalVars]
  | baseAddr => simp [expGlobalVars]
  | topAddr => simp [expGlobalVars]
  | bytesInWord => simp [expGlobalVars]

/-! Call-argument list case when every argument is a constant or local
variable. This composes the exact Const/Local `compile_exp_val_rel` cases
through HOL `compile_args`; compound expressions remain to be ported. -/
theorem compileArgsHOL_constOrLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    cases hsupported expression hmem with
    | const word =>
        exact compileExpHOL_const_eval_flatten context source target word value heval
    | localVar name =>
        exact compileExpHOL_local_eval_flatten context source target name value
          hlocals heval
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

/-! Full localized-expression IH for Call arguments consisting of Const,
Local, baseAddr, topAddr, and bytesInWord. Each address case uses the fixed
RISC-V state relation; this remains a constructor subset of HOL's general
compile_exp_val_rel induction. -/
theorem compileArgsHOL_constLocalAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstLocalAddress expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileArgsHOL compilerContext expressions) =
        some (values.flatMap panValueFlatten) ∧
      (∀ expression, expression ∈ expressions → ∀ value,
        evalPanSemStateExp source expression = some value →
        expGlobalVars expression = [] →
        evalCrepRuntimeExps target
            (compileExpHOL compilerContext expression).1 =
              some (panValueFlatten value) ∧
          (compileExpHOL compilerContext expression).1.length =
            Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
          panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
          isWfShape [] (compileExpHOL compilerContext expression).2 = true) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [] := by
    intro expression hmem
    cases hsupported expression hmem with
    | existing _ supported => cases supported <;> simp [expGlobalVars]
    | baseAddr => simp [expGlobalVars]
    | topAddr => simp [expGlobalVars]
    | bytesInWord => simp [expGlobalVars]
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
          some (panValueFlatten value) ∧
        (compileExpHOL compilerContext expression).1.length =
          Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
        panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
        isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
    intro expression hmem value heval hstate' hcode' hlocals' hlocalized'
    cases hsupported expression hmem with
    | existing expression' support =>
        cases support with
        | const word =>
            have hword : value = .word word := by
              have hword' : PanValue.word word = value := by
                simpa [evalPanSemStateExp, evalPanValueExp] using heval
              exact hword'.symm
            subst value
            simpa [compilerContext, panValueFlatten] using
              compileExpHOL_const_ofHOLIH context source target word
                hstate' hcode' hlocals' hlocalized' heval
        | localVar name =>
            simpa [compilerContext] using
              compileExpHOL_local_ofHOLIH context source target name value
                hstate' hcode' hlocals' hlocalized' heval
    | baseAddr =>
        have hvalue : value = .word source.baseAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_baseAddr_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
    | topAddr =>
        have hvalue : value = .word source.topAddress := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_topAddr_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
    | bytesInWord =>
        have hvalue : value = .word panSemBitVec64BytesInWord := by
          simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
        subst value
        simpa [compilerContext, panToCrepMkCtxtHOL, panValueFlatten] using
          compileExpHOL_bytesInWord_ofHOLIH context source target hstate' hcode'
            hlocals' hlocalized' heval
  have hcompiled := compileArgsHOL_eval_flatten_of_compileExpRel
    context source target expressions values hstate hcode hlocals hlocalized
    hsource heach
  refine ⟨?_, ?_⟩
  · simpa [compilerContext] using hcompiled
  · intro expression hmem value heval hlocalized'
    simpa [compilerContext] using
      heach expression hmem value heval hstate hcode hlocals hlocalized'

private theorem compileExpHOL_constLocalAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstLocalAddress expression)
    (heval : evalPanSemStateExp source expression = some value) :
    let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
    evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) ∧
      (compileExpHOL compilerContext expression).1.length =
        Shape.shapeSize (compileExpHOL compilerContext expression).2 ∧
      panValueShape [] value = (compileExpHOL compilerContext expression).2 ∧
      isWfShape [] (compileExpHOL compilerContext expression).2 = true := by
  have hsourceList : evalPanSemStateExps source [expression] = some [value] := by
    exact (evalPanSemStateExps_cons source expression [] value []).mpr
      ⟨heval, by simp [evalPanSemStateExps, evalPanValueExps,
        evalPanValueExp.evalPanValueExps]⟩
  have hlistSupport : ∀ item, item ∈ [expression] →
      compileArgConstLocalAddress item := by
    intro item hmem
    have heq : item = expression := by simpa using hmem
    subst item
    exact hsupported
  obtain ⟨_, hperExpression⟩ := compileArgsHOL_constLocalAddress_ofHOLIH
    context source target [expression] [value] hstate hcode hlocals
    hlistSupport hsourceList
  exact hperExpression expression (by simp) value heval
    (compileArgConstLocalAddress_localized hsupported)

inductive compileArgConstLocalAddressOrStruct : Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalAddress expression) :
      compileArgConstLocalAddressOrStruct expression
  | rStruct (fields : List (Exp (RiscV.Word 64)))
      (supported : ∀ expression, expression ∈ fields →
        compileArgConstLocalAddress expression) :
      compileArgConstLocalAddressOrStruct (.rStruct fields)
  | loadOneConst (address : RiscV.Word 64) :
      compileArgConstLocalAddressOrStruct (.load .one (.const address))

private theorem compileArgConstLocalAddressOrStruct_localized
    {expression : Exp (RiscV.Word 64)}
    (supported : compileArgConstLocalAddressOrStruct expression) :
    expGlobalVars expression = [] := by
  cases supported with
  | existing _ supported => exact compileArgConstLocalAddress_localized supported
  | loadOneConst _ => simp [expGlobalVars]
  | rStruct fields hfields =>
      induction fields with
      | nil => simp [expGlobalVars, expGlobalVars.expGlobalVarsList]
      | cons field fields ih =>
          have hfield := compileArgConstLocalAddress_localized
            (hfields field (by simp))
          have htail : ∀ expression, expression ∈ fields →
              compileArgConstLocalAddress expression := by
            intro expression hmem
            exact hfields expression (by simp [hmem])
          have htailLocalized : expGlobalVars.expGlobalVarsList fields = [] := by
            simpa only [expGlobalVars] using ih htail
          simp only [expGlobalVars]
          simp [expGlobalVars.expGlobalVarsList, hfield, htailLocalized]

/-! One additional `compile_exp_val_rel` constructor: an `RStruct` whose
fields are each constants or local variables. Its nested argument list is
proved with the leaf cases above; this does not cover nested structs or other
compound expressions. -/
private theorem compileExpListHOL_flatMap_eq_compileArgsHOL
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (fields : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext fields).flatMap Prod.fst =
      compileArgsHOL compilerContext fields := by
  induction fields with
  | nil => simp [compileExpHOL.compileExpListHOL, compileArgsHOL]
  | cons field fields ih =>
      simp [compileExpHOL.compileExpListHOL, compileArgsHOL, ih]

private theorem compileExpListHOL_map_snd_eq_map_compileExp_shape
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (fields : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext fields).map Prod.snd =
      fields.map (fun expression => (compileExpHOL compilerContext expression).2) := by
  induction fields with
  | nil => simp [compileExpHOL.compileExpListHOL]
  | cons field fields ih =>
      simp [compileExpHOL.compileExpListHOL, ih]

private theorem compileExpListHOL_map_fst_eq_map_compileExp
    (compilerContext : PanToCrepHOLContext (RiscV.Word 64))
    (expressions : List (Exp (RiscV.Word 64))) :
    (compileExpHOL.compileExpListHOL compilerContext expressions).map Prod.fst =
      expressions.map (fun expression => (compileExpHOL compilerContext expression).1) := by
  induction expressions with
  | nil => simp [compileExpHOL.compileExpListHOL]
  | cons expression expressions ih =>
      simp [compileExpHOL.compileExpListHOL, ih]

theorem compileExpHOL_rStruct_constOrLocal_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (fields : List (Exp (RiscV.Word 64)))
    (fieldValues : List (PanValue (RiscV.Word 64)))
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ fields →
      compileArgConstOrLocal expression)
    (hsource : evalPanSemStateExp source (.rStruct fields) =
      some (.rStruct fieldValues)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rStruct fields)).1 =
      some (panValueFlatten (.rStruct fieldValues)) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
    simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
      evalPanValueExps] using hsource
  have hcompiled := compileArgsHOL_constOrLocal_eval_flatten context source target
    fields fieldValues hlocals hsupported hsourceFields
  simpa [compilerContext, compileExpHOL,
    compileExpListHOL_flatMap_eq_compileArgsHOL,
    panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled

inductive compileArgConstLocalOrStruct : Exp (RiscV.Word 64) → Prop where
  | const (value : RiscV.Word 64) : compileArgConstLocalOrStruct (.const value)
  | localVar (name : String) : compileArgConstLocalOrStruct (.var .local name)
  | rStruct (fields : List (Exp (RiscV.Word 64)))
      (hsupported : ∀ expression, expression ∈ fields →
        compileArgConstOrLocal expression) :
      compileArgConstLocalOrStruct (.rStruct fields)

inductive compileArgConstLocalStructAddress
    (source : PanSemState (RiscV.Word 64) (FfiState σ)) :
    Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalOrStruct expression) :
      compileArgConstLocalStructAddress source expression
  | recordFieldLocal (name : String) (index : Nat)
      (fields : List (PanValue (RiscV.Word 64)))
      (hsource : FLOOKUP source.locals name = some (.rStruct fields))
      (hindex : index < fields.length) :
      compileArgConstLocalStructAddress source
        (.rField index (.var .local name))
  | baseAddress : compileArgConstLocalStructAddress source .baseAddr
  | topAddress : compileArgConstLocalStructAddress source .topAddr
  | bytesInWord : compileArgConstLocalStructAddress source .bytesInWord

private theorem compileExpHOL_constLocalStructAddress_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstLocalStructAddress source expression)
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, hbase, htop⟩
  cases hsupported with
  | baseAddress =>
      have hvalue : value = .word source.baseAddress := by
        simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
      subst value
      simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
        panValueFlatten, hbase]
  | topAddress =>
      have hvalue : value = .word source.topAddress := by
        simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
      subst value
      simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
        panValueFlatten, htop]
  | bytesInWord =>
      have hvalue : value = .word panSemBitVec64BytesInWord := by
        simpa [evalPanSemStateExp, evalPanValueExp] using heval.symm
      subst value
      simp [compileExpHOL, evalCrepRuntimeExps, evalCrepRuntimeExp,
        panValueFlatten, panSemBitVec64BytesInWord,
        CrepBytesInWord.bytesInWord]
  | existing _ supported =>
      cases supported with
      | const word =>
          exact compileExpHOL_const_eval_flatten context source target word value heval
      | localVar name =>
          exact compileExpHOL_local_eval_flatten context source target name value
            hlocals heval
      | rStruct fields hfields =>
          cases value with
          | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
          | rStruct fieldValues =>
              exact compileExpHOL_rStruct_constOrLocal_eval_flatten context source
                target fields fieldValues hlocals hfields heval
          | nStruct name fields => simp [evalPanSemStateExp, evalPanValueExp] at heval
  | recordFieldLocal name index fields hsource hindex =>
      have hlocal : source.locals name = some (.rStruct fields) := by
        simpa [FLOOKUP] using hsource
      unfold evalPanSemStateExp at heval
      simp [evalPanValueExp, hlocal, hindex] at heval
      have hvalue : value = fields[index] := heval.symm
      subst value
      exact compileExpHOL_rFieldLocal_eval_flatten context source target
        name index fields hlocals hsource hindex

/-! A source `RStruct` field may itself be an arbitrary-inner RField or one of
the already-proved Const/Local cases. This supplies the per-field case used
when a Call argument constructs a record containing a selected subrecord. -/
private theorem compileExpHOL_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expression : Exp (RiscV.Word 64)) (value : PanValue (RiscV.Word 64))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : compileArgConstOrLocal expression ∨
      compileArgRFieldInnerIH context source target expression)
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  cases hsupported with
  | inl supported =>
      cases supported with
      | const word =>
          exact compileExpHOL_const_eval_flatten context source target word value heval
      | localVar name =>
          exact compileExpHOL_local_eval_flatten context source target name value
            hlocals heval
  | inr supported =>
      cases supported with
      | rField inner index fields compiledExpressions fieldShapes hsourceInner
          hindex hlocalized hcompileInner hinnerIH =>
        have hsourceField : evalPanSemStateExp source
            (.rField index inner) = some fields[index] := by
          have hsourceInner' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord inner
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
            some (.rStruct fields) := by
            simpa [evalPanSemStateExp] using hsourceInner
          simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
        have hvalue : value = fields[index] :=
          Option.some.inj (heval.symm.trans hsourceField)
        subst value
        exact compileExpHOL_rField_eval_flatten_ofHOLIH context source target
          inner index fields fields[index] compiledExpressions fieldShapes
          hstate hcode hlocals hsourceInner hsourceField hindex hlocalized
          hcompileInner hinnerIH

private theorem compileArgsHOL_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ expressions →
      compileArgConstOrLocal expression ∨
        compileArgRFieldInnerIH context source target expression)
    (hsource : evalPanSemStateExps source expressions = some values) :
    evalCrepRuntimeExps target
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some (values.flatMap panValueFlatten) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      evalCrepRuntimeExps target (compileExpHOL compilerContext expression).1 =
        some (panValueFlatten value) := by
    intro expression hmem value heval
    exact compileExpHOL_constOrRFieldInnerIH_eval_flatten context source target
      expression value hstate hcode hlocals (hsupported expression hmem) heval
  simpa [compilerContext] using
    compileArgsHOL_eval_flatten_of_each compilerContext source target expressions values
      hsource heach

private theorem compileExpHOL_rStruct_constOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (fields : List (Exp (RiscV.Word 64)))
    (fieldValues : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsupported : ∀ expression, expression ∈ fields →
      compileArgConstOrLocal expression ∨
        compileArgRFieldInnerIH context source target expression)
    (hsource : evalPanSemStateExp source (.rStruct fields) =
      some (.rStruct fieldValues)) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.rStruct fields)).1 =
      some (panValueFlatten (.rStruct fieldValues)) := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
    simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
      evalPanValueExps] using hsource
  have hcompiled := compileArgsHOL_constOrRFieldInnerIH_eval_flatten
    context source target fields fieldValues hstate hcode hlocals hsupported
    hsourceFields
  simpa [compilerContext, compileExpHOL,
    compileExpListHOL_flatMap_eq_compileArgsHOL,
    panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled

/-! Mixed Call-argument evidence combines the already-proved constructors
with arbitrary-inner RField evidence. -/
private theorem evalPanSemStateExp_loadByte_const_riscvTarget
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.loadByte (.const address)) =
      (evalCrepRuntimeExp (riscvCrepWordTarget target)
        (.loadByte (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, hbe, _, _, _⟩
  have hmemoryView : panValueWordMemory source.memory =
      crepRuntimeMemoryView target.memory := by
    funext query
    simp [panValueWordMemory, crepRuntimeMemoryView, hmemory]
  have hread :
      panModelReadByte panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be =
        panModelReadByte (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian := by
    rw [← hdomain, ← hmemoryView, ← hbe]
    cases source.be with
    | false =>
        simp only [panModelReadByte,
          RiscV.panRiscVMemoryModelForEndian,
          panSemBitVec64ByteAlign_runtime_eq_panRiscV,
          panSemBitVec64GetByte_runtime_eq_riscvModel]
        rfl
    | true =>
        simp only [panModelReadByte,
          RiscV.panRiscVMemoryModelForEndian,
          panSemBitVec64ByteAlign_runtime_eq_panRiscV,
          panSemBitVec64GetByte_runtime_eq_riscvModel]
        rfl
  calc
    evalPanSemStateExp source (.loadByte (.const address)) =
        (panModelReadByte panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be).map
            PanValue.word := by
      simp [evalPanSemStateExp, evalPanValueExp,
        panSemBitVec64MemoryAccess,
        panValueMemoryAccessOfModel, panSemBitVec64BytesInWord]
    _ = (panModelReadByte (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian).map PanValue.word := by
      rw [hread]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget target)
          (.loadByte (.const address))).map PanValue.word := by
      simp [evalCrepRuntimeExp, crepRuntimeLoadByte_wordTarget_eq_riscv]

private theorem evalPanSemStateExp_load32_const_riscvTarget
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.load32 (.const address)) =
      (evalCrepRuntimeExp (riscvCrepWordTarget target)
        (.load32 (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, hbe, _, _, _⟩
  have hmemoryView : panValueWordMemory source.memory =
      crepRuntimeMemoryView target.memory := by
    funext query
    simp [panValueWordMemory, crepRuntimeMemoryView, hmemory]
  have hread :
      panModelRead32 panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be =
        panModelRead32 (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian := by
    rw [← hdomain, ← hmemoryView, ← hbe]
    cases source.be with
    | false =>
        simp only [panModelRead32,
          RiscV.panRiscVMemoryModelForEndian,
          panSemBitVec64ByteAlign_runtime_eq_panRiscV,
          panSemBitVec64Aligned_eq_riscvModel,
          panSemBitVec64GetByte_runtime_eq_riscvModel,
          panSemBitVec64WordOfBytes32_eq_riscvModel]
        rfl
    | true =>
        simp only [panModelRead32,
          RiscV.panRiscVMemoryModelForEndian,
          panSemBitVec64ByteAlign_runtime_eq_panRiscV,
          panSemBitVec64Aligned_eq_riscvModel,
          panSemBitVec64GetByte_runtime_eq_riscvModel,
          panSemBitVec64WordOfBytes32_eq_riscvModel]
        rfl
  calc
    evalPanSemStateExp source (.load32 (.const address)) =
        (panModelRead32 panSemBitVec64WordModel source.memaddrs
          (panValueWordMemory source.memory) panSemBitVec64BytesInWord address source.be).map
            PanValue.word := by
      simp [evalPanSemStateExp, evalPanValueExp,
        panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
        panSemBitVec64BytesInWord]
    _ = (panModelRead32 (RiscV.panRiscVMemoryModelForEndian target.bigEndian)
          target.memaddrs (crepRuntimeMemoryView target.memory)
          (BitVec.ofNat 64 (64 / 8)) address target.bigEndian).map PanValue.word := by
      rw [hread]
    _ = (evalCrepRuntimeExp (riscvCrepWordTarget target)
          (.load32 (.const address))).map PanValue.word := by
      simp [evalCrepRuntimeExp, crepRuntimeLoad32_wordTarget_eq_riscv]

private theorem evalPanSemStateExp_loadOne_const_stateRel
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source (.load .one (.const address)) =
      (evalCrepRuntimeExp target (.load (.const address))).map PanValue.word := by
  rcases hstate with ⟨hmemory, hdomain, _, _, _, _, _, _, _, _⟩
  simp [evalPanSemStateExp, evalPanValueExp, panValueFlatLoad,
    panValueFlatLoadFuel, panValueFlatReadWord, panSemBitVec64MemoryAccess,
    panValueMemoryAccessOfModel, evalCrepRuntimeExp, crepRuntimeLoad,
    isWfShape, hmemory, hdomain]

private theorem evalPanSemStateExp_loadTwo_const_stateRel
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : RiscV.Word 64)
    (hstate : stateRel source target) :
    evalPanSemStateExp source
        (.load (.comb [.one, .one]) (.const address)) =
      ((evalCrepRuntimeExp target (.load (.const address))).bind fun first =>
        (evalCrepRuntimeExp target (.load (.const (address + 8)))).map fun second =>
          .rStruct [.word first, .word second]) := by
  rcases hstate with ⟨hmemory, hdomain, _, hstructs, _, _, _, _, _, _⟩
  simp [evalPanSemStateExp, evalPanValueExp, panValueFlatLoad,
    panValueFlatLoadFuel, panValueFlatLoadListFuel, panValueFlatReadWord,
    panSemBitVec64MemoryAccess, panValueMemoryAccessOfModel,
    panValueFlatContextFuel, panValueFlatShapeFuel,
    panValueFlatShapeFuel.panValueFlatShapeListFuel,
    evalCrepRuntimeExp, crepRuntimeLoad, panValueFlatOffset,
    shapeSizeWithContext, panSemBitVec64BytesInWord,
    isWfShape, isWfShape.isWfShapeList, hmemory, hdomain, hstructs]
  cases target.memaddrs address <;>
    cases target.memaddrs (address + 8) <;>
    simp

/-! Restricted, untagged Call-argument induction evidence. In addition to the
existing Const/Local, record, address, byte-load, and word-load cases, this
relation now admits a two-word flat Load only at a constant address and under
the canonical RISC-V target invariant. This is argument-evaluation support;
it does not establish the complete HOL `compile_exp_val_rel` induction. -/
inductive compileArgConstLocalStructAddressOrRFieldInnerIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ) :
    Exp (RiscV.Word 64) → Prop where
  | existing (expression : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddress source expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression
  | rField (expression : Exp (RiscV.Word 64)) (index : Nat)
      (supported : compileArgRFieldInnerIH context source target
        (.rField index expression)) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rField index expression)
  | rStructRField (fields : List (Exp (RiscV.Word 64)))
      (hfields : ∀ expression, expression ∈ fields →
        compileArgConstOrLocal expression ∨
          compileArgRFieldInnerIH context source target expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rStruct fields)
  | rStructNested (fields : List (Exp (RiscV.Word 64)))
      (hfields : ∀ expression, expression ∈ fields →
        compileArgConstLocalStructAddressOrRFieldInnerIH context source target expression) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.rStruct fields)
  | globalVar (name : String) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.var .global name)
  | baseAddr :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .baseAddr
  | topAddr :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .topAddr
  | bytesInWord :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        .bytesInWord
  | nStruct (name : String) (fields : List (FieldName × Exp (RiscV.Word 64))) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.nStruct name fields)
  | nField (name : FieldName) (expression : Exp (RiscV.Word 64)) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.nField name expression)
  | loadByteConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte (.const address))
  | load32ConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 (.const address))
  | loadOneConst (address : RiscV.Word 64) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load .one (.const address))
  | loadTwoConstCanonicalTarget (address : RiscV.Word 64)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load (.comb [.one, .one]) (.const address))
  | load32LocalCanonicalTarget (name : String) (slot : Nat)
      (hvariable : FLOOKUP context.vars name = some (.one, [slot]))
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 (.var .local name))
  | loadByteLocalCanonicalTarget (name : String) (slot : Nat)
      (hvariable : FLOOKUP context.vars name = some (.one, [slot]))
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte (.var .local name))
  | loadByteSupportedAddress (address : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddressOrRFieldInnerIH
        context source target address)
      (hshape : (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax } address).2 = .one)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.loadByte address)
  | load32SupportedAddress (address : Exp (RiscV.Word 64))
      (supported : compileArgConstLocalStructAddressOrRFieldInnerIH
        context source target address)
      (hshape : (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax } address).2 = .one)
      (hcanonical : target = riscvCrepWordTarget target) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.load32 address)
  | panOpMul (left right : Exp (RiscV.Word 64))
      (hleft : compileArgConstLocalStructAddressOrRFieldInnerIH context source target left)
      (hright : compileArgConstLocalStructAddressOrRFieldInnerIH context source target right) :
      compileArgConstLocalStructAddressOrRFieldInnerIH context source target
        (.panOp .mul [left, right])

private theorem evalCrepRuntimeExps_length_of_some
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (expressions : List (CrepExp (RiscV.Word 64)))
    (values : List (RiscV.Word 64))
    (heval : evalCrepRuntimeExps state expressions = some values) :
    values.length = expressions.length := by
  induction expressions generalizing values with
  | nil => simp [evalCrepRuntimeExps] at heval; subst values; rfl
  | cons expression expressions ih =>
      cases hhead : evalCrepRuntimeExp state expression with
      | none => simp [evalCrepRuntimeExps, hhead] at heval
      | some head =>
          cases htail : evalCrepRuntimeExps state expressions with
          | none => simp [evalCrepRuntimeExps, hhead, htail] at heval
          | some tail =>
              have hvalues : values = head :: tail := by
                simpa [evalCrepRuntimeExps, hhead, htail] using heval.symm
              subst values
              simp [ih tail htail]

private theorem compileField_shape_eq_panValueField
    (fields : List (PanValue (RiscV.Word 64))) (index : Nat)
    (expressions : List (CrepExp (RiscV.Word 64)))
    (hindex : index < fields.length) :
    (compileField index (fields.map (panValueShape [])) expressions).2 =
      panValueShape [] fields[index] := by
  induction fields generalizing index expressions with
  | nil => simp at hindex
  | cons field fields ih =>
      cases index with
      | zero => simp [compileField]
      | succ index =>
          have hindex' : index < fields.length := by simpa using hindex
          simpa [compileField, List.getElem_cons_succ] using
            ih index (expressions.drop (Shape.shapeSize (panValueShape [] field))) hindex'

private theorem compileArgConstLocalStructAddressOrRFieldInnerIH_eval_flatten
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    {expression : Exp (RiscV.Word 64)}
    (evidence : compileArgConstLocalStructAddressOrRFieldInnerIH
      context source target expression)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (value : PanValue (RiscV.Word 64))
    (heval : evalPanSemStateExp source expression = some value) :
    evalCrepRuntimeExps target
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expression).1 = some (panValueFlatten value) := by
  revert value
  induction evidence with
  | existing expression supported =>
      intro value heval
      exact compileExpHOL_constLocalStructAddress_eval_flatten context source
        target expression value hstate hlocals supported heval
  | rField inner index supported =>
      cases supported with
      | rField _ _ fields compiledExpressions fieldShapes hsourceInner
          hindex hlocalized hcompileInner hinnerIH =>
        intro value heval
        have hsourceField : evalPanSemStateExp source
            (.rField index inner) = some fields[index] := by
          have hsourceInner' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord inner
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
            some (.rStruct fields) := by
            simpa [evalPanSemStateExp] using hsourceInner
          simp [evalPanSemStateExp, evalPanValueExp, hsourceInner', hindex]
        have hvalue : value = fields[index] :=
          Option.some.inj (heval.symm.trans hsourceField)
        subst value
        exact compileExpHOL_rField_eval_flatten_ofHOLIH context source target
          inner index fields fields[index] compiledExpressions fieldShapes
          hstate hcode hlocals hsourceInner hsourceField hindex hlocalized
          hcompileInner hinnerIH
  | rStructRField fields hfields =>
      intro value heval
      cases value with
      | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | nStruct name values => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | rStruct fieldValues =>
          exact compileExpHOL_rStruct_constOrRFieldInnerIH_eval_flatten
            context source target fields fieldValues hstate hcode hlocals
            hfields heval
  | rStructNested fields hfields ih =>
      intro value heval
      cases value with
      | word word => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | nStruct name values => simp [evalPanSemStateExp, evalPanValueExp] at heval
      | rStruct fieldValues =>
          have hsourceFields : evalPanSemStateExps source fields = some fieldValues := by
            simpa [evalPanSemStateExp, evalPanSemStateExps, evalPanValueExp,
              evalPanValueExps] using heval
          let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
          have heach : ∀ field, field ∈ fields → ∀ fieldValue,
              evalPanSemStateExp source field = some fieldValue →
              evalCrepRuntimeExps target
                (compileExpHOL compilerContext field).1 =
                  some (panValueFlatten fieldValue) := by
            intro field hmem fieldValue hfield
            exact ih field hmem fieldValue hfield
          have hcompiled := compileArgsHOL_eval_flatten_of_each compilerContext
            source target fields fieldValues hsourceFields heach
          simpa [compilerContext, compileExpHOL,
            compileExpListHOL_flatMap_eq_compileArgsHOL,
            panValueFlatten_rStruct, panValueFlattenValues_eq_flatMap] using hcompiled
  | globalVar name =>
      intro value heval
      have hglobals := stateRel_globals source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hglobals, FEMPTY] at heval
  | baseAddr =>
      intro value heval
      have hsource : evalPanSemStateExp source .baseAddr =
          some (.word source.baseAddress) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word source.baseAddress :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_baseAddr_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | topAddr =>
      intro value heval
      have hsource : evalPanSemStateExp source .topAddr =
          some (.word source.topAddress) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word source.topAddress :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_topAddr_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | bytesInWord =>
      intro value heval
      have hsource : evalPanSemStateExp source .bytesInWord =
          some (.word panSemBitVec64BytesInWord) := by
        simp [evalPanSemStateExp, evalPanValueExp]
      have hvalue : value = .word panSemBitVec64BytesInWord :=
        (Option.some.inj (hsource.symm.trans heval)).symm
      subst value
      have hcompiled := compileExpHOL_bytesInWord_ofHOLIH context source target
        hstate hcode hlocals (by simp [expGlobalVars]) hsource
      simpa [panToCrepMkCtxtHOL, panValueFlatten] using hcompiled.1
  | nStruct name fields =>
      intro value heval
      have hstructs := stateRel_structs source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hstructs, lookupInfo] at heval
  | nField name expression =>
      intro value heval
      have hstructs := stateRel_structs source target hstate
      simp [evalPanSemStateExp, evalPanValueExp, hstructs, lookupInfo] at heval
      simp only [Option.bind_eq_some_iff] at heval
      rcases heval with ⟨innerValue, _, hresult⟩
      cases innerValue <;> simp at hresult
  | loadByteConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.loadByte (.const address)) =
        (evalCrepRuntimeExp target (.loadByte (.const address))).map PanValue.word := by
        simpa [hcanonical.symm] using hsourceTarget
      rw [hsourceTarget'] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target
              (.loadByte (.const address)) = some word := by
            simpa using heval
          simp [compileExpHOL, evalCrepRuntimeExps, panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | load32ConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.load32 (.const address)) =
        (evalCrepRuntimeExp target (.load32 (.const address))).map PanValue.word := by
        simpa [hcanonical.symm] using hsourceTarget
      rw [hsourceTarget'] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target
              (.load32 (.const address)) = some word := by
            simpa using heval
          simp [compileExpHOL, evalCrepRuntimeExps, panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | loadOneConst address =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadOne_const_stateRel
        source target address hstate
      rw [hsourceTarget] at heval
      cases value with
      | word word =>
          have htarget : evalCrepRuntimeExp target (.load (.const address)) =
              some word := by
            simpa using heval
          let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
          have hcompiled : compileExpHOL compilerContext
              (.load .one (.const address)) =
              ([.load (.const address)], .one) := by
            simp [compileExpHOL, compilerContext, loadShape,
              CrepBytesInWord.bytesInWord]
          simp [compilerContext, hcompiled, evalCrepRuntimeExps,
            panValueFlatten, htarget]
      | rStruct fields => simp at heval
      | nStruct name fields => simp at heval
  | loadTwoConstCanonicalTarget address hcanonical =>
      intro value heval
      have hsourceTarget := evalPanSemStateExp_loadTwo_const_stateRel
        source target address hstate
      have hsourceTarget' : evalPanSemStateExp source
          (.load (.comb [.one, .one]) (.const address)) =
        (evalCrepRuntimeExp target (.load (.const address))).bind fun first =>
          (evalCrepRuntimeExp target
            (.load (.const (address + 8)))).map fun second =>
              .rStruct [.word first, .word second] := by
        simpa [hcanonical.symm] using hsourceTarget
      have haddressOffset : address + (8 : RiscV.Word 64) =
          address + BitVec.ofNat 64 8 := by rfl
      rw [haddressOffset] at hsourceTarget'
      rw [hsourceTarget'] at heval
      cases hfirst : evalCrepRuntimeExp target (.load (.const address)) with
      | none => simp [hfirst] at heval
      | some first =>
          cases hsecond : evalCrepRuntimeExp target
              (.load (.const (address + BitVec.ofNat 64 8))) with
          | none => simp [hsecond] at heval
          | some second =>
              have hvalue : value = .rStruct [.word first, .word second] := by
                have hequality :
                    some (.rStruct [.word first, .word second]) = some value := by
                  simpa [hfirst, hsecond] using heval
                exact (Option.some.inj hequality).symm
              subst value
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hcompiledLoad :
                  compileExpHOL compilerContext
                    (.load (.comb [.one, .one]) (.const address)) =
                    ([.load (.const address),
                      .load (.op .add
                        [.const address, .const (BitVec.ofNat 64 8)])],
                      .comb [.one, .one]) := by
                simp [compileExpHOL, compilerContext, loadShape,
                  CrepBytesInWord.bytesInWord, Shape.shapeSize]
              have htargetAddressNext :
                  evalCrepRuntimeExp target
                    (.op .add
                      [.const address, .const (BitVec.ofNat 64 8)]) =
                    some (address + 8) := by
                have hwordArgs :
                    ([.const address, .const (BitVec.ofNat 64 8)] :
                      List (CrepExp (RiscV.Word 64))).mapM
                        (evalCrepRuntimeExp (riscvCrepWordTarget target)) =
                      some [address, 8] := by
                  simp [evalCrepRuntimeExp]
                have hwordResult :
                    (([.const address, .const (BitVec.ofNat 64 8)] :
                      List (CrepExp (RiscV.Word 64))).mapM
                        (evalCrepRuntimeExp (riscvCrepWordTarget target))).bind
                        (wordOpHOL .add) = some (address + 8) := by
                  rw [hwordArgs]
                  simp [wordOpHOL, wordOp]
                rw [hcanonical]
                rw [evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
                exact hwordResult
              have htargetRun :
                  evalCrepRuntimeExps target
                      (compileExpHOL compilerContext
                        (.load (.comb [.one, .one]) (.const address))).1 =
                    some [first, second] := by
                rw [hcompiledLoad]
                have hloadBind (expression : CrepExp (RiscV.Word 64)) :
                    evalCrepRuntimeExp target (.load expression) =
                      (evalCrepRuntimeExp target expression).bind
                        (crepRuntimeLoad target) := by
                  simp only [evalCrepRuntimeExp]
                  rfl
                have hcompiledSecond : evalCrepRuntimeExp target
                    (.load (.op .add
                      [.const address, .const (BitVec.ofNat 64 8)])) = some second := by
                  rw [hloadBind, htargetAddressNext]
                  have hsecondLoad : crepRuntimeLoad target
                      (address + 8) = some second := by
                    simpa [evalCrepRuntimeExp] using hsecond
                  exact hsecondLoad
                simp [evalCrepRuntimeExps, hfirst, hcompiledSecond]
              simpa [compilerContext, panValueFlatten, panValueFlattenValues] using
                htargetRun
  | load32LocalCanonicalTarget name slot hvariable hcanonical =>
      intro value heval
      cases haddressValue : evalPanSemStateExp source (.var .local name) with
      | none =>
          have hlocal : source.locals name = none := by
            simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
          simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
      | some addressValue =>
          cases addressValue with
          | word address =>
              have hlocal : source.locals name = some (.word address) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              have hsourceConst :
                  evalPanSemStateExp source (.load32 (.var .local name)) =
                    evalPanSemStateExp source (.load32 (.const address)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hlocal]
              have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
                source target address hstate
              have hsourceTarget' : evalPanSemStateExp source
                  (.load32 (.const address)) =
                (evalCrepRuntimeExp target (.load32 (.const address))).map
                  PanValue.word := by
                simpa [hcanonical.symm] using hsourceTarget
              have hcompiledLocal := compileExpHOL_local_eval_flatten context
                source target name (.word address) hlocals haddressValue
              have htargetVariable :
                  evalCrepRuntimeExp target (.var slot) = some address := by
                have hmap : evalCrepRuntimeExps target [.var slot] =
                    some [address] := by
                  simpa [compileExpHOL, hvariable, panValueFlatten] using
                    hcompiledLocal
                cases hvalue : evalCrepRuntimeExp target (.var slot) with
                | none => simp [evalCrepRuntimeExps, hvalue] at hmap
                | some word =>
                    have hword : word = address := by
                      simpa [evalCrepRuntimeExps, hvalue] using hmap
                    simp [hword]
              have htargetLoad :
                  evalCrepRuntimeExp target (.load32 (.var slot)) =
                    evalCrepRuntimeExp target (.load32 (.const address)) := by
                simp [evalCrepRuntimeExp, htargetVariable]
              have hcompiled :
                  (compileExpHOL
                    { vars := context.vars, funcs := context.funcs,
                      eids := context.eids, vmax := context.vmax }
                    (.load32 (.var .local name))).1 = [.load32 (.var slot)] := by
                simp [compileExpHOL, hvariable]
              rw [hsourceConst, hsourceTarget'] at heval
              cases value with
              | word word =>
                  have htarget :
                      evalCrepRuntimeExp target (.load32 (.const address)) =
                        some word := by
                    simpa using heval
                  simp [hcompiled, evalCrepRuntimeExps,
                    htargetLoad, htarget, panValueFlatten]
              | rStruct fields => simp at heval
              | nStruct name fields => simp at heval
          | rStruct fields =>
              have hlocal : source.locals name = some (.rStruct fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
          | nStruct structName fields =>
              have hlocal : source.locals name = some (.nStruct structName fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
  | loadByteLocalCanonicalTarget name slot hvariable hcanonical =>
      intro value heval
      cases haddressValue : evalPanSemStateExp source (.var .local name) with
      | none =>
          have hlocal : source.locals name = none := by
            simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
          simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
      | some addressValue =>
          cases addressValue with
          | word address =>
              have hlocal : source.locals name = some (.word address) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              have hsourceConst :
                  evalPanSemStateExp source (.loadByte (.var .local name)) =
                    evalPanSemStateExp source (.loadByte (.const address)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hlocal]
              have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
                source target address hstate
              have hsourceTarget' : evalPanSemStateExp source
                  (.loadByte (.const address)) =
                (evalCrepRuntimeExp target (.loadByte (.const address))).map
                  PanValue.word := by
                simpa [hcanonical.symm] using hsourceTarget
              have hcompiledLocal := compileExpHOL_local_eval_flatten context
                source target name (.word address) hlocals haddressValue
              have htargetVariable :
                  evalCrepRuntimeExp target (.var slot) = some address := by
                have hmap : evalCrepRuntimeExps target [.var slot] =
                    some [address] := by
                  simpa [compileExpHOL, hvariable, panValueFlatten] using
                    hcompiledLocal
                cases hvalue : evalCrepRuntimeExp target (.var slot) with
                | none => simp [evalCrepRuntimeExps, hvalue] at hmap
                | some word =>
                    have hword : word = address := by
                      simpa [evalCrepRuntimeExps, hvalue] using hmap
                    simp [hword]
              have htargetLoad :
                  evalCrepRuntimeExp target (.loadByte (.var slot)) =
                    evalCrepRuntimeExp target (.loadByte (.const address)) := by
                simp [evalCrepRuntimeExp, htargetVariable]
              have hcompiled :
                  (compileExpHOL
                    { vars := context.vars, funcs := context.funcs,
                      eids := context.eids, vmax := context.vmax }
                    (.loadByte (.var .local name))).1 = [.loadByte (.var slot)] := by
                simp [compileExpHOL, hvariable]
              rw [hsourceConst, hsourceTarget'] at heval
              cases value with
              | word word =>
                  have htarget :
                      evalCrepRuntimeExp target (.loadByte (.const address)) =
                        some word := by
                    simpa using heval
                  simp [hcompiled, evalCrepRuntimeExps,
                    htargetLoad, htarget, panValueFlatten]
              | rStruct fields => simp at heval
              | nStruct name fields => simp at heval
          | rStruct fields =>
              have hlocal : source.locals name = some (.rStruct fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
          | nStruct structName fields =>
              have hlocal : source.locals name = some (.nStruct structName fields) := by
                simpa [evalPanSemStateExp, evalPanValueExp] using haddressValue
              simp [evalPanSemStateExp, evalPanValueExp, hlocal] at heval
  | loadByteSupportedAddress address supported hshape hcanonical ihAddress =>
      intro value heval
      cases haddress : evalPanSemStateExp source address with
      | none =>
          have hsourceAddress :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using haddress
          simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
      | some addressValue =>
          cases addressValue with
          | word addressWord =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word addressWord) := by
                simpa [evalPanSemStateExp] using haddress
              have hsourceByte :
                  evalPanSemStateExp source (.loadByte address) =
                    evalPanSemStateExp source (.loadByte (.const addressWord)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress]
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hshape' : (compileExpHOL compilerContext address).2 = .one := by
                simpa [compilerContext] using hshape
              have hcompiledAddressRun :
                  evalCrepRuntimeExps target
                    (compileExpHOL compilerContext address).1 = some [addressWord] := by
                simpa [panValueFlatten] using ihAddress (.word addressWord) haddress
              have hcompiledAddressLength :
                  (compileExpHOL compilerContext address).1.length = 1 := by
                simpa using (evalCrepRuntimeExps_length_of_some target
                  (compileExpHOL compilerContext address).1 [addressWord]
                  hcompiledAddressRun).symm
              cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
              | nil => simp [hcompiledAddress] at hcompiledAddressLength
              | cons targetAddress targetAddressTail =>
                  cases targetAddressTail with
                  | nil =>
                      have hcompiledAddressSingleton :
                          (compileExpHOL compilerContext address).1 =
                            [targetAddress] := by
                        simp [hcompiledAddress]
                      have hcompiledAddressPair :
                          compileExpHOL compilerContext address =
                            ([targetAddress], .one) := by
                        apply Prod.ext
                        · exact hcompiledAddressSingleton
                        · exact hshape'
                      have htargetAddress :
                          evalCrepRuntimeExp target targetAddress = some addressWord := by
                        rw [hcompiledAddressSingleton] at hcompiledAddressRun
                        cases hvalue : evalCrepRuntimeExp target targetAddress with
                        | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
                        | some word =>
                            have hword : word = addressWord := by
                              simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                            simp [hword]
                      have hcompiledLoad :
                          (compileExpHOL compilerContext (.loadByte address)).1 =
                            [.loadByte targetAddress] := by
                        simp only [compileExpHOL, hcompiledAddressPair]
                      have htargetLoad :
                          evalCrepRuntimeExp target (.loadByte targetAddress) =
                            evalCrepRuntimeExp target (.loadByte (.const addressWord)) := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      have hsourceTarget := evalPanSemStateExp_loadByte_const_riscvTarget
                        source target addressWord hstate
                      have hsourceTarget' :
                          evalPanSemStateExp source
                            (.loadByte (.const addressWord)) =
                            (evalCrepRuntimeExp target
                              (.loadByte (.const addressWord))).map PanValue.word := by
                        simpa [hcanonical.symm] using hsourceTarget
                      rw [hsourceByte, hsourceTarget'] at heval
                      cases value with
                      | word resultWord =>
                          have htarget : evalCrepRuntimeExp target
                              (.loadByte (.const addressWord)) = some resultWord := by
                            simpa using heval
                          simp [compilerContext, hcompiledLoad,
                            evalCrepRuntimeExps, htargetLoad, htarget,
                            panValueFlatten]
                      | rStruct fields => simp at heval
                      | nStruct name fields => simp at heval
                  | cons _ _ => simp [hcompiledAddress] at hcompiledAddressLength
          | rStruct fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.rStruct fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
          | nStruct name fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.nStruct name fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
  | load32SupportedAddress address supported hshape hcanonical ihAddress =>
      intro value heval
      cases haddress : evalPanSemStateExp source address with
      | none =>
          have hsourceAddress :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using haddress
          simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
      | some addressValue =>
          cases addressValue with
          | word addressWord =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word addressWord) := by
                simpa [evalPanSemStateExp] using haddress
              have hsourceConst :
                  evalPanSemStateExp source (.load32 address) =
                    evalPanSemStateExp source (.load32 (.const addressWord)) := by
                simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress]
              let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                { vars := context.vars, funcs := context.funcs,
                  eids := context.eids, vmax := context.vmax }
              have hshape' : (compileExpHOL compilerContext address).2 = .one := by
                simpa [compilerContext] using hshape
              have hcompiledAddressRun :
                  evalCrepRuntimeExps target
                    (compileExpHOL compilerContext address).1 = some [addressWord] := by
                simpa [panValueFlatten] using
                  ihAddress (.word addressWord) haddress
              have hcompiledAddressLength :
                  (compileExpHOL compilerContext address).1.length = 1 := by
                simpa using (evalCrepRuntimeExps_length_of_some target
                  (compileExpHOL compilerContext address).1 [addressWord]
                  hcompiledAddressRun).symm
              cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
              | nil => simp [hcompiledAddress] at hcompiledAddressLength
              | cons targetAddress targetAddressTail =>
                  cases targetAddressTail with
                  | nil =>
                      have hcompiledAddressSingleton :
                          (compileExpHOL compilerContext address).1 =
                            [targetAddress] := by
                        simp [hcompiledAddress]
                      have hcompiledAddressPair :
                          compileExpHOL compilerContext address =
                            ([targetAddress], .one) := by
                        apply Prod.ext
                        · exact hcompiledAddressSingleton
                        · exact hshape'
                      have htargetAddress :
                          evalCrepRuntimeExp target targetAddress =
                            some addressWord := by
                        rw [hcompiledAddressSingleton] at hcompiledAddressRun
                        cases hvalue : evalCrepRuntimeExp target targetAddress with
                        | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
                        | some word =>
                            have hword : word = addressWord := by
                              simpa [evalCrepRuntimeExps, hvalue] using
                                hcompiledAddressRun
                            simp [hword]
                      have hcompiledLoad :
                          (compileExpHOL compilerContext (.load32 address)).1 =
                            [.load32 targetAddress] := by
                        simp only [compileExpHOL, hcompiledAddressPair]
                      have htargetLoad :
                          evalCrepRuntimeExp target (.load32 targetAddress) =
                            evalCrepRuntimeExp target (.load32 (.const addressWord)) := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      have hsourceTarget := evalPanSemStateExp_load32_const_riscvTarget
                        source target addressWord hstate
                      have hsourceTarget' :
                          evalPanSemStateExp source
                            (.load32 (.const addressWord)) =
                            (evalCrepRuntimeExp target
                              (.load32 (.const addressWord))).map PanValue.word := by
                        simpa [hcanonical.symm] using hsourceTarget
                      rw [hsourceConst, hsourceTarget'] at heval
                      cases value with
                      | word resultWord =>
                          have htarget :
                              evalCrepRuntimeExp target
                                (.load32 (.const addressWord)) = some resultWord := by
                            simpa using heval
                          simp [compilerContext, hcompiledLoad,
                            evalCrepRuntimeExps, htargetLoad, htarget,
                            panValueFlatten]
                      | rStruct fields => simp at heval
                      | nStruct name fields => simp at heval
                  | cons _ _ => simp [hcompiledAddress] at hcompiledAddressLength
          | rStruct fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.rStruct fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
          | nStruct name fields =>
              have hsourceAddress :
                  evalPanValueExp source.structs source.locals source.globals
                    source.memory source.baseAddress source.topAddress
                    panSemBitVec64BytesInWord address
                    (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.nStruct name fields) := by
                simpa [evalPanSemStateExp] using haddress
              simp [evalPanSemStateExp, evalPanValueExp, hsourceAddress] at heval
  | panOpMul left right hleft hright ihLeft ihRight =>
      intro value heval
      have hevalSource : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          (.panOp .mul [left, right])
          (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some value := by
        simpa [evalPanSemStateExp] using heval
      cases hleftValue : evalPanSemStateExp source left with
      | none =>
          have hleftValue' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord left
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hleftValue
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue'] at hevalSource
      | some leftValue =>
          have hleftValue' : evalPanValueExp source.structs source.locals
              source.globals source.memory source.baseAddress source.topAddress
              panSemBitVec64BytesInWord left
              (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some leftValue := by
            simpa [evalPanSemStateExp] using hleftValue
          cases hrightValue : evalPanSemStateExp source right with
          | none =>
              have hrightValue' : evalPanValueExp source.structs source.locals
                  source.globals source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord right
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
                simpa [evalPanSemStateExp] using hrightValue
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue', hrightValue'] at hevalSource
          | some rightValue =>
              have hrightValue' : evalPanValueExp source.structs source.locals
                  source.globals source.memory source.baseAddress source.topAddress
                  panSemBitVec64BytesInWord right
                  (memoryAccess := some (panSemBitVec64MemoryAccess source)) = some rightValue := by
                simpa [evalPanSemStateExp] using hrightValue
              cases leftValue with
              | word leftWord =>
                  cases rightValue with
                  | word rightWord =>
                      have hcomputed : evalPanValueExp source.structs source.locals
                          source.globals source.memory source.baseAddress source.topAddress
                          panSemBitVec64BytesInWord (.panOp .mul [left, right])
                          (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                            some (.word (leftWord * rightWord)) := by
                        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                          hleftValue', hrightValue', evalPanOp]
                      have hvalue : value = .word (leftWord * rightWord) :=
                        Option.some.inj (hevalSource.symm.trans hcomputed)
                      subst value
                      let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
                        { vars := context.vars, funcs := context.funcs,
                          eids := context.eids, vmax := context.vmax }
                      have hleftRun : evalCrepRuntimeExps target
                          (compileExpHOL compilerContext left).1 = some [leftWord] := by
                        simpa [panValueFlatten] using
                          ihLeft (.word leftWord) hleftValue
                      have hrightRun : evalCrepRuntimeExps target
                          (compileExpHOL compilerContext right).1 = some [rightWord] := by
                        simpa [panValueFlatten] using
                          ihRight (.word rightWord) hrightValue
                      have hleftLength : (compileExpHOL compilerContext left).1.length = 1 := by
                        simpa using (evalCrepRuntimeExps_length_of_some target
                          (compileExpHOL compilerContext left).1 [leftWord] hleftRun).symm
                      have hrightLength : (compileExpHOL compilerContext right).1.length = 1 := by
                        simpa using (evalCrepRuntimeExps_length_of_some target
                          (compileExpHOL compilerContext right).1 [rightWord] hrightRun).symm
                      cases hleftCompiled : (compileExpHOL compilerContext left).1 with
                      | nil => simp [hleftCompiled] at hleftLength
                      | cons leftExpression leftTail =>
                          cases leftTail with
                          | nil =>
                              have hleftSingleton :
                                  (compileExpHOL compilerContext left).1 = [leftExpression] := by
                                simp [hleftCompiled]
                              have hleftExpressionRun :
                                  evalCrepRuntimeExp target leftExpression = some leftWord := by
                                rw [hleftSingleton] at hleftRun
                                cases hword : evalCrepRuntimeExp target leftExpression with
                                | none => simp [evalCrepRuntimeExps, hword] at hleftRun
                                | some word =>
                                    have hwordEq : word = leftWord := by
                                      simpa [evalCrepRuntimeExps, hword] using hleftRun
                                    simp [hwordEq]
                              cases hrightCompiled : (compileExpHOL compilerContext right).1 with
                              | nil => simp [hrightCompiled] at hrightLength
                              | cons rightExpression rightTail =>
                                  cases rightTail with
                                  | nil =>
                                      have hrightSingleton :
                                          (compileExpHOL compilerContext right).1 =
                                            [rightExpression] := by
                                        simp [hrightCompiled]
                                      have hrightExpressionRun :
                                          evalCrepRuntimeExp target rightExpression =
                                            some rightWord := by
                                        rw [hrightSingleton] at hrightRun
                                        cases hword : evalCrepRuntimeExp target rightExpression with
                                        | none => simp [evalCrepRuntimeExps, hword] at hrightRun
                                        | some word =>
                                            have hwordEq : word = rightWord := by
                                              simpa [evalCrepRuntimeExps, hword] using hrightRun
                                            simp [hwordEq]
                                      have hcompiled :
                                          (compileExpHOL compilerContext
                                            (.panOp .mul [left, right])).1 =
                                            [.crepOp .mul [leftExpression, rightExpression]] := by
                                        simp [compileExpHOL,
                                          compileExpHOL.compileExpListHOL,
                                          hleftSingleton, hrightSingleton,
                                          cexpHeads, compilePanOp]
                                      simp [compilerContext, hcompiled, evalCrepRuntimeExps,
                                        evalCrepRuntimeExp, crepOpCrep, hleftExpressionRun,
                                        hrightExpressionRun, panValueFlatten]
                                  | cons _ _ => simp [hrightCompiled] at hrightLength
                          | cons _ _ => simp [hleftCompiled] at hleftLength
                  | rStruct _ =>
                      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                        hleftValue', hrightValue', evalPanOp] at hevalSource
                  | nStruct _ _ =>
                      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                        hleftValue', hrightValue', evalPanOp] at hevalSource
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue', hrightValue', evalPanOp] at hevalSource
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue', hrightValue', evalPanOp] at hevalSource

/-! Full localized-expression IH case for a one-word generic Load. It uses
the source-owned memory evaluator and `stateRel` to match production target
`Load`; larger shapes still require a recursive flattened-memory proof. -/
theorem compileExpHOL_loadOne_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source (.load .one address) =
      some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load .one address)).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load .one address)).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have haddressRel := haddressIH (.word addressWord) haddress
    hstate hcode hlocals haddressLocalized
  have haddressShape : (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.load .one address) =
                ([.load targetAddress], .one) := by
            simp [compileExpHOL, compilerContext, hcompiledAddressPair,
              loadShape, CrepBytesInWord.bytesInWord]
          have htargetLoad : evalCrepRuntimeExp target (.load targetAddress) =
              evalCrepRuntimeExp target (.load (.const addressWord)) := by
            simp [evalCrepRuntimeExp, htargetAddress]
          have hsourceAddressEval :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                  some (.word addressWord) := by
            simpa [evalPanSemStateExp] using haddress
          have hsourceLoadConst :
              evalPanSemStateExp source (.load .one address) =
                evalPanSemStateExp source (.load .one (.const addressWord)) := by
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_loadOne_const_stateRel
            source target addressWord hstate
          rw [hsourceLoadConst, hsourceTarget] at hsourceLoad
          have htargetLoadResult :
              evalCrepRuntimeExp target (.load (.const addressWord)) =
                some loaded := by
            simpa using hsourceLoad
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [compilerContext, hcompiledLoad, evalCrepRuntimeExps,
              htargetLoad, htargetLoadResult]
          · simp [compilerContext, hcompiledLoad]
          · simp [compilerContext, hcompiledLoad, panValueShape]
          · simp [compilerContext, hcompiledLoad, isWfShape]
      | cons _ _ => simp [hcompiledAddress] at haddressLength

/-! Full localized-expression IH case for a two-word flat Load. The proof
keeps the source flat-load stride and target compile_exp load_shape stride
aligned at the fixed RV64 width. Arbitrary shape lists remain open. -/
theorem compileExpHOL_loadTwo_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (address : Exp (RiscV.Word 64)) (addressWord loaded0 loaded1 : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcanonical : target = riscvCrepWordTarget target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (haddressLocalized : expGlobalVars address = [])
    (haddress : evalPanSemStateExp source address = some (.word addressWord))
    (haddressIH : ∀ addressValue,
      evalPanSemStateExp source address = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars address = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            address).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              address).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          address).2 = true)
    (hsourceLoad : evalPanSemStateExp source
      (.load (.comb [.one, .one]) address) =
        some (.rStruct [.word loaded0, .word loaded1])) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) address)).1 = some [loaded0, loaded1] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) address)).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load (.comb [.one, .one]) address)).2 ∧
      panValueShape [] (.rStruct [.word loaded0, .word loaded1]) =
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) address)).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) address)).2 = true := by
  let compilerContext : PanToCrepHOLContext (RiscV.Word 64) :=
    { vars := context.vars, funcs := context.funcs,
      eids := context.eids, vmax := context.vmax }
  have haddressRel := haddressIH (.word addressWord) haddress
    hstate hcode hlocals haddressLocalized
  have haddressShape : (compileExpHOL compilerContext address).2 = .one := by
    have h := haddressRel.2.2.1
    simpa [compilerContext, panValueShape] using h.symm
  have haddressLength : (compileExpHOL compilerContext address).1.length = 1 := by
    have h := haddressRel.2.1
    rw [haddressShape] at h
    simpa using h
  have hcompiledAddressRun :
      evalCrepRuntimeExps target (compileExpHOL compilerContext address).1 =
        some [addressWord] := by
    simpa [compilerContext, panValueFlatten] using haddressRel.1
  cases hcompiledAddress : (compileExpHOL compilerContext address).1 with
  | nil => simp [hcompiledAddress] at haddressLength
  | cons targetAddress targetAddressTail =>
      cases targetAddressTail with
      | nil =>
          have hcompiledAddressSingleton :
              (compileExpHOL compilerContext address).1 = [targetAddress] := by
            simp [hcompiledAddress]
          have hcompiledAddressPair :
              compileExpHOL compilerContext address = ([targetAddress], .one) := by
            apply Prod.ext
            · exact hcompiledAddressSingleton
            · exact haddressShape
          have htargetAddress : evalCrepRuntimeExp target targetAddress =
              some addressWord := by
            rw [hcompiledAddressSingleton] at hcompiledAddressRun
            cases hvalue : evalCrepRuntimeExp target targetAddress with
            | none => simp [evalCrepRuntimeExps, hvalue] at hcompiledAddressRun
            | some word =>
                have hword : word = addressWord := by
                  simpa [evalCrepRuntimeExps, hvalue] using hcompiledAddressRun
                simp [hword]
          have hcompiledLoad :
              compileExpHOL compilerContext (.load (.comb [.one, .one]) address) =
                ([.load targetAddress,
                  .load (.op .add [targetAddress, .const 8])], .comb [.one, .one]) := by
            simp only [compileExpHOL, compilerContext, hcompiledAddressPair,
              CrepBytesInWord.bytesInWord]
            apply Prod.ext
            · have hcount : Shape.shapeSize (.comb [.one, .one]) = 2 := by
                simp [Shape.shapeSize]
              rw [hcount]
              change loadShape (0 : RiscV.Word 64)
                (BitVec.ofNat 64 (64 / 8)) 2 targetAddress =
                [.load targetAddress,
                  .load (.op .add [targetAddress, .const 8])]
              rw [loadShape]
              rw [loadShape]
              rfl
            · rfl
          have htargetAddressNext :
              evalCrepRuntimeExp target (.op .add [targetAddress, .const 8]) =
                some (addressWord + 8) := by
            have htargetAddressCanonical :
                evalCrepRuntimeExp (riscvCrepWordTarget target) targetAddress =
                  some addressWord := by
              rw [hcanonical] at htargetAddress
              exact htargetAddress
            have hwordArgs :
                [targetAddress, .const 8].mapM
                    (evalCrepRuntimeExp (riscvCrepWordTarget target)) =
                  some [addressWord, 8] := by
              simp only [List.mapM_cons, List.mapM_nil,
                evalCrepRuntimeExp, htargetAddressCanonical]
              rfl
            have hwordResult :
                ([targetAddress, .const 8].mapM
                    (evalCrepRuntimeExp (riscvCrepWordTarget target))).bind
                    (wordOpHOL .add) = some (addressWord + 8) := by
              rw [hwordArgs]
              simp [wordOpHOL, wordOp]
            rw [hcanonical]
            rw [evalCrepRuntimeExp_op_riscvWordTarget_wordOpHOL]
            exact hwordResult
          have hsourceAddressEval :
              evalPanValueExp source.structs source.locals source.globals
                source.memory source.baseAddress source.topAddress
                panSemBitVec64BytesInWord address
                (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                  some (.word addressWord) := by
            simpa [evalPanSemStateExp] using haddress
          have hsourceLoadConst :
              evalPanSemStateExp source (.load (.comb [.one, .one]) address) =
                evalPanSemStateExp source
                  (.load (.comb [.one, .one]) (.const addressWord)) := by
            simp [evalPanSemStateExp, evalPanValueExp, hsourceAddressEval]
          have hsourceTarget := evalPanSemStateExp_loadTwo_const_stateRel
            source target addressWord hstate
          rw [hsourceLoadConst, hsourceTarget] at hsourceLoad
          cases hfirst : evalCrepRuntimeExp target (.load (.const addressWord)) with
          | none => simp [hfirst] at hsourceLoad
          | some first =>
              simp only [hfirst, Option.bind_some] at hsourceLoad
              cases hsecond : evalCrepRuntimeExp target
                  (.load (.const (addressWord + 8))) with
              | none =>
                  simp only [hsecond, Option.map_none] at hsourceLoad
                  cases hsourceLoad
              | some second =>
                  simp only [hsecond, Option.map_some] at hsourceLoad
                  have hstruct := Option.some.inj hsourceLoad
                  have hvalues := PanValue.rStruct.inj hstruct
                  have hfirstValue : first = loaded0 := by
                    injection hvalues with hhead htail
                    exact PanValue.word.inj hhead
                  have hsecondValue : second = loaded1 := by
                    injection hvalues with hhead htail
                    injection htail with hheadSecond hnil
                    exact PanValue.word.inj hheadSecond
                  have hcompiledFirstLoad :
                      evalCrepRuntimeExp target (.load targetAddress) =
                        some loaded0 := by
                    have hfirstLoad := hfirst
                    calc
                      evalCrepRuntimeExp target (.load targetAddress) =
                          crepRuntimeLoad target addressWord := by
                        simp [evalCrepRuntimeExp, htargetAddress]
                      _ = evalCrepRuntimeExp target (.load (.const addressWord)) := by
                        simp [evalCrepRuntimeExp]
                      _ = some first := hfirst
                      _ = some loaded0 := by rw [hfirstValue]
                  have hcompiledSecondLoad :
                      evalCrepRuntimeExp target
                        (.load (.op .add [targetAddress, .const 8])) =
                        some loaded1 := by
                    have hloadBind (expression : CrepExp (RiscV.Word 64)) :
                        evalCrepRuntimeExp target (.load expression) =
                          (evalCrepRuntimeExp target expression).bind
                            (crepRuntimeLoad target) := by
                      simp only [evalCrepRuntimeExp]
                      rfl
                    rw [hloadBind, htargetAddressNext]
                    have hsecondLoad : crepRuntimeLoad target
                        (addressWord + 8) = some second := by
                      simpa [evalCrepRuntimeExp] using hsecond
                    exact hsecondLoad.trans (congrArg some hsecondValue)
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · have htargetRun : evalCrepRuntimeExps target
                        ([.load targetAddress,
                          .load (.op .add [targetAddress, .const 8])] :
                            List (CrepExp (RiscV.Word 64))) =
                          some [loaded0, loaded1] := by
                      change evalCrepRuntimeExps target
                        ([.load targetAddress] ++
                          [.load (.op .add [targetAddress, .const 8])]) =
                        some ([loaded0] ++ [loaded1])
                      have hfirstList : evalCrepRuntimeExps target
                          [.load targetAddress] = some [loaded0] := by
                        simp [evalCrepRuntimeExps, hcompiledFirstLoad]
                      have hsecondList : evalCrepRuntimeExps target
                          [.load (.op .add [targetAddress, .const 8])] =
                            some [loaded1] := by
                        simp only [evalCrepRuntimeExps, hcompiledSecondLoad]
                        simp
                      exact evalCrepRuntimeExps_append target
                        [.load targetAddress]
                        [.load (.op .add [targetAddress, .const 8])]
                        [loaded0] [loaded1]
                        hfirstList hsecondList
                    simpa [compilerContext, hcompiledLoad] using htargetRun
                  · simp [compilerContext, hcompiledLoad, Shape.shapeSize]
                  · simp [compilerContext, hcompiledLoad, panValueShape]
                  · simp [compilerContext, hcompiledLoad, isWfShape,
                      isWfShape.isWfShapeList]
      | cons _ _ => simp [hcompiledAddress] at haddressLength

/-! Regression corollaries compose the generic flat-load expression IH with a
localized variable address. They keep the address nonconstant and verify that
the recursive address IH, source state, and exact target load path compose for
both one-word and two-word loads. These are untagged induction support. -/
theorem compileExpHOL_loadOne_localAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (addressWord loaded : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load .one (.var .local name)) = some (.word loaded)) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load .one (.var .local name))).1 = some [loaded] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load .one (.var .local name))).2 ∧
      panValueShape [] (.word loaded) = (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load .one (.var .local name))).2 = true := by
  have haddress : evalPanSemStateExp source (.var .local name) =
      some (.word addressWord) := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceLocal
  have haddressIH : ∀ addressValue,
      evalPanSemStateExp source (.var .local name) = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.var .local name)).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              (.var .local name)).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 = true := by
    intro (addressValue : PanValue (RiscV.Word 64)) hvalue hstate' hcode' hlocals' hlocalized'
    have hvalue' : addressValue = .word addressWord :=
      Option.some.inj (hvalue.symm.trans haddress)
    subst addressValue
    exact compileExpHOL_local_ofHOLIH context source target name
      (.word addressWord) hstate' hcode' hlocals' hlocalized' haddress
  exact compileExpHOL_loadOne_ofHOLIH context source target
    (.var .local name) addressWord loaded hstate hcode hlocals
    (by simp [expGlobalVars]) haddress haddressIH hsourceLoad

theorem compileExpHOL_loadTwo_localAddress_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (addressWord loaded0 loaded1 : RiscV.Word 64)
    (hstate : stateRel source target)
    (hcanonical : target = riscvCrepWordTarget target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hsourceLocal : source.locals name = some (.word addressWord))
    (hsourceLoad : evalPanSemStateExp source
      (.load (.comb [.one, .one]) (.var .local name)) =
        some (.rStruct [.word loaded0, .word loaded1])) :
    evalCrepRuntimeExps target
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) (.var .local name))).1 =
          some [loaded0, loaded1] ∧
      (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) (.var .local name))).1.length =
          Shape.shapeSize (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.load (.comb [.one, .one]) (.var .local name))).2 ∧
      panValueShape [] (.rStruct [.word loaded0, .word loaded1]) =
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.load (.comb [.one, .one]) (.var .local name))).2 ∧
      isWfShape [] (compileExpHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        (.load (.comb [.one, .one]) (.var .local name))).2 = true := by
  have haddress : evalPanSemStateExp source (.var .local name) =
      some (.word addressWord) := by
    simpa [evalPanSemStateExp, evalPanValueExp, FLOOKUP] using hsourceLocal
  have haddressIH : ∀ addressValue,
      evalPanSemStateExp source (.var .local name) = some addressValue →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars (.var .local name : Exp (RiscV.Word 64)) = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            (.var .local name)).1 = some (panValueFlatten addressValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              (.var .local name)).2 ∧
        panValueShape [] addressValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          (.var .local name)).2 = true := by
    intro (addressValue : PanValue (RiscV.Word 64)) hvalue hstate' hcode' hlocals' hlocalized'
    have hvalue' : addressValue = .word addressWord :=
      Option.some.inj (hvalue.symm.trans haddress)
    subst addressValue
    exact compileExpHOL_local_ofHOLIH context source target name
      (.word addressWord) hstate' hcode' hlocals' hlocalized' haddress
  exact compileExpHOL_loadTwo_ofHOLIH context source target
    (.var .local name) addressWord loaded0 loaded1 hstate hcanonical hcode hlocals
    (by simp [expGlobalVars]) haddress haddressIH hsourceLoad

/-! Full-IH constructor evidence includes Cmp, Shift, and the LoadByte/Load32
address cases below. The separate restricted argument support composes
Const/Local/RStruct/address/RField cases and PanOp multiplication through HOL
`compile_args`. The general compile_exp_val_rel induction, remaining Load forms
and operators, and the enclosing Call proof remain open. -/
private theorem evalPanSemStateExp_panOpMul_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (left right : Exp (RiscV.Word 64)) (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.panOp .mul [left, right]) =
      some (.word result)) :
    ∃ leftWord rightWord,
      evalPanSemStateExp source left = some (.word leftWord) ∧
      evalPanSemStateExp source right = some (.word rightWord) ∧
      result = leftWord * rightWord := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.panOp .mul [left, right])
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  cases hleft : evalPanSemStateExp source left with
  | none =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
        simpa [evalPanSemStateExp] using hleft
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleftValue,
        evalPanOp] at hsourceValue
  | some leftValue =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
          some leftValue := by
        simpa [evalPanSemStateExp] using hleft
      cases hright : evalPanSemStateExp source right with
      | none =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hright
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue, hrightValue, evalPanOp] at hsourceValue
      | some rightValue =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
              some rightValue := by
            simpa [evalPanSemStateExp] using hright
          cases leftValue with
          | word leftWord =>
              cases rightValue with
              | word rightWord =>
                  have hcomputed : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord (.panOp .mul [left, right])
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      some (.word (leftWord * rightWord)) := by
                    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftValue, hrightValue, evalPanOp]
                  have hwords : PanValue.word result =
                      PanValue.word (leftWord * rightWord) :=
                    Option.some.inj (hsourceValue.symm.trans hcomputed)
                  exact ⟨leftWord, rightWord, rfl, rfl,
                    PanValue.word.inj hwords⟩
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue, evalPanOp] at hsourceValue
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue, evalPanOp] at hsourceValue
          | rStruct _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue, evalPanOp] at hsourceValue
          | nStruct _ _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue, evalPanOp] at hsourceValue

private theorem panValues_eq_words_map_of_wordProjection
    (values : List (PanValue (RiscV.Word 64)))
    (words : List (RiscV.Word 64))
    (hvalues : values.mapM panValueWordProjection = some words) :
    values = words.map PanValue.word := by
  induction values generalizing words with
  | nil => simpa using hvalues.symm
  | cons value values ih =>
      cases value with
      | word word =>
          cases htail : values.mapM panValueWordProjection with
          | none => simp [List.mapM_cons, panValueWordProjection, htail] at hvalues
          | some tail =>
              have hwords : words = word :: tail := by
                simpa [List.mapM_cons, htail] using hvalues.symm
              subst words
              have htailValues : values = tail.map PanValue.word := ih tail htail
              simp [htailValues]
      | rStruct fields => simp [List.mapM_cons, panValueWordProjection] at hvalues
      | nStruct name fields => simp [List.mapM_cons, panValueWordProjection] at hvalues

private theorem evalPanSemStateExp_op_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (operator : BinOp) (arguments : List (Exp (RiscV.Word 64)))
    (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.op operator arguments) =
      some (.word result)) :
    ∃ words,
      evalPanSemStateExps source arguments = some (words.map PanValue.word) ∧
      wordOpHOL operator words = some result := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.op operator arguments)
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  simp only [evalPanValueExp] at hsourceValue
  cases harguments : evalPanSemStateExps source arguments with
  | none =>
      change evalPanValueExp.evalPanValueExps source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord arguments (some (panSemBitVec64MemoryAccess source)) =
        none at harguments
      rw [harguments] at hsourceValue
      simp at hsourceValue
  | some values =>
      change evalPanValueExp.evalPanValueExps source.structs source.locals
        source.globals source.memory source.baseAddress source.topAddress
        panSemBitVec64BytesInWord arguments (some (panSemBitVec64MemoryAccess source)) =
        some values at harguments
      rw [harguments] at hsourceValue
      cases hprojection : values.mapM panValueWordProjection with
      | none => simp [hprojection] at hsourceValue
      | some words =>
          have hvalues : values = words.map PanValue.word :=
            panValues_eq_words_map_of_wordProjection values words hprojection
          have hwordMap : (words.map PanValue.word).mapM panValueWordProjection =
              some words := by
            simp only [List.mapM_map]
            change words.mapM (fun word => some word) = some words
            simpa using (List.mapM_pure (m := Option) (f := id) (l := words))
          have hwordOp : (panSemBitVec64MemoryAccess source).wordOp
              operator words = wordOpHOL operator words := rfl
          simp [hvalues, hwordMap, hwordOp] at hsourceValue
          have hresultEq : wordOpHOL operator words = some result := by
            cases hword : wordOpHOL operator words with
            | none => simp [hword] at hsourceValue
            | some word =>
                have heq : word = result := by
                  have hwordValues : PanValue.word word = PanValue.word result := by
                    simpa [hword] using hsourceValue
                  exact PanValue.word.inj hwordValues
                simp [heq]
          exact ⟨words, congrArg some hvalues, hresultEq⟩

private theorem evalPanSemStateExp_op2_inv
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (operator : BinOp) (left right : Exp (RiscV.Word 64))
    (result : RiscV.Word 64)
    (hsource : evalPanSemStateExp source (.op operator [left, right]) =
      some (.word result)) :
    ∃ leftWord rightWord,
      evalPanSemStateExp source left = some (.word leftWord) ∧
      evalPanSemStateExp source right = some (.word rightWord) ∧
      wordOpHOL operator [leftWord, rightWord] = some result := by
  have hsourceValue : evalPanValueExp source.structs source.locals source.globals
      source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
      (.op operator [left, right])
      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
      some (.word result) := by
    simpa [evalPanSemStateExp] using hsource
  cases hleft : evalPanSemStateExp source left with
  | none =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
        simpa [evalPanSemStateExp] using hleft
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hleftValue] at hsourceValue
  | some leftValue =>
      have hleftValue : evalPanValueExp source.structs source.locals source.globals
          source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
          left (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
          some leftValue := by
        simpa [evalPanSemStateExp] using hleft
      cases hright : evalPanSemStateExp source right with
      | none =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) = none := by
            simpa [evalPanSemStateExp] using hright
          simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
            hleftValue, hrightValue] at hsourceValue
      | some rightValue =>
          have hrightValue : evalPanValueExp source.structs source.locals source.globals
              source.memory source.baseAddress source.topAddress panSemBitVec64BytesInWord
              right (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
              some rightValue := by
            simpa [evalPanSemStateExp] using hright
          cases leftValue with
          | word leftWord =>
              cases rightValue with
              | word rightWord =>
                  have hwordOp : (panSemBitVec64MemoryAccess source).wordOp
                      operator [leftWord, rightWord] =
                      wordOpHOL operator [leftWord, rightWord] := by
                    rfl
                  have hcomputed : evalPanValueExp source.structs source.locals
                      source.globals source.memory source.baseAddress source.topAddress
                      panSemBitVec64BytesInWord (.op operator [left, right])
                      (memoryAccess := some (panSemBitVec64MemoryAccess source)) =
                      (wordOpHOL operator [leftWord, rightWord]).map PanValue.word := by
                    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                      hleftValue, hrightValue, hwordOp]
                  rw [hcomputed] at hsourceValue
                  cases hword : wordOpHOL operator [leftWord, rightWord] with
                  | none => simp [hword] at hsourceValue
                  | some word =>
                      have hresultEq : result = word := by
                        have hvalues : PanValue.word result = PanValue.word word := by
                          simpa [hword] using hsourceValue.symm
                        exact PanValue.word.inj hvalues
                      subst result
                      exact ⟨leftWord, rightWord, by rfl,
                        by rfl, hword⟩
              | rStruct _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue] at hsourceValue
              | nStruct _ _ =>
                  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                    hleftValue, hrightValue] at hsourceValue
          | rStruct _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue] at hsourceValue
          | nStruct _ _ =>
              simp [evalPanValueExp, evalPanValueExp.evalPanValueExps,
                hleftValue, hrightValue] at hsourceValue

/-! A successful source parameter-shape match preserves `Shape.shapeSize`.
Named shapes also satisfy this because every named shape has size one; their
name equality is only the matching condition. -/
mutual
  private theorem panShapeMatches_shapeSize_eq (left right : Shape)
      (hmatch : panShapeMatches left right = true) :
      Shape.shapeSize left = Shape.shapeSize right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches] at hmatch ⊢
    | named leftName =>
        cases right <;> simp [panShapeMatches] at hmatch ⊢
    | comb leftFields =>
        cases right with
        | one => simp [panShapeMatches] at hmatch
        | named _ => simp [panShapeMatches] at hmatch
        | comb rightFields =>
            simp only [panShapeMatches] at hmatch
            rw [shapeSize_comb_eq_sum, shapeSize_comb_eq_sum]
            exact panShapeListMatches_shapeSize_eq leftFields rightFields hmatch

  private theorem panShapeListMatches_shapeSize_eq (left right : List Shape)
      (hmatch : panShapeMatches.panShapeListMatches left right = true) :
      (left.map Shape.shapeSize).sum = (right.map Shape.shapeSize).sum := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches] at hmatch ⊢
    | cons leftHead leftTail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches] at hmatch
        | cons rightHead rightTail =>
            simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true] at hmatch
            rcases hmatch with ⟨hhead, htail⟩
            simp only [List.map_cons, List.sum_cons]
            rw [panShapeMatches_shapeSize_eq leftHead rightHead hhead,
              panShapeListMatches_shapeSize_eq leftTail rightTail htail]
end

/-! The successful `lookup_code` parameter check fixes each formal shape to its
source `shape_of` argument shape. This Flapjack projection exposes the
map-level fact needed by the indexed HOL `LIST_REL` locals bridge. -/
private theorem panSemCodeArgumentsMatch_shapeMapEq (structs : StructContext)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (hmatch : panSemCodeArgumentsMatch structs parameters values = true) :
    parameters.map Prod.snd = values.map (panValueShape structs) := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          rcases hmatch with ⟨hshape, htail⟩
          simp only [List.map_cons]
          rw [panShapeMatches_eq (panValueShape structs value) parameter.2 hshape,
            ih values htail]

private theorem panSemCodeArgumentsMatch_length (structs : StructContext)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (hmatch : panSemCodeArgumentsMatch structs parameters values = true) :
    parameters.length = values.length := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          exact congrArg Nat.succ (ih values hmatch.2)

/-! Successful source parameter matching plus well-formed source values fixes
the flattened argument length used by target code lookup. -/
private theorem panSemCodeArgumentsMatch_flattenLength
    (parameters : List (String × Shape)) (values : List (PanValue (RiscV.Word 64)))
    (hmatch : panSemCodeArgumentsMatch [] parameters values = true)
    (hwf : panValueIsWfValues ([] : StructContext) values = true) :
    Shape.shapeSize (.comb (parameters.map Prod.snd)) =
      (values.flatMap panValueFlatten).length := by
  induction parameters generalizing values with
  | nil => cases values <;> simp [panSemCodeArgumentsMatch, Shape.shapeSize] at hmatch ⊢
  | cons parameter parameters ih =>
      cases values with
      | nil => simp [panSemCodeArgumentsMatch] at hmatch
      | cons value values =>
          simp only [panSemCodeArgumentsMatch, Bool.and_eq_true] at hmatch
          rcases hmatch with ⟨hshape, htailMatch⟩
          simp only [panValueIsWfValues, Bool.and_eq_true] at hwf
          have hshapeSize := panShapeMatches_shapeSize_eq
            (panValueShape [] value) parameter.2 hshape
          have hwfShape : isWfShape [] (panValueShape [] value) = true :=
            panValueIsWf_isWfShape_panValueShape [] value hwf.1
          have hflatLength := panValueFlatten_length_eq_shapeSize value hwfShape
          have htail := ih values htailMatch hwf.2
          calc
            Shape.shapeSize (.comb ((parameter :: parameters).map Prod.snd)) =
                Shape.shapeSize parameter.2 +
                  Shape.shapeSize (.comb (parameters.map Prod.snd)) := by
              simp only [shapeSize_comb_eq_sum, List.map_cons, List.sum_cons]
            _ = (panValueFlatten value).length +
                  (values.flatMap panValueFlatten).length := by
              rw [← hshapeSize, ← hflatLength, htail]
            _ = ((value :: values).flatMap panValueFlatten).length := by
              simp [List.flatMap, List.length_append]

private theorem panSemCodeArgumentsMatch_of_lookup_success [BEq String]
    (structs : StructContext) (code : PanSemCodeMap α) (function : String)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (body : Prog α) (returnShape : Shape)
    (locals : String → Option (PanValue α))
    (hentry : panSemCodeLookup code function = some (parameters, body, returnShape))
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, locals)) :
    panSemCodeArgumentsMatch structs parameters values = true := by
  cases hargs : panSemCodeArgumentsMatch structs parameters values with
  | true => rfl
  | false => simp [lookupPanSemCodeCall, hentry, hargs] at hlookup

/-! Successful state-owned `lookupPanSemCodeCall` exposes the same parameter
map returned by the source evaluator's callee-entry setup. This projection
connects its body lookup to the binder-to-`slc` locals relation in PanToCrep. -/
private theorem bindPanValueParameters_of_lookup_success [BEq String]
    (structs : StructContext) (code : PanSemCodeMap α) (function : String)
    (parameters : List (String × Shape)) (values : List (PanValue α))
    (body : Prog α) (returnShape : Shape)
    (locals : String → Option (PanValue α))
    (hentry : panSemCodeLookup code function = some (parameters, body, returnShape))
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, locals)) :
    (parameters.map Prod.fst).Nodup ∧
      bindPanValueParameters (parameters.map Prod.fst) values = some locals := by
  have hmatch := panSemCodeArgumentsMatch_of_lookup_success structs code function
    parameters values body returnShape locals hentry hlookup
  have hnames : (parameters.map Prod.fst).Nodup := by
    by_cases hnames : (parameters.map Prod.fst).Nodup
    · exact hnames
    · simp [lookupPanSemCodeCall, hentry, hnames] at hlookup
  have hbind : bindPanValueParameters (parameters.map Prod.fst) values = some locals := by
    have hlookup' := hlookup
    simp [lookupPanSemCodeCall, hentry, hnames, hmatch] at hlookup'
    cases hbind : bindPanValueParameters (parameters.map Prod.fst) values with
    | none => simp [hbind] at hlookup'
    | some bound =>
        simp [hbind] at hlookup'
        cases hlookup'
        rfl
  exact ⟨hnames, hbind⟩

/-! Derive the production Crep callee lookup and parameter locals from the
state-owned source/target code maps. The argument words are arbitrary; their
length must match the flattened source parameter shapes. The HOL compiled
argument evaluation bridge that supplies those words remains a separate
obligation in the general Call case. -/
private theorem eraseDups_eq_self_of_nodup (values : List Nat)
    (hnodup : values.Nodup) : values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rw [List.eraseDups_cons]
      have hfilter : tail.filter (fun value => !(value == head)) = tail := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        have hne : value ≠ head := by
          intro heq
          subst value
          exact hhead hvalue
        simp [hne]
      rw [hfilter, ih htail]

private theorem crepRuntimeLocals_zip_eq_fupdateList
    (slots : List Nat) (words : List (RiscV.Word 64))
    (locals : Nat → Option (PanWordLab (RiscV.Word 64))) :
    (slots.zip words).foldl
        (fun locals (slot, word) => updateCrepRuntimeLocal locals slot (.word word))
        locals =
      FUPDATE_LIST locals (slots.zip (words.map PanWordLab.word)) := by
  induction slots generalizing words locals with
  | nil => cases words <;> simp [FUPDATE_LIST]
  | cons slot slots ih =>
      cases words with
      | nil => rfl
      | cons word words =>
          simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons, FUPDATE_LIST]
          have hfirst : updateCrepRuntimeLocal locals slot (.word word) =
              FUPDATE locals (slot, .word word) := by
            funext key
            by_cases hkey : key = slot
            · subst key
              simp [updateCrepRuntimeLocal, FUPDATE]
            · have hslotKey : (slot == key) = false := by
                exact beq_eq_false_iff_ne.mpr (Ne.symm hkey)
              simp [updateCrepRuntimeLocal, FUPDATE, hslotKey]
          rw [hfirst, ih]
          rfl

theorem lookupCrepRuntimeCode_ofCodeRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (argumentWords : List (RiscV.Word 64))
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) = argumentWords.length) :
    ∃ targetLocals : Nat → Option (PanWordLab (RiscV.Word 64)),
      lookupCrepRuntimeCode function argumentWords target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids (parameters.map Prod.fst)
            (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) ∧
      targetLocals = ((List.range
        (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip argumentWords).foldl
          (fun locals (name, value) =>
            updateCrepRuntimeLocal locals name (.word value))
            (fun _ => none : Nat → Option (PanWordLab (RiscV.Word 64))) := by
  let names := List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup source.code) function =
      some (parameters, sourceBody, returnShape) := by
    change panSemCodeLookup source.code function = _
    exact hentry
  rcases codeRelImp context (panSemCodeAsLookup source.code) target.code hcode
      function parameters sourceBody returnShape hsourceLookup with
    ⟨_, _, htargetEntry⟩
  have hnamesLength : names.length = argumentWords.length := by
    simpa [names] using hargumentLength
  have hnamesNodup : names.Nodup := by simp [names, List.nodup_range]
  refine ⟨(names.zip argumentWords).foldl
      (fun locals (name, value) =>
        updateCrepRuntimeLocal locals name (.word value))
      (fun _ => none : Nat → Option (PanWordLab (RiscV.Word 64))), ?_, rfl⟩
  simp only [lookupCrepRuntimeCode, lookupCrepHolCode, htargetEntry]
  have hvalid : names.length = (argumentWords.map PanWordLab.word).length ∧ names.Nodup := by
    simp [names, hnamesLength, hnamesNodup]
  rw [if_pos hvalid]
  apply congrArg some
  apply Prod.ext
  · rfl
  ·
    change FUPDATE_LIST (fun _ : Nat => none)
        (names.zip (argumentWords.map PanWordLab.word)) = _
    exact (crepRuntimeLocals_zip_eq_fupdateList names argumentWords
      (fun _ => none)).symm

/-! Relate arbitrary-list target `exp_hdl` writes to the source handler-local
assignment. This supplies the handler-body `locals_rel` premise for any
flattened payload whose words are present in the target return-global area;
the full state/code/excp relation and enclosing Call IH composition remain
separate Flapjack-only obligations. -/
theorem crepRuntimeExpHdlFiniteMapWords_localsRel
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (state : CrepRuntimeState (RiscV.Word 64) σ)
    (sourceLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (name : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (values : List (RiscV.Word 64))
    (hlocals : localsRel context sourceLocals state.locals)
    (hsource : FLOOKUP sourceLocals name = some old)
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars name = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current, state.locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel state 0 slots values) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2) state
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      localsRel context (FUPDATE sourceLocals (name, payload)) targetPost.locals := by
  obtain ⟨payloadSlots, hcontextPayload, _hslotsDistinct, hlocalsPayload⟩ :=
    localsRelUpdateExistingValue context sourceLocals state.locals name old payload
      hlocals hsource hshape
  have hpayloadSlots : payloadSlots = slots := by
    have hcontextTarget : FLOOKUP context.vars name =
        some (panValueShape [] payload, slots) := by
      rw [hpayloadShape]
      exact hvariable
    have hpairs : (panValueShape [] payload, payloadSlots) =
        (panValueShape [] payload, slots) := by
      exact Option.some.inj (hcontextPayload.symm.trans hcontextTarget)
    exact congrArg Prod.snd hpairs
  let targetPost := { state with locals :=
    ((slots.zip values).foldl
      (fun locals (entry : Nat × RiscV.Word 64) =>
        updateCrepRuntimeLocal locals entry.1 (.word entry.2))
      state.locals) }
  have hrun := crepRuntimeExpHdlFiniteMapWords handler primitive state context.vars
    name shape slots values hvariable hslots hglobals
  have hrunPost : evalCrepRuntimeProg handler primitive (slots.length + 2) state
      (expHdlFiniteMap context.vars name) = some (.normal, targetPost) := by
    simpa [targetPost] using hrun
  have hlocalsMap : targetPost.locals =
      FUPDATE_LIST state.locals (slots.zip (values.map PanWordLab.word)) := by
    simpa [targetPost] using crepRuntimeLocals_zip_eq_fupdateList
      slots values state.locals
  have hupdates :
      FUPDATE_LIST state.locals (slots.zip (values.map PanWordLab.word)) =
        FUPDATE_LIST state.locals
          (payloadSlots.zip ((panValueFlatten payload).map PanWordLab.word)) := by
    rw [← hpayloadSlots, hflatten]
  refine ⟨targetPost, hrunPost, ?_⟩
  rw [hlocalsMap, hupdates]
  exact hlocalsPayload

/-! Arbitrary-payload actual-state handler-entry boundary. It runs the target
`exp_hdl` against the caller/callee states and supplies all four relations
required by the handler-body IH. The recursive callee and handler IHs and the
enclosing HOL `Call_Ret_Exception` induction case remain open. -/
theorem crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceCallerLocals : FiniteMap String (PanValue (RiscV.Word 64)))
    (targetCaller targetCallee : CrepRuntimeState (RiscV.Word 64) σ)
    (name : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (values : List (RiscV.Word 64))
    (hstate : stateRel sourceAfterCallee targetCallee)
    (hcode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      targetCallee.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context sourceCallerLocals targetCaller.locals)
    (hsource : FLOOKUP sourceCallerLocals name = some old)
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars name = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current,
      (crepRuntimeCallerState targetCaller targetCallee).locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState targetCaller targetCallee) 0 slots values) :
    ∃ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (crepRuntimeCallerState targetCaller targetCallee)
        (expHdlFiniteMap context.vars name) = some (.normal, targetPost) ∧
      stateRel
        { sourceAfterCallee with locals := updatePanValueMap sourceCallerLocals name payload }
        targetPost ∧
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code ∧
      excpRel context.eids sourceAfterCallee.exceptionShapes ∧
      localsRel context
        (updatePanValueMap sourceCallerLocals name payload) targetPost.locals := by
  let targetHandlerStart := crepRuntimeCallerState targetCaller targetCallee
  obtain ⟨targetPost, hrun, hlocalsPost⟩ :=
    crepRuntimeExpHdlFiniteMapWords_localsRel context handler primitive
      targetHandlerStart sourceCallerLocals name shape slots old payload values
      hlocals hsource hshape hvariable hpayloadShape hflatten hslots hglobals
  have hrunExact := crepRuntimeExpHdlFiniteMapWords handler primitive
    targetHandlerStart context.vars name shape slots values hvariable hslots hglobals
  have hpostPair := Option.some.inj (hrun.symm.trans hrunExact)
  have hpost : targetPost =
      { targetHandlerStart with locals := ((slots.zip values).foldl
        (fun locals (entry : Nat × RiscV.Word 64) =>
          updateCrepRuntimeLocal locals entry.1 (.word entry.2))
        targetHandlerStart.locals) } := congrArg Prod.snd hpostPair
  have hsourceUpdate : FUPDATE sourceCallerLocals (name, payload) =
      updatePanValueMap sourceCallerLocals name payload := by
    funext key
    by_cases hkey : name = key
    · subst key
      simp [FUPDATE, updatePanValueMap]
    · have hforward : (name == key) = false := beq_eq_false_iff_ne.mpr hkey
      have hbackward : (key == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm hkey)
      simp [FUPDATE, updatePanValueMap, hforward, hbackward]
  refine ⟨targetPost, hrun, ?_, ?_, hexcp, ?_⟩
  · rw [hpost]
    simpa [stateRel, targetHandlerStart, crepRuntimeCallerState] using hstate
  · rw [hpost]
    simpa [targetHandlerStart, crepRuntimeCallerState] using hcode
  · rw [← hsourceUpdate]
    exact hlocalsPost

/-! Compose a full HOL-shaped expression IH with the real source/target code
maps at Call argument lookup. The flattened target words are obtained by the
`compile_args` induction above, then `code_rel` supplies production
`lookupCrepRuntimeCode`; the remaining Call body IHs are still separate. -/
theorem lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (target : CrepRuntimeState (RiscV.Word 64) σ)
    (function : String)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (values : List (PanValue (RiscV.Word 64)))
    (hstate : stateRel source target)
    (hcode : codeRel context (panSemCodeAsLookup source.code) target.code)
    (hlocals : localsRel context source.locals target.locals)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsource : evalPanSemStateExps source expressions = some values)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (values.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ value,
      evalPanSemStateExp source expression = some value →
      stateRel source target →
      codeRel context (panSemCodeAsLookup source.code) target.code →
      localsRel context source.locals target.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps target
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten value) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] value = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true) :
    ∃ targetLocals : Nat → Option (PanWordLab (RiscV.Word 64)),
      evalCrepRuntimeExps target
        (compileArgsHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expressions) = some (values.flatMap panValueFlatten) ∧
      lookupCrepRuntimeCode function (values.flatMap panValueFlatten) target.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) ∧
      targetLocals = tlcWordLab
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
  have harguments := compileArgsHOL_eval_flatten_of_compileExpRel context source
    target expressions values hstate hcode hlocals hlocalized hsource heach
  obtain ⟨targetLocals, hlookup, htargetFold⟩ :=
    lookupCrepRuntimeCode_ofCodeRel context source target function parameters
      sourceBody returnShape (values.flatMap panValueFlatten) hcode hentry
      hargumentLength
  have htargetMap : targetLocals = tlcWordLab
      (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := by
    calc
      targetLocals = ((List.range
          (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
          (values.flatMap panValueFlatten)).foldl
            (fun locals (slot, word) => updateCrepRuntimeLocal locals slot (.word word))
            (FEMPTY : Nat → Option (PanWordLab (RiscV.Word 64))) := htargetFold
      _ = FUPDATE_LIST FEMPTY
          ((List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))).zip
            ((values.flatMap panValueFlatten).map PanWordLab.word)) :=
        crepRuntimeLocals_zip_eq_fupdateList
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))
          (values.flatMap panValueFlatten) FEMPTY
      _ = tlcWordLab
          (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))) values := rfl
  have hlookupExact :
      lookupCrepRuntimeCode function (values.flatMap panValueFlatten) target.code =
        some (compileProgRiscV
          (PanToCrepProofContext.toHOLContext (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd))))))
          sourceBody, targetLocals) := by
    simpa [compileCodeRelProg_eq_compileProgRiscV] using hlookup
  exact ⟨targetLocals, harguments, hlookupExact, htargetMap⟩

/-! Full-expression-IH target Call dispatcher with arbitrary handler payload
length. It derives compiled arguments and the state-owned target callee lookup,
then composes the actual finite-map `exp_hdl` run and all four handler-entry
relations with the handler-body IH. This remains untagged induction support;
the enclosing HOL Call case remains open. -/
private theorem evalCrepRuntimeCall_catchesRaisedHandlerBody_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (shape : Shape) (slots : List Nat)
    (old payload : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (values : List (RiscV.Word 64))
    (handlerBody : CrepProg (RiscV.Word 64))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (hinitialState : stateRel source caller)
    (hcallCode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hcalleeState : stateRel sourceAfterCallee calleeState)
    (hcalleeCode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      calleeState.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hsource : FLOOKUP source.locals handlerVariable = some old)
    (hshape : panValueShape [] old = panValueShape [] payload)
    (hvariable : FLOOKUP context.vars handlerVariable = some (shape, slots))
    (hpayloadShape : panValueShape [] payload = shape)
    (hflatten : panValueFlatten payload = values)
    (hslots : ∀ slot, slot ∈ slots → ∃ current,
      (crepRuntimeCallerState caller calleeState).locals slot = some current)
    (hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState caller calleeState) 0 slots values)
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    (hcalleeIH : ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      evalCrepRuntimeProg handler primitive (values.length + 3)
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hhandlerIH : ∀ targetPost,
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, targetPost) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable payload }
        targetPost →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable payload) targetPost.locals →
      evalCrepRuntimeProg handler primitive (slots.length + 2)
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive (slots.length + 4) caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  have hslotsLength := crepRuntimeGlobalWordsRel_length
    (crepRuntimeCallerState caller calleeState) 0 slots values hglobals
  obtain ⟨targetPost, hpayload, hpayloadState, hpayloadCode,
      hpayloadExcp, hpayloadLocals⟩ :=
    crepRuntimeExpHdlFiniteMapWords_handlerPrestateRelations context handler primitive
      sourceAfterCallee source.locals caller calleeState handlerVariable shape slots
      old payload values hcalleeState hcalleeCode hexcp hlocals hsource hshape
      hvariable hpayloadShape hflatten hslots hglobals
  have hhandlerBody := hhandlerIH targetPost hpayload hpayloadState hpayloadCode
    hpayloadExcp hpayloadLocals
  obtain ⟨targetLocals, harguments, hlookup, _htargetMap⟩ :=
    lookupCrepRuntimeCode_ofCodeRel_compiledArgsOfHOLIH context source caller
      function parameters sourceBody returnShape expressions arguments hinitialState
      hcallCode hlocals hlocalized hsourceArgs hentry hargumentLength heach
  let handlerStart := crepRuntimeCallerState caller calleeState
  have hhandlerBody' : evalCrepRuntimeProg handler primitive (slots.length + 2)
      { targetPost with clock := min handlerStart.clock targetPost.clock }
      handlerBody = some handlerResult := by
    simpa [fixCrepRuntimeClock] using hhandlerBody
  have hpayloadStart : evalCrepRuntimeProg handler primitive (slots.length + 2)
      handlerStart (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, targetPost) := by
    simpa [handlerStart] using hpayload
  have hpayloadStart' : evalCrepRuntimeProg handler primitive (slots.length + 2)
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (expHdlFiniteMap context.vars handlerVariable) =
        some (.normal, targetPost) := by
    simpa [handlerStart, crepRuntimeCallerState] using hpayloadStart
  have hhandlerRun : evalCrepRuntimeProg handler primitive (slots.length + 3)
      { crepRuntimeCallerState caller calleeState with locals := caller.locals }
      (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody) =
        some handlerResult := by
    simp only [evalCrepRuntimeProg]
    rw [hpayloadStart']
    simp only [fixCrepRuntimeClock]
    rw [hhandlerBody']
  exact evalCrepRuntimeCall_handlesRaisedBody handler primitive (slots.length + 3)
    caller destinations caught exceptionCode
    (.seq (expHdlFiniteMap context.vars handlerVariable) handlerBody)
    (compileCodeRelProg
      (ctxtFc context.funcs context.eids
        (parameters.map Prod.fst) (parameters.map Prod.snd)
        (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
      sourceBody)
    function
    (compileArgsHOL
      { vars := context.vars, funcs := context.funcs,
        eids := context.eids, vmax := context.vmax }
      expressions)
    (arguments.flatMap panValueFlatten) targetLocals calleeState handlerResult
    harguments hlookup hinfoValid hclock hmatch
    (by simpa [hslotsLength] using hcalleeIH targetLocals hlookup)
    hhandlerRun

/-! Two-word-payload specialization of the arbitrary-length target dispatcher.
This keeps the existing concrete Call slice while allowing its actual runtime
composition to exercise the general `exp_hdl`/locals relation above. -/
private theorem evalCrepRuntimeCall_catchesRaisedTwoWordsHandlerBody_ofHOLIH
    (context : PanToCrepProofContext (RiscV.Word 64))
    (handler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (primitive : CrepPrimitiveHandler (RiscV.Word 64))
    (source : PanSemState (RiscV.Word 64) (FfiState σ))
    (sourceAfterCallee : PanSemState (RiscV.Word 64) (FfiState σ))
    (caller : CrepRuntimeState (RiscV.Word 64) σ)
    (function handlerVariable : String) (slot0 slot1 : Nat)
    (old : PanValue (RiscV.Word 64))
    (destinations : List Nat) (caught exceptionCode value0 value1 : RiscV.Word 64)
    (parameters : List (String × Shape))
    (sourceBody : Prog (RiscV.Word 64)) (returnShape : Shape)
    (expressions : List (Exp (RiscV.Word 64)))
    (arguments : List (PanValue (RiscV.Word 64)))
    (handlerBody : CrepProg (RiscV.Word 64))
    (calleeState : CrepRuntimeState (RiscV.Word 64) σ)
    (handlerResult : CrepRuntimeStep (RiscV.Word 64) σ FfiFinalEvent)
    (hinitialState : stateRel source caller)
    (hcallCode : codeRel context (panSemCodeAsLookup source.code) caller.code)
    (hcalleeState : stateRel sourceAfterCallee calleeState)
    (hcalleeCode : codeRel context (panSemCodeAsLookup sourceAfterCallee.code)
      calleeState.code)
    (hexcp : excpRel context.eids sourceAfterCallee.exceptionShapes)
    (hlocals : localsRel context source.locals caller.locals)
    (hsource : FLOOKUP source.locals handlerVariable = some old)
    (hshape : panValueShape [] old = .comb [.one, .one])
    (hvariable : FLOOKUP context.vars handlerVariable =
      some (.comb [.one, .one], [slot0, slot1]))
    (hslot0 : ∃ current, caller.locals slot0 = some current)
    (hslot1 : ∃ current, caller.locals slot1 = some current)
    (hglobal0 : calleeState.globals (0 : BitVec 5) = some (.word value0))
    (hglobal1 : calleeState.globals (1 : BitVec 5) = some (.word value1))
    (hlocalized : ∀ expression, expression ∈ expressions →
      expGlobalVars expression = [])
    (hsourceArgs : evalPanSemStateExps source expressions = some arguments)
    (hentry : panSemCodeLookup source.code function =
      some (parameters, sourceBody, returnShape))
    (hargumentLength :
      Shape.shapeSize (.comb (parameters.map Prod.snd)) =
        (arguments.flatMap panValueFlatten).length)
    (heach : ∀ expression, expression ∈ expressions → ∀ expressionValue,
      evalPanSemStateExp source expression = some expressionValue →
      stateRel source caller →
      codeRel context (panSemCodeAsLookup source.code) caller.code →
      localsRel context source.locals caller.locals →
      expGlobalVars expression = [] →
      evalCrepRuntimeExps caller
          (compileExpHOL
            { vars := context.vars, funcs := context.funcs,
              eids := context.eids, vmax := context.vmax }
            expression).1 = some (panValueFlatten expressionValue) ∧
        (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).1.length =
            Shape.shapeSize (compileExpHOL
              { vars := context.vars, funcs := context.funcs,
                eids := context.eids, vmax := context.vmax }
              expression).2 ∧
        panValueShape [] expressionValue = (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 ∧
        isWfShape [] (compileExpHOL
          { vars := context.vars, funcs := context.funcs,
            eids := context.eids, vmax := context.vmax }
          expression).2 = true)
    (hinfoValid : crepRuntimeCallInfoValid
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) = true)
    (hclock : caller.clock ≠ 0)
    (hmatch : (caught == exceptionCode) = true)
    (hcalleeIH : ∀ targetLocals,
      lookupCrepRuntimeCode function (arguments.flatMap panValueFlatten) caller.code =
        some (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody, targetLocals) →
      evalCrepRuntimeProg handler primitive 5
        (decCrepClock { caller with locals := targetLocals })
        (compileCodeRelProg
          (ctxtFc context.funcs context.eids
            (parameters.map Prod.fst) (parameters.map Prod.snd)
            (List.range (Shape.shapeSize (.comb (parameters.map Prod.snd)))))
          sourceBody) = some (.raised exceptionCode, calleeState))
    (hhandlerIH : ∀ targetPost,
      evalCrepRuntimeProg handler primitive 4
        (crepRuntimeCallerState caller calleeState)
        (expHdlFiniteMap context.vars handlerVariable) = some (.normal, targetPost) →
      stateRel
        { sourceAfterCallee with
          locals := updatePanValueMap source.locals handlerVariable
            (.rStruct [.word value0, .word value1]) }
        targetPost →
      codeRel context (panSemCodeAsLookup sourceAfterCallee.code) targetPost.code →
      excpRel context.eids sourceAfterCallee.exceptionShapes →
      localsRel context
        (updatePanValueMap source.locals handlerVariable
          (.rStruct [.word value0, .word value1])) targetPost.locals →
      evalCrepRuntimeProg handler primitive 4
        (fixCrepRuntimeClock (ε := FfiFinalEvent)
          (crepRuntimeCallerState caller calleeState) (.normal, targetPost)).2
        handlerBody = some handlerResult) :
    evalCrepRuntimeCall handler primitive 6 caller
      (some (destinations, some (caught,
        .seq (expHdlFiniteMap context.vars handlerVariable) handlerBody))) function
      (compileArgsHOL
        { vars := context.vars, funcs := context.funcs,
          eids := context.eids, vmax := context.vmax }
        expressions) = some handlerResult := by
  let payload : PanValue (RiscV.Word 64) :=
    .rStruct [.word value0, .word value1]
  have hpayloadShape : panValueShape [] payload = .comb [.one, .one] := by
    simp [payload, panValueShape]
  have hflatten : panValueFlatten payload = [value0, value1] := by
    simp [payload, panValueFlatten, panValueFlattenValues]
  have hslots : ∀ slot, slot ∈ [slot0, slot1] →
      ∃ current, (crepRuntimeCallerState caller calleeState).locals slot = some current := by
    intro slot hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · cases hmem
      simpa [crepRuntimeCallerState] using hslot0
    · rcases hmem with hmem | hmem
      · cases hmem
        simpa [crepRuntimeCallerState] using hslot1
      · simp at hmem
  have hglobals : crepRuntimeGlobalWordsRel
      (crepRuntimeCallerState caller calleeState) 0 [slot0, slot1]
      [value0, value1] := by
    constructor
    · have hmap := evalCrepRuntimeExp_loadGlob_wordLab
        (crepRuntimeCallerState caller calleeState) (0 : BitVec 5)
      rw [show (crepRuntimeCallerState caller calleeState).globals 0 =
          some (.word value0) by simpa [crepRuntimeCallerState] using hglobal0] at hmap
      simpa using hmap
    · constructor
      · have hmap := evalCrepRuntimeExp_loadGlob_wordLab
          (crepRuntimeCallerState caller calleeState) (1 : BitVec 5)
        rw [show (crepRuntimeCallerState caller calleeState).globals 1 =
            some (.word value1) by simpa [crepRuntimeCallerState] using hglobal1] at hmap
        simpa using hmap
      · trivial
  exact evalCrepRuntimeCall_catchesRaisedHandlerBody_ofHOLIH
    context handler primitive source sourceAfterCallee caller function handlerVariable
    (.comb [.one, .one]) [slot0, slot1] old payload destinations caught exceptionCode
    parameters sourceBody returnShape expressions arguments [value0, value1]
    handlerBody calleeState handlerResult hinitialState hcallCode hcalleeState
    hcalleeCode hexcp hlocals hsource (by
      simpa [payload, panValueShape] using hshape) hvariable hpayloadShape hflatten
    hslots hglobals hlocalized hsourceArgs hentry hargumentLength heach hinfoValid
    hclock hmatch hcalleeIH
    (by simpa [payload] using hhandlerIH)

/-! Compose a state-owned source Call result with the arbitrary-payload target
exception dispatcher. The successful source callee lookup determines target
entry locals, the full expression IH determines compiled arguments, and the
recursive target callee IH supplies the related post-state and state-owned
global words used by the actual finite-map `exp_hdl`. The handler IH supplies
the final post-state relations; recursive simulations remain premises, so
this is not the full HOL `pc_compile_correct[Call_Ret_Exception]` theorem. -/
mutual
private theorem panShapeMatches_self_forSourceCall :
    ∀ shape, panShapeMatches shape shape = true
  | .one => by simp [panShapeMatches]
  | .named _ => by simp [panShapeMatches]
  | .comb shapes => by
      simp only [panShapeMatches]
      exact panShapeListMatches_self_forSourceCall shapes

private theorem panShapeListMatches_self_forSourceCall :
    ∀ shapes, panShapeMatches.panShapeListMatches shapes shapes = true
  | [] => by simp [panShapeMatches.panShapeListMatches]
  | shape :: shapes => by
      simp [panShapeMatches.panShapeListMatches,
        panShapeMatches_self_forSourceCall shape,
        panShapeListMatches_self_forSourceCall shapes]
end

private theorem list_mapM_some_lookup_of_mem {α β : Type _}
    (lookup : α → Option β) {keys : List α} {values : List β}
    (hmap : keys.mapM lookup = some values) :
    ∀ key, key ∈ keys → ∃ value, lookup key = some value := by
  induction keys generalizing values with
  | nil =>
      intro key hmem
      cases hmem
  | cons key keys ih =>
      intro candidate hmem
      simp only [List.mapM_cons] at hmap
      cases hlookup : lookup key with
      | none => simp [hlookup] at hmap
      | some value =>
          cases htail : keys.mapM lookup with
          | none => simp [hlookup, htail] at hmap
          | some tail =>
              simp [hlookup, htail] at hmap
              rcases List.mem_cons.mp hmem with hhead | htailMem
              · subst candidate
                exact ⟨value, hlookup⟩
              · exact ih htail candidate htailMem

/-! Result correspondence carried by the recursive handler IH. This records
the result component of HOL `pc_compile_correct` independently from the
post-state relations: normal/error/timeout/control/return/final-FFI results map
constructor-by-constructor, while raised results use the context's exception
code and the actual target state's `globalsLookup` cells. This is Flapjack-only
induction support and is not tagged as the enclosing HOL theorem. -/
def panToCrepClockResultRel {α σ : Type}
    (context : PanToCrepProofContext α)
    (sourceResult : PanValueFfiClockResult α σ)
    (targetResult : CrepRuntimeStep α σ FfiFinalEvent) : Prop :=
  match sourceResult.1, targetResult.1 with
  | .timeout .., .timeout => True
  | .control (.normal ..), .normal => True
  | .control (.error ..), .error => True
  | .control (.broke ..), .broke 0 => True
  | .control (.continued ..), .continued 0 => True
  | .control (.returned _ _ _ _ values), .returned words =>
      words = values.flatMap panValueFlatten
  | .control (.raised _ _ _ _ exception value), .raised code =>
      FLOOKUP context.eids exception = some code ∧
        (1 ≤ Shape.shapeSize (panSemShapeOf value) →
          globalsLookup targetResult.2 value =
            some ((panValueFlatten value).map PanWordLab.word) ∧
          Shape.shapeSize (panSemShapeOf value) ≤ 32)
  | .control (.finalFfi _ _ _ _ event), .finalFfi targetEvent =>
      targetEvent = event
  | _, _ => False

/-! Compiler-generated function return destinations are a mapped `List.range`,
so the target runtime's duplicate-destination guard follows from function
metadata itself. -/
private theorem allocatedNamesHOL_nodup
    (context : PanToCrepHOLContext α) (shape : Shape) :
    (allocatedNamesHOL context shape).Nodup := by
  unfold allocatedNamesHOL
  apply List.nodup_iff_pairwise_ne.mpr
  exact (List.nodup_iff_pairwise_ne.mp
      (List.nodup_range (n := Shape.shapeSize shape))).map
    (fun offset => context.vmax + 1 + offset)
    (by
      intro left right hne heq
      apply hne
      omega)

theorem panToCrepPcCompileCorrectCallRaiseOneWordExceptionCodeStateRiscV64
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceContext : PanValueFfiContext (RiscV.Word 64))
    (sourcePrimitive : PanPrimitiveHandler (RiscV.Word 64))
    (sourceHandler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (targetHandler : CrepRuntimeFfiHandler (RiscV.Word 64) σ FfiFinalEvent)
    (targetPrimitive : CrepPrimitiveHandler (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (function exception : String) (exceptionCode : RiscV.Word 64)
    (value : RiscV.Word 64)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code) targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (_hlocals : localsRel context sourceState.locals targetState.locals)
    (hcontextException : FLOOKUP context.eids exception = some exceptionCode)
    (hentry : panSemCodeLookup sourceState.code function =
      some ([], .raise exception (.const value), .one))
    (hexception : sourceState.exceptionShapes exception = some .one)
    (hclock : sourceState.clock ≠ 0) :
    let program : Prog (RiscV.Word 64) := .call none function []
    let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
      (.control (.raised (fun _ => none) sourceState.globals sourceState.memory
        sourceState.ffi exception (.word value)), decPanClock sourceState.clock)
    panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive sourceHandler
      sourceState program = some sourceResult ∧
    ∃ targetPost,
      evalCrepRuntimeResult targetHandler targetPrimitive 8 targetState
        (compileCodeRelProg context program) =
          some (.raised exceptionCode, targetPost) ∧
      stateRel (panSemCodeStateAfter sourceState sourceResult) targetPost ∧
      codeRel context
        (panSemCodeAsLookup (panSemCodeStateAfter sourceState sourceResult).code)
        targetPost.code ∧
      excpRel context.eids
        (panSemCodeStateAfter sourceState sourceResult).exceptionShapes ∧
      globalsLookup targetPost (.word value) = some [.word value] ∧
      decPanClock sourceState.clock = targetPost.clock := by
  let program : Prog (RiscV.Word 64) := .call none function []
  let sourceResult : PanValueFfiClockResult (RiscV.Word 64) σ :=
    (.control (.raised (fun _ => none) sourceState.globals sourceState.memory
      sourceState.ffi exception (.word value)), decPanClock sourceState.clock)
  let functionContext := ctxtFc context.funcs context.eids [] [] []
  let targetBody : CrepProg (RiscV.Word 64) :=
    .seq (.dec 1 (.const value)
      (.seq (.storeGlob (0 : BitVec 5) (.var 1)) .skip))
      (.raise exceptionCode)
  let targetPost : CrepRuntimeState (RiscV.Word 64) σ :=
    { decCrepClock targetState with
      locals := fun _ => none
      globals := updateCrepRuntimeGlobal targetState.globals
        (0 : BitVec 5) (.word value) }
  rcases hstate with ⟨hmem, hmemaddrs, hshared, hstructs, hglobals,
    hclockRel, hbe, hffi, hbase, htop⟩
  have hsource : panSemEvaluateRiscV64CodeState sourceContext sourcePrimitive
      sourceHandler sourceState program = some sourceResult := by
    simpa [program, sourceResult] using
      panSemEvaluateRiscV64CodeState_callRaiseOneWordException_ofEntry
        sourceContext sourcePrimitive sourceHandler sourceState function
        exception value hentry hexception hclock
  have hsourceLookup : FLOOKUP (panSemCodeAsLookup sourceState.code) function =
      some ([], .raise exception (.const value), .one) := by
    change panSemCodeLookup sourceState.code function = _
    exact hentry
  have hcodeEntry := codeRelImp context
    (panSemCodeAsLookup sourceState.code) targetState.code hcode function
    [] (.raise exception (.const value)) .one hsourceLookup
  rcases hcodeEntry with ⟨_hlocalized, _hfunction, htargetLookup⟩
  have hcompiledBody : compileCodeRelProg functionContext
      (.raise exception (.const value)) = targetBody := by
    simp [functionContext, targetBody, compileCodeRelProg, compileProgHOL,
      compileExpHOL, freshNamesHOL, ctxtFc, maxList, hcontextException,
      nestedDecs, crepNestedSeq, storeGlobals]
  have htargetCode : FLOOKUP targetState.code function = some ([], targetBody) := by
    simpa [Shape.shapeSize, functionContext, maxList, hcompiledBody] using htargetLookup
  have htargetCallLookup : lookupCrepRuntimeCode function [] targetState.code =
      some (targetBody, fun _ => none) := by
    simp [lookupCrepRuntimeCode, lookupCrepHolCode, htargetCode,
      FUPDATE_LIST]
    funext key
    rfl
  have htargetClock : targetState.clock ≠ 0 := by omega
  have hcompiledCall : compileCodeRelProg context program =
      .call none function [] := by
    simp [program, compileCodeRelProg, compileProgHOL, compileArgsHOL]
  have htargetRun : evalCrepRuntimeResult targetHandler targetPrimitive 8
      targetState (compileCodeRelProg context program) =
        some (.raised exceptionCode, targetPost) := by
    simp [hcompiledCall, targetPost, targetBody,
      evalCrepRuntimeResult, evalCrepRuntimeProg, evalCrepRuntimeCall,
      evalCrepRuntimeExps, evalCrepRuntimeExp, htargetCallLookup,
      htargetClock, decCrepClock, fixCrepRuntimeClock,
      restoreCrepRuntimeStep, updateCrepRuntimeLocal, clearCrepRuntimeLocals,
      crepRuntimeCallerState, crepRuntimeCallInfoValid,
      setCrepRuntimeGlobals, setCrepHolGlobals, CrepRuntimeState.toHolState,
      updateCrepRuntimeGlobal_eq_FUPDATE, panTheWord]
  refine ⟨hsource, targetPost, htargetRun, ?_, ?_, ?_, ?_, ?_⟩
  · simp [stateRel, panSemCodeStateAfter, targetPost,
      decCrepClock, decPanClock, hmem, hmemaddrs, hshared, hstructs,
      hglobals, hclockRel, hbe, hffi, hbase, htop]
  · simpa [panSemCodeStateAfter, sourceResult, targetPost, decCrepClock] using hcode
  · simpa [panSemCodeStateAfter, sourceResult] using hexcp
  · simp [globalsLookup, targetPost, panSemShapeOf,
      updateCrepRuntimeGlobal]
  · simp [targetPost, decPanClock, decCrepClock, hclockRel]
end Flapjack
