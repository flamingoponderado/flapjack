module

public import Flapjack.PanValueFfiCore

@[expose] public section

/-!
# Stateful FFI semantics for structured Pancake programs

The ordinary `PanValues` evaluator has deliberately pure host handlers.  This
module adds the next CakeML-facing boundary: a stepped evaluator carrying an
explicit `FfiState`.  In particular, `shMemLoad` and `shMemStore` use the
`SharedMem` FFI operations, including their size byte, aligned address checks,
state transition, and terminal `FinalFFI` result.

The context, FFI operations, control results and simple-statement helpers
shared with the clocked semantics live in `PanValueFfiCore`.  This module holds
only the stepped evaluator and its program-level wrappers, and is slated to
leave flapjack (issue #1251).
-/

namespace Flapjack

mutual
  def evalPanValueFfiCallSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        FfiState σ → Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      (contracts : Option PanValueCallContracts := none) →
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
      (preserveReturnLocals : Bool := false) →
      Option (PanValueFfiSteppedResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, info, function, arguments, memoryAccess,
        contracts, memoryHandler, preserveReturnLocals => do
        (panValueCallArguments structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun argumentPair => do
            let (values, argumentSteps) := argumentPair
            (panValueCallTarget structs contracts function functions values).elim
              (some (.error locals globals memory ffi, argumentSteps))
              (fun callTarget => do
                let (body, calleeLocals) := callTarget
                let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
                  baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
                -- HOL returns `SOME Error` preserving the callee state's locals for
                -- NONE/Break/Continue, and empties them only in the catch-all
                -- (`SOME Error`/TimeOut) clause.
                match result with
                | .normal calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    some (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .returned retLocals calleeGlobals calleeMemory calleeFfi values =>
                    -- HOL's Call checks only `shape_of retv <> return_sh`; the
                    -- payload-size limit is enforced by the callee `Return`.
                    if panValueReturnValid structs contracts function values then
                      match info with
                      | none =>
                          let returnedLocals :=
                            if preserveReturnLocals then calleeLocals else fun _ => none
                          pure (.returned returnedLocals calleeGlobals calleeMemory calleeFfi values,
                            argumentSteps + steps)
                      | some (destination, _) => do
                          let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                            destination values
                            (structs := structs)
                          pure (.normal locals globals calleeMemory calleeFfi,
                            argumentSteps + steps)
                    else some (.error retLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .raised _ calleeGlobals calleeMemory calleeFfi exception value =>
                    if panValueExceptionValid structs contracts exception value &&
                        panValuePayloadWithinLimit structs value then
                      match info with
                      | some (_, some (caught, handlerVariable, handlerProgram)) =>
                          if caught == exception then
                            if panValueHandlerValid structs contracts locals handlerVariable value then
                              let (handlerResult, handlerSteps) ← evalPanValueFfiProgSteps context
                                primitive handler structs functions baseAddress topAddress bytesInWord fuel
                                (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                                calleeFfi handlerProgram
                                (memoryAccess := memoryAccess) (contracts := contracts)
                                (memoryHandler := memoryHandler)
                              pure (handlerResult, argumentSteps + steps + handlerSteps)
                            else none
                          else
                            pure (.raised (fun _ => none) calleeGlobals calleeMemory calleeFfi exception value,
                              argumentSteps + steps)
                      | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory calleeFfi exception value,
                          argumentSteps + steps)
                    else none
                | .broke calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    pure (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .continued calleeLocals calleeGlobals calleeMemory calleeFfi =>
                    pure (.error calleeLocals calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .error _ calleeGlobals calleeMemory calleeFfi =>
                    pure (.error (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                      argumentSteps + steps)
                | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                    pure (.finalFfi (fun _ => none) calleeGlobals calleeMemory calleeFfi event,
                      argumentSteps + steps)))
    termination_by fuel _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiProgSteps
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        FfiState σ → (program : Prog α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
      (contracts : Option PanValueCallContracts := none) →
      (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
      Option (PanValueFfiSteppedResult α σ)
    | 0, _, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, ffi, .skip, _, _, _ =>
        some (.normal locals globals memory ffi, 1)
    | fuel + 1, locals, globals, memory, ffi,
        .dec name shape value body, memoryAccess, contracts, memoryHandler =>
        (panValueDecAccepted structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape).elim
          (some (.error locals globals memory ffi, 0))
          (fun accepted => do
            let oldValue := locals name
            let (result, steps) ← evalPanValueFfiProgSteps context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel (updatePanValueMap locals name accepted.1)
              globals memory ffi body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (restorePanValueFfiLocal name oldValue result, accepted.2 + steps + 1))
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .local name value, memoryAccess, _contracts, _memoryHandler =>
        panValueAssignLocalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .assign .global name value, memoryAccess, _contracts, _memoryHandler =>
        panValueAssignGlobalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .primitive name operator arguments, memoryAccess, _contracts, _memoryHandler =>
        panValuePrimitiveResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi name operator arguments memoryAccess primitive
    | _fuel + 1, locals, globals, memory, ffi, .store address value, memoryAccess,
        _contracts, _memoryHandler =>
        panValueStoreResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .store32 address value, memoryAccess, _contracts, _memoryHandler =>
        panValueStore32Result structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .storeByte address value, memoryAccess, _contracts, _memoryHandler =>
        panValueStoreByteResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess
    | fuel + 1, locals, globals, memory, ffi, .seq first second, memoryAccess,
        contracts, memoryHandler => do
        let (firstResult, firstSteps) ← evalPanValueFfiProgSteps context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi first
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match firstResult with
        | .normal locals globals memory ffi =>
            let (secondResult, secondSteps) ← evalPanValueFfiProgSteps context primitive handler
              structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
              second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (secondResult, firstSteps + secondSteps + 1)
        | result => pure (result, firstSteps + 1)
    | _fuel + 1, locals, globals, memory, ffi,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler =>
        (panValueIteCondition structs baseAddress topAddress bytesInWord locals globals memory
          condition memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun conditionPair => do
            let (condition, conditionSteps) := conditionPair
            let (result, steps) ←
              if condition != 0 then
                evalPanValueFfiProgSteps context primitive handler structs functions
                  baseAddress topAddress bytesInWord _fuel locals globals memory ffi thenBranch
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
              else
                evalPanValueFfiProgSteps context primitive handler structs functions
                  baseAddress topAddress bytesInWord _fuel locals globals memory ffi elseBranch
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
            pure (result, conditionSteps + steps + 1))
    | fuel + 1, locals, globals, memory, ffi,
        .call info function arguments, memoryAccess, contracts, memoryHandler => do
        let (result, steps) ← evalPanValueFfiCallSteps context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        pure (result, steps + 1)
    | fuel + 1, locals, globals, memory, ffi,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (callResult, callSteps) ← evalPanValueFfiCallSteps context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
          none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (preserveReturnLocals := true)
        match callResult with
        | .returned returnedLocals globals memory ffi [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyResult, bodySteps) ← evalPanValueFfiProgSteps context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) globals memory ffi body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (restorePanValueFfiLocal name oldValue bodyResult,
                callSteps + bodySteps + 1)
            -- HOL's mismatch branch returns the callee post-state `st`.
            else some (.error returnedLocals globals memory ffi, callSteps + 1)
        | .raised _ globals memory ffi exception value =>
            pure (.raised (fun _ => none) globals memory ffi exception value,
              callSteps + 1)
        | .finalFfi _ globals memory ffi event =>
            pure (.finalFfi (fun _ => none) globals memory ffi event,
              callSteps + 1)
        | .error calleeLocals globals memory ffi =>
            pure (.error calleeLocals globals memory ffi, callSteps + 1)
        | _ => none
    | _fuel + 1, locals, globals, memory, ffi,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts, memoryHandler =>
        panValueFfiExtCallSteps context handler structs baseAddress topAddress bytesInWord
          locals globals memory ffi function configuration configurationLength array arrayLength
          memoryAccess memoryHandler
    | fuel + 1, locals, globals, memory, ffi, .while conditionExp body, memoryAccess,
        contracts, memoryHandler =>
        (panValueIteCondition structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess).elim
          (some (.error locals globals memory ffi, 0))
          (fun conditionPair => do
            let (conditionValue, conditionSteps) := conditionPair
            if conditionValue == 0 then
              pure (.normal locals globals memory ffi, conditionSteps + 1)
            else
              let (bodyResult, bodySteps) ← evalPanValueFfiProgSteps context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
                body (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              match bodyResult with
              | .normal locals globals memory ffi | .continued locals globals memory ffi =>
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps context primitive handler
                    structs functions baseAddress topAddress bytesInWord fuel locals globals memory
                    ffi (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler)
                  pure (loopResult, conditionSteps + bodySteps + loopSteps + 1)
              | .broke locals globals memory ffi =>
                  pure (.normal locals globals memory ffi, conditionSteps + bodySteps + 1)
              | result => pure (result, conditionSteps + bodySteps + 1))
    | _fuel + 1, locals, globals, memory, ffi, .break, _, _, _ =>
        pure (.broke locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .continue, _, _, _ =>
        pure (.continued locals globals memory ffi, 1)
    | _fuel + 1, locals, globals, memory, ffi, .raise exception value, memoryAccess,
        contracts, _memoryHandler =>
        panValueRaiseResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          contracts exception value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi, .return value, memoryAccess,
        _contracts, _memoryHandler =>
        panValueReturnResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler =>
        panValueShMemLoadResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size kind name address memoryAccess
    | _fuel + 1, locals, globals, memory, ffi,
        .shMemStore size address value, memoryAccess, _contracts, _memoryHandler =>
        panValueShMemStoreResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size address value memoryAccess
    | _fuel + 1, locals, globals, memory, ffi, .tick, _, _, _ |
        _fuel + 1, locals, globals, memory, ffi, .annot _ _, _, _, _ =>
        pure (.normal locals globals memory ffi, 1)
    termination_by fuel _ _ _ _ _ _ => fuel
end

/-! The accelerator-style handler is selected before the CakeML byte-array
    path.  Keeping this equation as a theorem makes the dispatch priority
    available to source-to-target proofs instead of relying on an unfolding
    detail of the mutual evaluator. -/
theorem evalPanValueFfiProgSteps_extCall_memoryHandler
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : PanValueMemoryFfiHandler α σ)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := access) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hhandler : memoryHandler function configuration configurationLength
      array arrayLength locals memory ffi =
      some (nextLocals, nextMemory, nextFfi)) :
    evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := access) (contracts := contracts)
      (memoryHandler := some memoryHandler) =
      some (.normal nextLocals globals nextMemory nextFfi, expressionSteps + 1) := by
  simp [evalPanValueFfiProgSteps, panValueFfiExtCallSteps, hvalues, hhandler]

theorem evalPanValueFfiProgSteps_extCall_returned_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (contracts : Option PanValueCallContracts)
    (access : PanValueMemoryAccess α)
    (nextLocals : VarName → Option (PanValue α))
    (nextMemory : α → Option (PanValue α)) (nextFfi : FfiState σ)
    (expressionSteps : Nat)
    (hvalues : evalPanValueExpsCounted structs locals globals memory
      baseAddress topAddress bytesInWord
      [.const configuration, .const configurationLength,
        .const array, .const arrayLength]
      (memoryAccess := some access) =
      some ([.word configuration, .word configurationLength,
        .word array, .word arrayLength], expressionSteps))
    (hresult : evalPanValueFfiProgSteps context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi
      (.extCall function (.const configuration) (.const configurationLength)
        (.const array) (.const arrayLength))
      (memoryAccess := some access) (contracts := contracts)
      (memoryHandler := none) =
      some (.normal nextLocals globals nextMemory nextFfi, expressionSteps + 1)) :
    ffi.ioEvents <+: nextFfi.ioEvents := by
  simp [evalPanValueFfiProgSteps, panValueFfiExtCallSteps, hvalues] at hresult
  cases hcall : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength with
  | none => simp [hcall] at hresult
  | some result =>
      cases result with
      | returned returnedMemory returnedFfi =>
          simp [hcall] at hresult
          rcases hresult with ⟨_, ⟨_, hffi⟩⟩
          rw [← hffi]
          exact panValueFfiExtCall_returned_ioEvents_prefix access context memory
            bytesInWord ffi function configuration configurationLength array arrayLength
            returnedMemory returnedFfi hcall
      | final event => simp [hcall] at hresult

def evalPanValueFfiProgramSteps
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiSteppedResult α σ) :=
  evalPanValueFfiProgSteps context primitive handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory ffi program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

/-! Exact source callers carry the Cake memory operations as data rather than
    relying on the optional compatibility argument below. -/
structure PanValueFfiExactProgramState (α : Type u) (σ : Type v) where
  legacy : PanValueFfiProgramState α σ
  memoryAccess : PanValueMemoryAccess α

def PanValueFfiExactProgramState.toProgramState
    (state : PanValueFfiExactProgramState α σ) : PanValueFfiProgramState α σ :=
  state.legacy

def evalPanValueFfiProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiControlResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let (result, _) ← evalPanValueFfiCallSteps context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, .returned locals globals memory ffi [value] =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory ffi [value])
      else none
  | some _, .returned _ _ _ _ _ => none
  | _, result => some result

def evalPanValueFfiExactProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiControlResult α σ) :=
  evalPanValueFfiProgram context initial.legacy primitive handler fuel declarations entry
    arguments (memoryAccess := some initial.memoryAccess)
    (memoryHandler := memoryHandler)

theorem evalPanValueFfiExactProgram_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    evalPanValueFfiExactProgram context initial primitive handler fuel declarations entry
        arguments (memoryHandler := memoryHandler) =
      evalPanValueFfiProgram context initial.legacy primitive handler fuel declarations entry
        arguments (memoryAccess := some initial.memoryAccess)
        (memoryHandler := memoryHandler) := by
  rfl

/-! Public top-level stateful-FFI evaluator retaining the source-step count.
    The underlying call evaluator already records argument and body steps; this
    wrapper keeps that count at the same declaration/entry boundary as
    `evalPanValueFfiProgram`. -/
def evalPanValueFfiProgramStepped
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiSteppedResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess)
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  let result ← evalPanValueFfiCallSteps context primitive handler state.structs
    state.functions state.baseAddress state.topAddress state.bytesInWord fuel
    (fun _ => none) state.globals state.memory initial.ffi none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  match lookupInfo entry state.returnShapes, result with
  | some shape, (.returned locals globals memory ffi [value], steps) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.returned locals globals memory ffi [value], steps)
      else none
  | some _, (.returned _ _ _ _ _, _) => none
  | _, result => some result

/-! The stepped exact entrypoint carries the Cake memory operations in its
    state, just as `evalPanValueFfiExactProgram` does.  In particular, an
    exact caller cannot accidentally select the legacy whole-cell load/store
    fallback by omitting `memoryAccess`. -/
def evalPanValueFfiExactProgramStepped
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    Option (PanValueFfiSteppedResult α σ) :=
  evalPanValueFfiProgramStepped context initial.legacy primitive handler fuel
    declarations entry arguments
    (memoryAccess := some initial.memoryAccess)

theorem evalPanValueFfiProgramStepped_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    (evalPanValueFfiProgramStepped context initial primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler)).map Prod.fst =
      evalPanValueFfiProgram context initial primitive handler fuel
      declarations entry arguments (memoryAccess := memoryAccess)
      (memoryHandler := memoryHandler) := by
  unfold evalPanValueFfiProgramStepped evalPanValueFfiProgram
  cases hstate : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) with
  | none => simp
  | some state =>
      cases hcall : evalPanValueFfiCallSteps context primitive handler state.structs
          state.functions state.baseAddress state.topAddress state.bytesInWord fuel
          (fun _ => none) state.globals state.memory initial.ffi none entry arguments
          (memoryAccess := memoryAccess)
          (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
            state.parameterShapes))
          (memoryHandler := memoryHandler) with
      | none => simp [hcall]
      | some result =>
          cases result with
          | mk control steps =>
              cases hlookup : lookupInfo entry state.returnShapes with
              | none => simp [hcall, hlookup]
              | some shape =>
                  cases control with
                  | normal locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | error locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | returned locals globals memory ffi values =>
                      cases values with
                      | nil => simp [hcall, hlookup]
                      | cons value values =>
                          cases values with
                          | nil => simp [hcall, hlookup]
                          | cons value values => simp [hcall, hlookup]
                  | raised locals globals memory ffi exception value =>
                      simp [hcall, hlookup]
                  | broke locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | continued locals globals memory ffi =>
                      simp [hcall, hlookup]
                  | finalFfi locals globals memory ffi event =>
                      simp [hcall, hlookup]

theorem evalPanValueFfiExactProgramStepped_fst
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiExactProgramState α σ)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α)) :
    (evalPanValueFfiExactProgramStepped context initial primitive handler fuel
      declarations entry arguments).map Prod.fst =
      evalPanValueFfiExactProgram context initial primitive handler fuel
        declarations entry arguments := by
  exact evalPanValueFfiProgramStepped_fst context initial.legacy primitive handler
    fuel declarations entry arguments
    (memoryAccess := some initial.memoryAccess)

end Flapjack
