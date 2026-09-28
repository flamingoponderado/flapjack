import Flapjack.PanValueFfiClockCorrectness
import Flapjack.Test.PanValueMemoryFfi

/-! The clocked source evaluator must retain the accelerator-style memory FFI
    boundary.  This is the same memory-mutating handler used by the stepped
    evaluator, with the additional observable clock decrement at the call. -/

namespace Flapjack

def clockedMemoryFfiResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiAccelerator)

def clockedMemoryFfiResultHasWrite : Bool :=
  match clockedMemoryFfiResult with
  | some (.control (.returned _ _ memory _ [.word value]), 19) =>
      value == 8 && match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard clockedMemoryFfiResultHasWrite

def clockedMemoryFfiDecliningFinalResult := do
  let state ← evalPanValueDeclarations memoryFfiInitial.source
    [.function
      { name := "main", inline := false, exported := true, params := [],
        body := memoryFfiFinalMain, returnShape := .one }]
    (memoryAccess := some memoryFfiTestMemoryAccess)
  evalPanValueFfiClockCall memoryFfiTestContext (fun _ _ => none)
    memoryFfiTestHandler state.structs state.functions state.baseAddress
    state.topAddress state.bytesInWord 20 (fun _ => none) state.globals state.memory
    memoryFfiFinalState 20 none "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
      state.parameterShapes))
    (memoryHandler := some memoryFfiDecliningHandler)

def clockedMemoryFfiDecliningFinalIsReachable : Bool :=
  match clockedMemoryFfiDecliningFinalResult with
  | some (.control (.finalFfi locals _ memory ffi event), 19) =>
      locals "x" = none && memory 200 = none && ffi.state = () &&
        event.name = .extCall "unknown" && event.outcome = .failed
  | _ => false

#guard clockedMemoryFfiDecliningFinalIsReachable

def clockedMemoryFfiDecliningFinalProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext
    { memoryFfiInitial with ffi := memoryFfiFinalState } 20
    (fun _ _ => none) memoryFfiTestHandler 20
    [.function
      { name := "main", inline := false, exported := true, params := [],
        body := memoryFfiFinalMain, returnShape := .one }]
    "main" [] (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiDecliningHandler)

def clockedMemoryFfiDecliningFinalProgramIsReachable : Bool :=
  match clockedMemoryFfiDecliningFinalProgramResult with
  | some (.control (.finalFfi locals _ memory ffi event), 19) =>
      locals "x" = none && memory 200 = none && ffi.state = () &&
        event.name = .extCall "unknown" && event.outcome = .failed
  | _ => false

#guard clockedMemoryFfiDecliningFinalProgramIsReachable

def clockedRaisedDeclarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .raise "E" (.const 7), returnShape := .one }]

def clockedRaisedProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20 clockedRaisedDeclarations "main" []

def clockedRaisedProgramAccepted : Bool :=
  match clockedRaisedProgramResult with
  | some (.control (.raised locals globals memory ffi exception (.word value)), 19) =>
      exception == "E" && value == 7 && locals "x" = none &&
        globals "x" = none && memory 200 = none && ffi.state = ()
  | _ => false

#guard clockedRaisedProgramAccepted

def clockedTimeoutProgramResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 0
    (fun _ _ => none) memoryFfiTestHandler 20 clockedRaisedDeclarations "main" []

def clockedTimeoutProgramAccepted : Bool :=
  match clockedTimeoutProgramResult with
  | some (.timeout locals globals memory ffi, 0) =>
      locals "x" = none && globals "x" = none && memory 200 = none && ffi.state = ()
  | _ => false

#guard clockedTimeoutProgramAccepted

def clockedReturnedProgramAccepted : Bool :=
  match clockedMemoryFfiResult with
  | some (.control (.returned locals _ memory _ [.word value]), 19) =>
      locals "x" = none && value == 8 &&
        match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard clockedReturnedProgramAccepted

/-- Direct HOL `evaluate` observations are captured in
    `scripts/hol-probes/pan_clock_program_route_probe.out`. Duplicate function
    declarations use front-update order: the later helper body is selected and
    returns word 2 through the declaration-level clocked wrapper. -/
def clockedDuplicateFunctionDeclarations : List (Decl Nat) :=
  [.function
      { name := "helper", inline := false, exported := false, params := [],
        body := .return (.const 1), returnShape := .one },
   .function
      { name := "helper", inline := false, exported := false, params := [],
        body := .return (.const 2), returnShape := .one },
   .function
      { name := "main", inline := false, exported := true, params := [],
        body := .call none "helper" [], returnShape := .one }]

def clockedDuplicateFunctionRouteResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20
    clockedDuplicateFunctionDeclarations "main" []

def clockedDuplicateFunctionRouteMatchesHol : Bool :=
  match clockedDuplicateFunctionRouteResult with
  | some (.control (.returned _ _ _ _ [.word value]), _) => value == 2
  | _ => false

#guard clockedDuplicateFunctionRouteMatchesHol

/-- The original `evaluate` oracle rejects a nested callee whose returned
    value violates that function's declared return shape, even when the entry
    function's return shape would accept the value. -/
def clockedNestedCalleeReturnShapeDeclarations : List (Decl Nat) :=
  [.function
      { name := "helper", inline := false, exported := false, params := [],
        body := .return (.rStruct []), returnShape := .one },
   .function
      { name := "main", inline := false, exported := true, params := [],
        body := .call none "helper" [], returnShape := .comb [] }]

def clockedNestedCalleeReturnShapeResult :=
  evalPanValueFfiClockProgram memoryFfiTestContext memoryFfiInitial 20
    (fun _ _ => none) memoryFfiTestHandler 20
    clockedNestedCalleeReturnShapeDeclarations "main" []

def clockedNestedCalleeReturnShapeMatchesHol : Bool :=
  match clockedNestedCalleeReturnShapeResult with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false

#guard clockedNestedCalleeReturnShapeMatchesHol

end Flapjack
