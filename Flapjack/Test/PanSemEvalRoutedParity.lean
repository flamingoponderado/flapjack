import Flapjack.Pancake.Semantics.PanSem.EvalRuntimeRoute
import Flapjack.Test.PanSemStateEvalParity

/-! Exercise the selected expression route through the code-map program runner.
The changing test route distinguishes actual dispatch from a proof-only bridge. -/

namespace Flapjack.Test.PanSemEvalRoutedParity

open Flapjack Flapjack.Test.PanSemStateEvalParity

private abbrev W := RiscV.Word 64

private def observesWord (result : Option (PanValueFfiClockResult W Unit)) (expected : W) : Bool :=
  match result with
  | some (.control (.returned _ _ _ _ [.word value]), _) => value == expected
  | _ => false

private def replacingRoute : PanExprEvaluator W :=
  fun _ _ _ _ _ _ _ _ _ => some (.word 99)

/- A deliberately different route confirms that Return evaluates its expression
   through the supplied callback, rather than just proving equivalence elsewhere. -/
private def routeDispatchResult : Option (PanValueFfiClockResult W Unit) :=
  let state := sourceCodeState false true
  evalPanValueFfiClockCodeProg sourceFfiContext sourcePrimitive sourceFfiHandler
    state.structs state.code state.exceptionShapes state.baseAddress state.topAddress
    panSemBitVec64BytesInWord 3 state.locals state.globals state.memory state.ffi state.clock
    (.return (.const 1)) (memoryAccess := some (panSemBitVec64MemoryAccess state))
    (evaluator := some replacingRoute)

#guard observesWord routeDispatchResult 99

private def incrementConstantsRoute : PanExprEvaluator W :=
  fun _ locals globals _ _ _ _ _ expression =>
    match expression with
    | .const value => some (.word (value + 1))
    | .var .local name => locals name
    | .var .global name => globals name
    | _ => none

private def testSelectedRoute (state : PanSemState W (FfiState Unit)) (program : Prog W) :=
  evalPanValueFfiClockCodeProg sourceFfiContext sourcePrimitive sourceFfiHandler
    state.structs state.code state.exceptionShapes state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (panSemCodeEvaluateFuel state program) state.locals state.globals
    state.memory state.ffi state.clock program (memoryAccess := some (panSemBitVec64MemoryAccess state))
    (evaluator := some incrementConstantsRoute)

/- The selected route changes the Call argument before the callee reads it. -/
private def dispatchCallState :=
  { sourceCodeState false true with
    clock := 5
    code := [("id", ([("x", .one)], .return (.var .local "x"), .one))] }

#guard observesWord (testSelectedRoute dispatchCallState (.call none "id" [.const 1])) 2

/- The route also controls the clocked conditional, not just leaf expressions. -/
#guard observesWord
  (testSelectedRoute (sourceCodeState false true)
    (.ite (.const 0) (.return (.const 9)) (.return (.const 19)))) 10

/- The actual HOL route sees source byte order and rejects out-of-domain reads. -/
#guard observesWord
  (panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (sourceCodeState false true) (.return (.loadByte (.const 0)))) 0x88
#guard observesWord
  (panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (sourceCodeState true true) (.return (.loadByte (.const 0)))) 0x11
#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (sourceCodeState false false) (.return (.loadByte (.const 0))) with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false)

/- The concrete production entry uses the routed evaluator, retaining the
   original HOL byte-load observations for both byte orders and domain failure. -/
#guard observesWord
  (panSemEvaluateRiscV64CodeStateWithProductionPrimop sourceFfiContext sourceFfiHandler
    (sourceCodeState false true) (.return (.loadByte (.const 0)))) 0x88
#guard observesWord
  (panSemEvaluateRiscV64CodeStateWithProductionPrimop sourceFfiContext sourceFfiHandler
    (sourceCodeState true true) (.return (.loadByte (.const 0)))) 0x11
#guard (match panSemEvaluateRiscV64CodeStateWithProductionPrimop sourceFfiContext sourceFfiHandler
    (sourceCodeState false false) (.return (.loadByte (.const 0))) with
  | some (.control (.error _ _ _ _), _) => true
  | _ => false)

/- The assigned value is read again after the state update in a Seq. -/
private def routedSeqState :=
  { sourceCodeState false true with
    locals := fun name => if name == "x" then some (.word 0) else none }

#guard observesWord
  (panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    routedSeqState (.seq (.assign .local "x" (.loadByte (.const 0)))
      (.return (.var .local "x")))) 0x88

/- Arguments and the callee body both use the supplied route. -/
private def routedCallState :=
  { sourceCodeState false true with
    clock := 5
    code := [("id", ([("x", .one)], .return (.var .local "x"), .one))] }

#guard observesWord
  (panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    routedCallState (.call none "id" [.loadByte (.const 0)])) 0x88


/- Direct HOL rows from pan_sem_call_return_shape_probe.out: good and bad
   callee returns both consume one clock, and a bad shape yields Error. -/
private def routedReturnState (body : Prog W) :=
  { sourceCodeState false true with
    clock := 5
    code := [("callee", ([], body, .one))] }

#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (routedReturnState (.return (.const 7))) (.call none "callee" []) with
  | some (.control (.returned _ _ _ _ [.word value]), clock) => value == 7 && clock == 4
  | _ => false)
#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (routedReturnState (.return (.rStruct []))) (.call none "callee" []) with
  | some (.control (.error locals _ _ _), clock) => (locals "caller").isNone && clock == 4
  | _ => false)

private def initialProgram (owner : PanSemState W (FfiState Unit)) (bytes : W) :
    PanValueFfiProgramState W Unit :=
  { source :=
      { structs := []
        globals := fun _ => none
        functions := []
        returnShapes := []
        exceptions := []
        memory := owner.memory
        baseAddress := owner.baseAddress
        topAddress := owner.topAddress
        bytesInWord := bytes }
    ffi := owner.ffi }

private def programDecls : List (Decl W) :=
  [.decl .one "g" (.loadByte (.const 0)),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.var .global "g"), returnShape := .one }]

/- This exercises both the declaration initializer and the entry body through
   the state-derived HOL route. The expected bytes come from the HOL probe. -/
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (initialProgram (sourceCodeState false true) 8) (sourceCodeState false true)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []) 0x88
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (initialProgram (sourceCodeState true true) 8) (sourceCodeState true true)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []) 0x11
#guard (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (initialProgram (sourceCodeState false false) 8) (sourceCodeState false false)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []).isNone

#guard observesWord
  (panSemEvaluateRiscV64ProgramWithProductionPrimop sourceFfiContext
    (initialProgram (sourceCodeState true true) 8) (sourceCodeState true true)
    10 sourceFfiHandler 20 programDecls "main" []) 0x11

/- A deliberately changed route proves declaration evaluation itself calls the
   selected evaluator before the entry function reads the installed global. -/
private def dispatchDecls : List (Decl W) :=
  [.decl .one "g" (.const 1),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.var .global "g"), returnShape := .one }]

#guard observesWord
  (evalPanValueFfiClockProgram sourceFfiContext (initialProgram (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 dispatchDecls "main" []
    (memoryAccess := some (panSemBitVec64MemoryAccess (sourceCodeState false true)))
    (evaluator := some incrementConstantsRoute)) 2

end Flapjack.Test.PanSemEvalRoutedParity
