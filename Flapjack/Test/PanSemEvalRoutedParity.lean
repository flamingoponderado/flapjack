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

/- Check the dispatch for the same state and expression subsequently executed
   by the production entry. The second case exercises its String fallback. -/
#guard panSemExpressionUsesHOLCached
  (panSemExpressionContextCache (sourceCodeState false true).structs)
  (sourceCodeState false true) (.loadByte (.const 0))

private def fallbackRouteState :=
  { sourceCodeState false true with
    locals := fun name => if name == "Ā" then some (.word 17) else none }

#guard !(panSemExpressionUsesHOLCached (panSemExpressionContextCache fallbackRouteState.structs)
  fallbackRouteState (.var .local "Ā"))
#guard observesWord
  (panSemEvaluateRiscV64CodeStateWithProductionPrimop sourceFfiContext sourceFfiHandler
    fallbackRouteState (.return (.var .local "Ā"))) 17

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


/- The same Call and DecCall cases as pan_sem_call_return_shape_probe.out,
   specialized to the RV64 runner (the HOL probe uses 8-bit words). The caller
   starts with a binding, so the post-error lookup distinguishes cleared locals. -/
private def routedReturnState (shape : Shape) :=
  { sourceCodeState false false with
    clock := 5
    locals := fun name => if name == "caller" then some (.word 3) else none
    memory := fun _ => some (.word 0)
    code := [("callee", ([], .return (.const 7), shape))] }

#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (routedReturnState .one) (.call none "callee" []) with
  | some (.control (.returned _ _ _ _ [.word value]), _) => value == 7
  | _ => false)
#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (routedReturnState (.comb [.one, .one])) (.call none "callee" []) with
  | some (.control (.error locals _ _ _), clock) => (locals "caller").isNone && clock == 4
  | _ => false)
#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    (routedReturnState (.comb [.one, .one])) (.decCall "dest" .one "callee" [] .skip) with
  | some (.control (.error locals _ _ _), clock) => (locals "caller").isNone && clock == 4
  | _ => false)

private def routedParamReturnState :=
  { routedReturnState (.comb [.one, .one]) with
    code := [("callee", ([("x", .one)], .return (.const 7), .comb [.one, .one]))] }

#guard (match panSemEvaluateRiscV64CodeStateViaHOL sourceFfiContext sourcePrimitive sourceFfiHandler
    routedParamReturnState (.call none "callee" [.const 4]) with
  | some (.control (.error locals _ _ _), _) => (locals "x").isNone
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

private def programInput (owner : PanSemState W (FfiState Unit)) (bytes : W) :
    PanSemRiscV64ProgramInput Unit :=
  { initial := initialProgram owner bytes
    memaddrs := owner.memaddrs
    sharedMemaddrs := owner.sharedMemaddrs
    bigEndian := owner.be }

private def programDecls : List (Decl W) :=
  [.decl .one "g" (.loadByte (.const 0)),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.var .global "g"), returnShape := .one }]

/- The final structure context is collected before initializers, even when
   its declaration follows them. Both initialization and entry use that cache. -/
private def programDeclsWithLaterStruct := programDecls ++ [.name "S" [("field", .one)]]

#guard (match collectPanValueStructs programDeclsWithLaterStruct [] with
  | some structs => (panSemExpressionContextCache structs).ranged
  | none => false)
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsWithLaterStruct "main" []) 0x88

/- A non-byte name in the collected context selects the String fallback while
   preserving the initializer and entry result. -/
private def programDeclsWithFallbackStruct := programDecls ++ [.name "Ā" [("field", .one)]]

#guard (match collectPanValueStructs programDeclsWithFallbackStruct [] with
  | some structs => !(panSemExpressionContextCache structs).ranged
  | none => false)
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsWithFallbackStruct "main" []) 0x88

/- A struct-using initializer and entry body need the collected structure
   context in both phases. The `.nStruct`/`.nField` expressions read the named
   struct through the route's pinned structure context, so a route that
   received the wrong context fails here. The expected value is cross-checked
   against the generic runner only; there is no HOL probe for this
   struct-specific program. -/
private def programDeclsStructFirst : List (Decl W) :=
  [.name "S" [("a", .one), ("b", .one)],
   .decl .one "g" (.nField "a" (.nStruct "S" [("a", .const 1), ("b", .const 2)])),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.nField "b" (.nStruct "S" [("a", .const 3), ("b", .const 4)]))
       returnShape := .one }]

/- The struct declaration follows the initializer that uses it. The collected
   context must be available before initializers, as `decs_stcnames` provides. -/
private def programDeclsStructLater : List (Decl W) :=
  [.decl .one "g" (.nField "a" (.nStruct "S" [("a", .const 1), ("b", .const 2)])),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.nField "b" (.nStruct "S" [("a", .const 3), ("b", .const 4)]))
       returnShape := .one },
   .name "S" [("a", .one), ("b", .one)]]

/- Both struct expressions take the HOL route rather than the String fallback. -/
#guard (match collectPanValueStructs programDeclsStructLater [] with
  | some structs =>
      panSemExpressionUsesHOLCached (panSemExpressionContextCache structs)
        { (sourceCodeState false true) with structs := structs }
        (.nField "a" (.nStruct "S" [("a", .const 1), ("b", .const 2)]))
  | none => false)
#guard (match collectPanValueStructs programDeclsStructLater [] with
  | some structs =>
      panSemExpressionUsesHOLCached (panSemExpressionContextCache structs)
        { (sourceCodeState false true) with structs := structs }
        (.nField "b" (.nStruct "S" [("a", .const 3), ("b", .const 4)]))
  | none => false)

#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsStructFirst "main" []) 4
#guard observesWord
  (evalPanValueFfiClockProgram sourceFfiContext
    (initialProgram (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsStructFirst "main" []
    (memoryAccess := some (panSemBitVec64MemoryAccess (sourceCodeState false true)))
    (evaluator := none)) 4

#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsStructLater "main" []) 4
#guard observesWord
  (evalPanValueFfiClockProgram sourceFfiContext
    (initialProgram (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsStructLater "main" []
    (memoryAccess := some (panSemBitVec64MemoryAccess (sourceCodeState false true)))
    (evaluator := none)) 4

/- Without the struct declaration the initializer fails; both runners reject. -/
private def programDeclsMissingStruct : List (Decl W) :=
  [.decl .one "g" (.nField "a" (.nStruct "S" [("a", .const 1), ("b", .const 2)])),
   .function
     { name := "main", inline := false, exported := true, params := []
       body := .return (.var .global "g"), returnShape := .one }]

#guard (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsMissingStruct "main" []).isNone
#guard (evalPanValueFfiClockProgram sourceFfiContext
    (initialProgram (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDeclsMissingStruct "main" []
    (memoryAccess := some (panSemBitVec64MemoryAccess (sourceCodeState false true)))
    (evaluator := none)).isNone

/- This exercises both the declaration initializer and the entry body through
   the state-derived HOL route. The expected bytes come from the HOL probe. -/
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []) 0x88
#guard observesWord
  (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState true true) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []) 0x11
#guard (panSemEvaluateRiscV64ProgramViaHOL sourceFfiContext
    (programInput (sourceCodeState false false) 8)
    10 sourcePrimitive sourceFfiHandler 20 programDecls "main" []).isNone

#guard observesWord
  (panSemEvaluateRiscV64ProgramWithProductionPrimop sourceFfiContext
    (programInput (sourceCodeState true true) 8)
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
