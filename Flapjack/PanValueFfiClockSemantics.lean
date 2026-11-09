module

public import Flapjack.PanValueFfiCore
public import Flapjack.PanBst

@[expose] public section

/-!
# Clocked structured Pancake semantics

This module adds the clock/timeout part of CakeML's `panSem` boundary to the
canonical structured, stateful-FFI evaluator.  The clocked evaluator charges
one unit at a function call, at each executed while
iteration, and at `Tick`, exactly as `dec_clock` is used by `panSem`.

Semantic errors (`panSem`'s `SOME Error`) are explicit
`PanValueFfiControlResult.error` results carrying the unchanged state, while
timeout is explicit and clears source locals.  Only a genuinely missing
evaluation result (for example fuel exhaustion) is `none`.  Keeping timeout in
a separate result type avoids changing the established control-result API used
by the compiler proofs.
-/

namespace Flapjack

/-! Exact clock projection of Pancake's `dec_clock_def`
    (`cakeml/pancake/semantics/panSemScript.sml:441-443`).  The structured
    clock evaluator carries the state components separately, so this helper
    is the state-update equation's clock component. -/
abbrev decPanClock (clock : Nat) : Nat :=
  clock - 1

inductive PanValueFfiClockOutcome (α : Type u) (σ : Type v) where
  | control (result : PanValueFfiControlResult α σ)
  | timeout (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ)

abbrev PanValueFfiClockResult (α : Type u) (σ : Type v) :=
  PanValueFfiClockOutcome α σ × Nat

/-! Exact clock projection of Pancake's `fix_clock_def`
    (`cakeml/pancake/semantics/panSemScript.sml:446-448`).  The result is
    unchanged and the returned clock is clamped to the smaller old/new
    clock.  This is transparent so existing clock proofs can still rewrite
    the underlying subtraction and minimum directly. -/
abbrev fixPanClock {β : Type u} (oldClock : Nat) (step : β × Nat) :
    β × Nat :=
  let (outcome, newClock) := step
  (outcome, min oldClock newClock)

def panValueFfiClockTimeout
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) : PanValueFfiClockResult α σ :=
  (.timeout (fun _ => none) globals memory ffi, clock)

def panValueFfiClockRestoreLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueFfiClockOutcome α σ → PanValueFfiClockOutcome α σ
  | .control result => .control (restorePanValueFfiLocal name oldValue result)
  | .timeout locals globals memory ffi =>
      .timeout (restorePanValueLocal locals name oldValue) globals memory ffi

def panValueFfiClockClearTimeoutLocals :
    PanValueFfiClockOutcome α σ → PanValueFfiClockOutcome α σ
  | .control result => .control result
  | .timeout _ globals memory ffi => .timeout (fun _ => none) globals memory ffi

/-- Control result of a simple statement (a leaf) under the clocked
    semantics, with an optional alternative expression route.  The leaves are
    the statements that neither recurse nor touch the clock; each is the
    control result of the corresponding `PanValueFfiCore` helper.  `Tick`,
    `Dec`, `Seq`, `If`, `While`, `Call` and `DecCall` are handled by the clocked
    evaluators themselves and never reach this function.  It returns `none` for
    them, so an evaluator that forgot its own `Tick` clause would fail instead
    of silently skipping the clock. -/
def evalPanValueFfiLeafControl
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiControlResult α σ) :=
  match program with
    | .skip | .annot _ _ => some (.normal locals globals memory ffi)
    | .break => some (.broke locals globals memory ffi)
    | .continue => some (.continued locals globals memory ffi)
    | .assign .local name value =>
        panValueAssignLocalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess evaluator
    | .assign .global name value =>
        panValueAssignGlobalResult structs baseAddress topAddress bytesInWord locals globals
          memory ffi name value memoryAccess evaluator
    | .primitive name op args =>
        panValuePrimitiveResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi name op args memoryAccess primitive evaluator
    | .store address value =>
        panValueStoreResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess evaluator
    | .store32 address value =>
        panValueStore32Result structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess evaluator
    | .storeByte address value =>
        panValueStoreByteResult structs baseAddress topAddress bytesInWord locals globals memory
          ffi address value memoryAccess evaluator
    | .extCall function config configLength array arrayLength =>
        panValueFfiExtCallResult context handler structs baseAddress topAddress bytesInWord
          locals globals memory ffi function config configLength array arrayLength
          memoryAccess memoryHandler evaluator
    | .return value =>
        panValueReturnResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          value memoryAccess evaluator
    | .raise exception value =>
        panValueRaiseResult structs baseAddress topAddress bytesInWord locals globals memory ffi
          contracts exception value memoryAccess evaluator
    | .shMemLoad size kind name address =>
        panValueShMemLoadResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size kind name address memoryAccess evaluator
    | .shMemStore size address value =>
        panValueShMemStoreResult context structs baseAddress topAddress bytesInWord locals globals
          memory ffi size address value memoryAccess evaluator
    | .tick | .dec .. | .seq .. | .ite .. | .while .. | .call .. | .decCall .. => none

/-- The leaf statements: exactly those that `evalPanValueFfiClockCodeProg` hands
    to `evalPanValueFfiClockLeaf`, i.e. every constructor except `Tick` and the
    compound statements. -/
inductive PanValueFfiLeafProg : Prog α → Prop
  | skip : PanValueFfiLeafProg (.skip : Prog α)
  | assign (kind : VarKind) (name : VarName) (value : Exp α) :
      PanValueFfiLeafProg (.assign kind name value)
  | primitive (name : VarName) (operator : PrimOp) (args : List (Exp α)) :
      PanValueFfiLeafProg (.primitive name operator args)
  | store (address value : Exp α) : PanValueFfiLeafProg (.store address value)
  | store32 (address value : Exp α) : PanValueFfiLeafProg (.store32 address value)
  | storeByte (address value : Exp α) : PanValueFfiLeafProg (.storeByte address value)
  | break : PanValueFfiLeafProg (.break : Prog α)
  | continue : PanValueFfiLeafProg (.continue : Prog α)
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Exp α) :
      PanValueFfiLeafProg (.extCall function configuration configurationLength array arrayLength)
  | raise (exception : ExceptionId) (value : Exp α) :
      PanValueFfiLeafProg (.raise exception value)
  | return (value : Exp α) : PanValueFfiLeafProg (.return value)
  | shMemLoad (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α) :
      PanValueFfiLeafProg (.shMemLoad size kind name address)
  | shMemStore (size : OpSize) (address value : Exp α) :
      PanValueFfiLeafProg (.shMemStore size address value)
  | annot (tag text : String) : PanValueFfiLeafProg (.annot tag text)

/-- The leaf clauses of the clocked evaluators: the leaf's control result at the
    unchanged clock.  `evaluator` optionally selects an alternative expression
    route; the default is the ordinary evaluator. -/
def evalPanValueFfiClockLeaf
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (baseAddress topAddress bytesInWord : α) (clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) : Option (PanValueFfiClockResult α σ) :=
  (evalPanValueFfiLeafControl context primitive handler structs baseAddress topAddress
    bytesInWord locals globals memory ffi program memoryAccess contracts memoryHandler
    evaluator).map (fun outcome => (.control outcome, clock))

/-- A pointwise-correct expression route preserves the complete result of
    every clocked leaf, including errors, state, FFI, and clock. -/
theorem evalPanValueFfiClockLeaf_some_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (base top bytes : α) (clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (access : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (run : PanExprEvaluator α)
    (h : ∀ e, run structs locals globals memory base top bytes access e =
      evalPanValueExp structs locals globals memory base top bytes e access) :
    evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock
      locals globals memory ffi program access contracts mh (some run) =
    evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock
      locals globals memory ffi program access contracts mh := by
  have hs : ∀ e, evalPanValueExpWith (some run) structs locals globals memory base top bytes e
      access = evalPanValueExpWith none structs locals globals memory base top bytes e access :=
    fun e => by simp [evalPanValueExpWith, h]
  have hl : ∀ es, evalPanValueExpsWith (some run) structs locals globals memory base top bytes es
      access = evalPanValueExpsWith none structs locals globals memory base top bytes es access :=
    fun es => by
      simpa [evalPanValueExpsWith] using
        evalPanValueExpsWith_some_eq run structs locals globals memory base top bytes access h es
  cases program
  case assign kind name value =>
    cases kind <;> simp only [evalPanValueFfiClockLeaf,
      evalPanValueFfiLeafControl, panValueAssignLocalResult, panValueAssignGlobalResult, hs]
  all_goals
    simp only [evalPanValueFfiClockLeaf,
      evalPanValueFfiLeafControl, panValuePrimitiveResult, panValueStoreResult, panValueStore32Result, panValueStoreByteResult,
      panValueFfiExtCallResult, panValueReturnResult, panValueRaiseResult,
      panValueShMemLoadResult, panValueShMemStoreResult, hs, hl]

/-! Source-state clock evaluator. Every Call and DecCall resolves directly
    from the finite code map that is threaded unchanged through recursive
    evaluation. This is an executable
    evaluator analogue exercised against direct HOL oracle cases; it is not
    tagged as a HOL theorem port because the full state-rel correspondence
    proof remains open. -/
mutual
  def evalPanValueFfiClockCodeCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (preserveReturnLocals : Bool := false) →
        (evaluator : Option (PanExprEvaluator α) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, info, function, arguments,
        memoryAccess, contracts, memoryHandler, preserveReturnLocals, evaluator => do
        (panValueCallArgumentsValue structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess evaluator).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun values =>
            (lookupPanSemCodeCall structs code function values).elim
              (pure (.control (.error locals globals memory ffi), clock))
              (fun codeTarget => do
              let (body, returnShape, calleeLocals) := codeTarget
              if clock = 0 then
                pure (panValueFfiClockTimeout globals memory ffi clock)
              else
                let (outcome, calleeClock) ← evalPanValueFfiClockCodeProg context primitive handler
                  structs code exceptionShapes baseAddress topAddress bytesInWord fuel calleeLocals
                  globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler) (evaluator := evaluator)
                let (outcome, calleeClock) :=
                  fixPanClock (decPanClock clock) (outcome, calleeClock)
                match outcome with
                | .timeout _ calleeGlobals calleeMemory calleeFfi =>
                    pure (.timeout (fun _ => none) calleeGlobals calleeMemory calleeFfi,
                      calleeClock)
                | .control result =>
                    match result with
                    | .normal calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .broke calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .continued calleeLocals calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error calleeLocals calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .error _ calleeGlobals calleeMemory calleeFfi =>
                        pure (.control (.error (fun _ => none) calleeGlobals calleeMemory calleeFfi),
                          calleeClock)
                    | .returned calleeLocals calleeGlobals calleeMemory calleeFfi values =>
                        let sourceReturnValid := match values with
                          | [value] => panShapeMatches (panValueShape structs value) returnShape
                          | _ => false
                        if sourceReturnValid then
                          -- The source code entry supplies `returnShape`; HOL
                          -- Call checks that shape directly. `contracts` is an
                          -- optional extra input and is not part of the HOL
                          -- state, so it must not impose a second return-shape
                          -- check here. The payload-size limit is enforced by
                          -- the callee's `Return` equation.
                          match info with
                          | none =>
                              let returnedLocals :=
                                if preserveReturnLocals then calleeLocals else fun _ => none
                              pure (.control
                              (.returned returnedLocals calleeGlobals calleeMemory
                                calleeFfi values), calleeClock)
                          | some (destination, _) =>
                              match assignPanValueCallResult locals calleeGlobals destination values
                                  (structs := structs) with
                              | some (callerLocals, callerGlobals) =>
                                  pure (.control (.normal callerLocals callerGlobals
                                    calleeMemory calleeFfi), calleeClock)
                              | none =>
                                  pure (.control (.error calleeLocals calleeGlobals
                                    calleeMemory calleeFfi), calleeClock)
                        else pure (.control (.error calleeLocals calleeGlobals
                          calleeMemory calleeFfi), calleeClock)
                    | .raised calleeLocals calleeGlobals calleeMemory calleeFfi exception value =>
                        match info with
                        | some (_, some (caught, handlerVariable, handlerProgram)) =>
                            if caught == exception then
                              match exceptionShapes exception with
                              | some shape =>
                                  if panShapeMatches (panValueShape structs value) shape &&
                                      panValueAssignmentValid structs locals (fun _ => none)
                                        .local handlerVariable value then
                                    evalPanValueFfiClockCodeProg context primitive handler structs code
                                      exceptionShapes
                                      baseAddress topAddress bytesInWord fuel
                                      (updatePanValueMap locals handlerVariable value) calleeGlobals
                                      calleeMemory calleeFfi calleeClock handlerProgram
                                      (memoryAccess := memoryAccess) (contracts := contracts)
                                      (memoryHandler := memoryHandler) (evaluator := evaluator)
                                  else
                                    pure (.control (.error calleeLocals calleeGlobals
                                      calleeMemory calleeFfi), calleeClock)
                              | none =>
                                  pure (.control (.error calleeLocals calleeGlobals
                                    calleeMemory calleeFfi), calleeClock)
                            else pure (.control (.raised (fun _ => none) calleeGlobals
                              calleeMemory calleeFfi exception value), calleeClock)
                        | _ => pure (.control (.raised (fun _ => none) calleeGlobals
                            calleeMemory calleeFfi exception value), calleeClock)
                    | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                        pure (.control (.finalFfi (fun _ => none) calleeGlobals
                          calleeMemory calleeFfi event), calleeClock)
              ))
    termination_by fuel _ _ _ _ _ _ _ _ _ _ _ => fuel

  /-- State-code `DecCall` helper. The helper consumes the returned value only
      after the state-owned callee has completed, runs the continuation at the
      caller's local environment, and restores the old destination binding. -/
  def evalPanValueFfiClockCodeDecCall
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        VarName → Shape → FunName → List (Exp α) → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (evaluator : Option (PanExprEvaluator α) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, name, shape, function,
        arguments, body, memoryAccess, contracts, memoryHandler, evaluator => do
        let oldValue := locals name
        let (outcome, nextClock) ← evalPanValueFfiClockCodeCall context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals
          memory ffi clock none function arguments (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler) (evaluator := evaluator)
          (preserveReturnLocals := true)
        match outcome with
        | .control (.returned nextLocals nextGlobals nextMemory nextFfi [value]) =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockCodeProg
                context primitive handler structs code exceptionShapes baseAddress topAddress
                bytesInWord fuel (updatePanValueMap locals name value) nextGlobals nextMemory
                nextFfi nextClock body (memoryAccess := memoryAccess)
                (contracts := contracts) (memoryHandler := memoryHandler) (evaluator := evaluator)
              pure (panValueFfiClockRestoreLocal name oldValue bodyOutcome, bodyClock)
            else
              pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.raised _ nextGlobals nextMemory nextFfi exception value) =>
            pure (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
              exception value), nextClock)
        | .timeout nextLocals nextGlobals nextMemory nextFfi =>
            pure (.timeout nextLocals nextGlobals nextMemory nextFfi, nextClock)
        | .control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event) =>
            pure (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event), nextClock)
        | .control (.returned _ _ _ _ _) => none
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
            .control (.broke nextLocals nextGlobals nextMemory nextFfi) |
            .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.error nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
    termination_by fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiClockCodeProg
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (context : PanValueFfiContext α)
      (primitive : PanPrimitiveHandler α)
      (handler : PanValueStatefulFfiHandler α σ)
      (structs : StructContext) (code : PanSemCodeMap α)
      (exceptionShapes : ExceptionId → Option Shape)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (evaluator : Option (PanExprEvaluator α) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .dec name shape value body,
        memoryAccess, contracts, memoryHandler, evaluator =>
        (panValueDecAcceptedValue structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape evaluator).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun evaluated => do
            let oldValue := locals name
            let (outcome, nextClock) ← evalPanValueFfiClockCodeProg context primitive handler
              structs code exceptionShapes baseAddress topAddress bytesInWord fuel
              (updatePanValueMap locals name evaluated) globals memory ffi clock body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler) (evaluator := evaluator)
            pure (panValueFfiClockRestoreLocal name oldValue outcome, nextClock))
    | fuel + 1, locals, globals, memory, ffi, clock, .seq first second,
        memoryAccess, contracts, memoryHandler, evaluator => do
        let (firstOutcome, firstClock) ← evalPanValueFfiClockCodeProg context primitive handler
          structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi
          clock first (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (evaluator := evaluator)
        let (firstOutcome, firstClock) := fixPanClock clock (firstOutcome, firstClock)
        match firstOutcome with
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
            evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
              baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
              firstClock second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler) (evaluator := evaluator)
        | _ => pure (firstOutcome, firstClock)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler, evaluator =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory condition memoryAccess evaluator).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun condition =>
            evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
              baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
              (if condition != 0 then thenBranch else elseBranch)
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler) (evaluator := evaluator))
    | fuel + 1, locals, globals, memory, ffi, clock,
        .call info function arguments, memoryAccess, contracts, memoryHandler, evaluator =>
        evalPanValueFfiClockCodeCall context primitive handler structs code exceptionShapes
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info
          function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (evaluator := evaluator)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler, evaluator => do
        evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptionShapes
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock name shape
          function arguments body (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (evaluator := evaluator)
    | _fuel + 1, locals, globals, memory, ffi, clock,
        .raise exception expression, memoryAccess, _contracts, _memoryHandler, evaluator =>
        match evalPanValueExpWith evaluator structs locals globals memory baseAddress topAddress
            bytesInWord expression memoryAccess with
        | none => pure (.control (.error locals globals memory ffi), clock)
        | some value =>
            match exceptionShapes exception with
            | some shape =>
                if panShapeMatches (panValueShape structs value) shape &&
                    panValuePayloadWithinLimit structs value then
                  pure (.control (.raised (fun _ => none) globals memory ffi
                    exception value), clock)
                else pure (.control (.error locals globals memory ffi), clock)
            | none => pure (.control (.error locals globals memory ffi), clock)
    | fuel + 1, locals, globals, memory, ffi, clock, .while conditionExp body,
        memoryAccess, contracts, memoryHandler, evaluator =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess evaluator).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun conditionValue =>
            if conditionValue == 0 then
              pure (.control (.normal locals globals memory ffi), clock)
            else if clock == 0 then
              pure (panValueFfiClockTimeout globals memory ffi clock)
            else do
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockCodeProg context primitive handler
                structs code exceptionShapes baseAddress topAddress bytesInWord fuel locals globals memory ffi
                (decPanClock clock) body (memoryAccess := memoryAccess)
                (contracts := contracts) (memoryHandler := memoryHandler) (evaluator := evaluator)
              let (bodyOutcome, bodyClock) :=
                fixPanClock (decPanClock clock) (bodyOutcome, bodyClock)
              match bodyOutcome with
              | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
                  .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
                  evalPanValueFfiClockCodeProg context primitive handler structs code exceptionShapes
                    baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
                    bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler) (evaluator := evaluator)
              | .control (.broke nextLocals nextGlobals nextMemory nextFfi) =>
                  pure (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock)
              | _ => pure (bodyOutcome, bodyClock))
    | _fuel + 1, locals, globals, memory, ffi, clock, .tick, _, _, _, _evaluator =>
        if clock == 0 then pure (panValueFfiClockTimeout globals memory ffi clock)
        else pure (.control (.normal locals globals memory ffi), decPanClock clock)
    | _fuel + 1, locals, globals, memory, ffi, clock, program, memoryAccess, contracts,
        memoryHandler, evaluator =>
        evalPanValueFfiClockLeaf context primitive handler structs
          baseAddress topAddress bytesInWord clock locals globals memory ffi program
          memoryAccess contracts memoryHandler evaluator
    termination_by fuel _ _ _ _ _ _ _ _ _ _ => fuel
end

/-- A result clock is at most the input clock; `none` results are unconstrained.

    This is the clock bound that HOL proves in `evaluate_clock`
    (`panSemScript.sml:752-760`) for the shared `evaluate` relation: every
    evaluator result clock is at most the input clock.  HOL's
    `fix_clock_evaluate` (`panSemScript.sml:772-778`) then turns the bound into
    `fix_clock` being the identity on results. -/
def panValueFfiClockBounded {α : Type u} {σ : Type v}
    (clock : Nat) : Option (PanValueFfiClockResult α σ) → Prop
  | none => True
  | some (_, clock') => clock' ≤ clock

@[simp] theorem panValueFfiClockBounded_none {α : Type u} {σ : Type v} (clock : Nat) :
    panValueFfiClockBounded (α := α) (σ := σ) clock none := by
  simp [panValueFfiClockBounded]

@[simp] theorem panValueFfiClockBounded_some {α : Type u} {σ : Type v}
    (clock : Nat) (outcome : PanValueFfiClockOutcome α σ) (clock' : Nat) :
    panValueFfiClockBounded clock (some (outcome, clock')) ↔ clock' ≤ clock := by
  simp [panValueFfiClockBounded]

@[simp] theorem panValueFfiClockBounded_pure {α : Type u} {σ : Type v}
    (clock : Nat) (outcome : PanValueFfiClockOutcome α σ) (clock' : Nat) :
    panValueFfiClockBounded clock (pure (outcome, clock')) ↔ clock' ≤ clock := by
  simp [panValueFfiClockBounded]

@[simp] theorem panValueFfiClockBounded_some_of_le {α : Type u} {σ : Type v}
    (clock : Nat) (outcome : PanValueFfiClockOutcome α σ) (clock' : Nat)
    (h : clock' ≤ clock) :
    panValueFfiClockBounded clock (some (outcome, clock')) :=
  Iff.mpr (panValueFfiClockBounded_some clock outcome clock') h

theorem panValueFfiClockBounded_pure_of_le {α : Type u} {σ : Type v}
    (clock : Nat) (outcome : PanValueFfiClockOutcome α σ) (clock' : Nat)
    (h : clock' ≤ clock) :
    panValueFfiClockBounded clock (pure (outcome, clock')) :=
  (panValueFfiClockBounded_pure clock outcome clock').mpr h

theorem panValueFfiClockBounded_mono {α : Type u} {σ : Type v}
    {x : Option (PanValueFfiClockResult α σ)} {c c' : Nat}
    (h : c' ≤ c) (hb : panValueFfiClockBounded c' x) :
    panValueFfiClockBounded c x := by
  cases x with
  | none => exact panValueFfiClockBounded_none c
  | some p =>
      obtain ⟨o, k⟩ := p
      simp only [panValueFfiClockBounded_some] at hb ⊢
      omega

@[simp] theorem panValueFfiClockTimeout_snd {α : Type u} {σ : Type v}
    (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :
    (panValueFfiClockTimeout globals memory ffi clock).2 = clock := rfl

private theorem evalPanValueFfiClockLeaf_bounded
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (base top bytes : α) (clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (access : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (evaluator : Option (PanExprEvaluator α)) :
    panValueFfiClockBounded clock
      (evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock
        locals globals memory ffi program access contracts mh evaluator) := by
  simp only [evalPanValueFfiClockLeaf]
  cases hleaf : evalPanValueFfiLeafControl context primitive handler structs base top bytes
      locals globals memory ffi program access contracts mh evaluator with
  | none =>
      show panValueFfiClockBounded clock none
      exact panValueFfiClockBounded_none clock
  | some outcome =>
      exact panValueFfiClockBounded_some_of_le clock _ clock (Nat.le_refl clock)

/-- Every code-map evaluator result clock is at most the input clock, for
    calls, DecCall, and programs.  This mirrors HOL `evaluate_clock`
    (`panSemScript.sml:752-760`): each recursive step either returns the
    current clock, decrements it with `decPanClock`, or propagates a callee
    clock that is already bounded. -/
theorem evalPanValueFfiClockCode_clock_bounded
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) :
    ∀ fuel,
      (∀ locals globals memory ffi clock info function arguments preserve
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockBounded clock
          (evalPanValueFfiClockCodeCall context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock info function arguments
            access contracts mh preserve evaluator)) ∧
      (∀ locals globals memory ffi clock name shape function arguments body
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockBounded clock
          (evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock name shape function arguments
            body access contracts mh evaluator)) ∧
      (∀ locals globals memory ffi clock program
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockBounded clock
          (evalPanValueFfiClockCodeProg context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock program access contracts mh
            evaluator)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;>
        intro <;>
        simp [evalPanValueFfiClockCodeCall, evalPanValueFfiClockCodeDecCall,
          evalPanValueFfiClockCodeProg]
  | succ fuel ih =>
      obtain ⟨ihCall, ihDecCall, ihProg⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro locals globals memory ffi clock info function arguments preserve evaluator
        have hdec : decPanClock clock ≤ clock := by simp [decPanClock]
        simp only [evalPanValueFfiClockCodeCall]
        cases hargs : panValueCallArgumentsValue structs base top bytes locals globals memory
            arguments access evaluator with
        | none =>
            simp only [Option.elim_none]
            simp [panValueFfiClockBounded]
        | some argValues =>
            simp only [Option.elim_some]
            cases hlook : lookupPanSemCodeCall structs code function argValues with
            | none =>
                simp only [Option.elim_none]
                simp [panValueFfiClockBounded]
            | some codeTarget =>
                simp only [Option.elim_some]
                obtain ⟨body, returnShape, calleeLocals⟩ := codeTarget
                split
                next => simp [panValueFfiClockBounded]
                next hclock =>
                  cases hrec : evalPanValueFfiClockCodeProg context primitive handler structs
                      code exceptions base top bytes fuel calleeLocals globals memory ffi
                      (decPanClock clock) body access contracts mh evaluator with
                  | none => simp [panValueFfiClockBounded]
                  | some step =>
                      obtain ⟨callOutcome, callClock⟩ := step
                      have hb := ihProg calleeLocals globals memory ffi (decPanClock clock) body
                        evaluator
                      rw [hrec] at hb
                      simp only [panValueFfiClockBounded_some] at hb
                      simp only [Option.bind_eq_bind, Option.bind_some]
                      split
                      next => simp [panValueFfiClockBounded] <;> omega
                      next result =>
                        split
                        next => simp [panValueFfiClockBounded] <;> omega
                        next => simp [panValueFfiClockBounded] <;> omega
                        next => simp [panValueFfiClockBounded] <;> omega
                        next => simp [panValueFfiClockBounded] <;> omega
                        next calleeLocals' calleeGlobals' calleeMemory' calleeFfi' values' =>
                          split
                          next =>
                            split
                            next =>
                              split
                              next => simp [panValueFfiClockBounded] <;> omega
                              next destination =>
                                split
                                next callerLocals' callerGlobals' =>
                                  simp [panValueFfiClockBounded] <;> omega
                                next => simp [panValueFfiClockBounded] <;> omega
                            next => simp [panValueFfiClockBounded] <;> omega
                          next => simp [panValueFfiClockBounded] <;> omega
                        next calleeLocals' calleeGlobals' calleeMemory' calleeFfi'
                            exception' value' =>
                          split
                          next caught' handlerVariable' handlerProgram' =>
                            split
                            next h =>
                              split
                              next shape' =>
                                split
                                next =>
                                  cases hhandler : evalPanValueFfiClockCodeProg context primitive
                                      handler structs code exceptions base top bytes fuel
                                      (updatePanValueMap locals handlerVariable' value')
                                      calleeGlobals' calleeMemory' calleeFfi'
                                      (min (decPanClock clock) callClock) handlerProgram'
                                      access contracts mh evaluator with
                                  | none => simp [panValueFfiClockBounded]
                                  | some step2 =>
                                      obtain ⟨handlerOutcome, handlerClock⟩ := step2
                                      have hb2 := ihProg
                                        (updatePanValueMap locals handlerVariable' value')
                                        calleeGlobals' calleeMemory' calleeFfi'
                                        (min (decPanClock clock) callClock) handlerProgram'
                                        evaluator
                                      rw [hhandler] at hb2
                                      simp only [panValueFfiClockBounded_some] at hb2
                                      simp [panValueFfiClockBounded] <;> omega
                                next => simp [panValueFfiClockBounded] <;> omega
                              next => simp [panValueFfiClockBounded] <;> omega
                            next => simp [panValueFfiClockBounded] <;> omega
                          next => simp [panValueFfiClockBounded] <;> omega
                        next calleeLocals' calleeGlobals' calleeMemory' calleeFfi' event' =>
                          simp [panValueFfiClockBounded] <;> omega
      · intro locals globals memory ffi clock name shape function arguments body evaluator
        have hdec : decPanClock clock ≤ clock := by simp [decPanClock]
        simp only [evalPanValueFfiClockCodeDecCall]
        cases hcall : evalPanValueFfiClockCodeCall context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock none function arguments access
            contracts mh true evaluator with
        | none => simp [panValueFfiClockBounded]
        | some step =>
            obtain ⟨callOutcome, callClock⟩ := step
            have hb := ihCall locals globals memory ffi clock none function arguments true evaluator
            rw [hcall] at hb
            simp only [panValueFfiClockBounded_some] at hb
            simp only [Option.bind_eq_bind, Option.bind_some]
            split
            next nextLocals' nextGlobals' nextMemory' nextFfi' value' =>
              split
              next =>
                cases hcont : evalPanValueFfiClockCodeProg context primitive handler structs
                    code exceptions base top bytes fuel
                    (updatePanValueMap locals name value') nextGlobals' nextMemory' nextFfi'
                    callClock body access contracts mh evaluator with
                | none => simp [panValueFfiClockBounded]
                | some step2 =>
                    obtain ⟨bodyOutcome, bodyClock⟩ := step2
                    have hb2 := ihProg (updatePanValueMap locals name value') nextGlobals'
                      nextMemory' nextFfi' callClock body evaluator
                    rw [hcont] at hb2
                    simp only [panValueFfiClockBounded_some] at hb2
                    simp only [Option.bind_some]
                    simp [panValueFfiClockBounded] <;> omega
              next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
            next => simp [panValueFfiClockBounded] <;> omega
      · intro locals globals memory ffi clock program evaluator
        have hdec : decPanClock clock ≤ clock := by simp [decPanClock]
        cases program with
        | skip =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi .skip access contracts mh evaluator
        | «break» =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi .break access contracts mh evaluator
        | «continue» =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi .continue access contracts mh evaluator
        | annot tag text =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.annot tag text) access contracts mh evaluator
        | assign kind name value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.assign kind name value) access contracts mh
                evaluator
        | primitive name operator args =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.primitive name operator args) access contracts mh
                evaluator
        | store address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.store address value) access contracts mh evaluator
        | store32 address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.store32 address value) access contracts mh evaluator
        | storeByte address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.storeByte address value) access contracts mh
                evaluator
        | extCall function config configLength array arrayLength =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi
              (.extCall function config configLength array arrayLength) access contracts mh
                evaluator
        | «return» value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.return value) access contracts mh evaluator
        | shMemLoad size kind name address =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.shMemLoad size kind name address)
                access contracts mh evaluator
        | shMemStore size address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_bounded context primitive handler structs base top bytes
              clock locals globals memory ffi (.shMemStore size address value) access contracts mh
                evaluator
        | dec name shape value body =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hdecAccept : panValueDecAcceptedValue structs base top bytes locals globals memory
                value access shape evaluator with
            | none =>
                simp only [Option.elim_none]
                simp [panValueFfiClockBounded]
            | some evaluated =>
                simp only [Option.elim_some]
                cases hrec : evalPanValueFfiClockCodeProg context primitive handler structs code
                    exceptions base top bytes fuel (updatePanValueMap locals name evaluated)
                    globals memory ffi clock body access contracts mh evaluator with
                | none => simp [panValueFfiClockBounded]
                | some step =>
                    obtain ⟨nextOutcome, nextClock⟩ := step
                    have hb := ihProg (updatePanValueMap locals name evaluated) globals memory ffi
                      clock body evaluator
                    rw [hrec] at hb
                    simp only [panValueFfiClockBounded_some] at hb
                    simp only [Option.bind_eq_bind, Option.bind_some]
                    simp [panValueFfiClockBounded] <;> omega
        | seq first second =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hfirst : evalPanValueFfiClockCodeProg context primitive handler structs code
                exceptions base top bytes fuel locals globals memory ffi clock first access
                contracts mh evaluator with
            | none => simp [panValueFfiClockBounded]
            | some step =>
                obtain ⟨firstOutcome, firstClock⟩ := step
                have hb := ihProg locals globals memory ffi clock first evaluator
                rw [hfirst] at hb
                simp only [panValueFfiClockBounded_some] at hb
                simp only [Option.bind_eq_bind, Option.bind_some]
                split
                next nextLocals' nextGlobals' nextMemory' nextFfi' =>
                  cases hsecond : evalPanValueFfiClockCodeProg context primitive handler structs
                      code exceptions base top bytes fuel nextLocals' nextGlobals' nextMemory'
                      nextFfi' (min clock firstClock) second access contracts mh evaluator with
                  | none => simp [panValueFfiClockBounded]
                  | some step2 =>
                      obtain ⟨secondOutcome, secondClock⟩ := step2
                      have hb2 := ihProg nextLocals' nextGlobals' nextMemory' nextFfi'
                        (min clock firstClock) second evaluator
                      rw [hsecond] at hb2
                      simp only [panValueFfiClockBounded_some] at hb2
                      simp [panValueFfiClockBounded] <;> omega
                next => simp [panValueFfiClockBounded] <;> omega
        | ite condition thenBranch elseBranch =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hcond : panValueIteConditionValue structs base top bytes locals globals memory
                condition access evaluator with
            | none =>
                simp only [Option.elim_none]
                simp [panValueFfiClockBounded]
            | some conditionValue =>
                simp only [Option.elim_some]
                split
                next => exact ihProg locals globals memory ffi clock thenBranch evaluator
                next => exact ihProg locals globals memory ffi clock elseBranch evaluator
        | call info function arguments =>
            simp only [evalPanValueFfiClockCodeProg]
            exact ihCall locals globals memory ffi clock info function arguments false evaluator
        | decCall name shape function arguments body =>
            simp only [evalPanValueFfiClockCodeProg]
            exact ihDecCall locals globals memory ffi clock name shape function arguments body
              evaluator
        | raise exception expression =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hexp : evalPanValueExpWith evaluator structs locals globals memory base top bytes
                expression access with
            | none => simp [panValueFfiClockBounded]
            | some value =>
                split
                next => simp [panValueFfiClockBounded]
                next =>
                  split
                  next shape' =>
                    split
                    next => simp [panValueFfiClockBounded]
                    next => simp [panValueFfiClockBounded] <;> omega
                  next => simp [panValueFfiClockBounded]
        | «while» conditionExp body =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hcond : panValueIteConditionValue structs base top bytes locals globals memory
                conditionExp access evaluator with
            | none =>
                simp only [Option.elim_none]
                simp [panValueFfiClockBounded]
            | some conditionValue =>
                simp only [Option.elim_some]
                split
                next => simp [panValueFfiClockBounded]
                next =>
                  split
                  next => simp [panValueFfiClockBounded]
                  next =>
                    cases hbody : evalPanValueFfiClockCodeProg context primitive handler structs
                        code exceptions base top bytes fuel locals globals memory ffi
                        (decPanClock clock) body access contracts mh evaluator with
                    | none => simp [panValueFfiClockBounded]
                    | some step =>
                        obtain ⟨bodyOutcome, bodyClock⟩ := step
                        have hb := ihProg locals globals memory ffi (decPanClock clock) body
                          evaluator
                        rw [hbody] at hb
                        simp only [panValueFfiClockBounded_some] at hb
                        simp only [Option.bind_eq_bind, Option.bind_some]
                        split
                        next nextLocals' nextGlobals' nextMemory' nextFfi' =>
                          cases hrec : evalPanValueFfiClockCodeProg context primitive handler
                              structs code exceptions base top bytes fuel nextLocals' nextGlobals'
                              nextMemory' nextFfi' (min (decPanClock clock) bodyClock)
                              (.while conditionExp body) access contracts mh evaluator with
                          | none => simp [panValueFfiClockBounded]
                          | some step2 =>
                              obtain ⟨whileOutcome, whileClock⟩ := step2
                              have hb2 := ihProg nextLocals' nextGlobals' nextMemory' nextFfi'
                                (min (decPanClock clock) bodyClock) (.while conditionExp body)
                                evaluator
                              rw [hrec] at hb2
                              simp only [panValueFfiClockBounded_some] at hb2
                              simp [panValueFfiClockBounded] <;> omega
                        next nextLocals' nextGlobals' nextMemory' nextFfi' =>
                          cases hrec : evalPanValueFfiClockCodeProg context primitive handler
                              structs code exceptions base top bytes fuel nextLocals' nextGlobals'
                              nextMemory' nextFfi' (min (decPanClock clock) bodyClock)
                              (.while conditionExp body) access contracts mh evaluator with
                          | none => simp [panValueFfiClockBounded]
                          | some step2 =>
                              obtain ⟨whileOutcome, whileClock⟩ := step2
                              have hb2 := ihProg nextLocals' nextGlobals' nextMemory' nextFfi'
                                (min (decPanClock clock) bodyClock) (.while conditionExp body)
                                evaluator
                              rw [hrec] at hb2
                              simp only [panValueFfiClockBounded_some] at hb2
                              simp [panValueFfiClockBounded] <;> omega
                        next => simp [panValueFfiClockBounded] <;> omega
                        next => simp [panValueFfiClockBounded] <;> omega
        | tick =>
            simp only [evalPanValueFfiClockCodeProg]
            split
            next => simp [panValueFfiClockBounded]
            next => simp [panValueFfiClockBounded] <;> omega

/-- `fixPanClock` clamps to the smaller of the old clock and the result clock;
    when the result clock is already at most the old clock the clamp is the
    identity, mirroring HOL `fix_clock_evaluate` (`panSemScript.sml:772-778`). -/
theorem fixPanClock_eq_self {β : Type u} (oldClock : Nat) (outcome : β) (newClock : Nat)
    (h : newClock ≤ oldClock) :
    fixPanClock oldClock (outcome, newClock) = (outcome, newClock) := by
  simp [fixPanClock, Nat.min_eq_right h]

/-- The pair form of `evalPanValueFfiClockCode_clock_bounded`: whenever a
    code-map evaluator call, DecCall, or program returns `some (result, clock')`,
    the result clock is at most the input clock. -/
theorem evalPanValueFfiClockCode_clock_le
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (fuel : Nat) :
    (∀ locals globals memory ffi clock info function arguments preserve
        (evaluator : Option (PanExprEvaluator α))
        (result : PanValueFfiClockResult α σ),
      evalPanValueFfiClockCodeCall context primitive handler structs code exceptions base top
        bytes fuel locals globals memory ffi clock info function arguments access contracts mh
        preserve evaluator = some result → result.2 ≤ clock) ∧
    (∀ locals globals memory ffi clock name shape function arguments body
        (evaluator : Option (PanExprEvaluator α))
        (result : PanValueFfiClockResult α σ),
      evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions base
        top bytes fuel locals globals memory ffi clock name shape function arguments body
        access contracts mh evaluator = some result → result.2 ≤ clock) ∧
    (∀ locals globals memory ffi clock program
        (evaluator : Option (PanExprEvaluator α))
        (result : PanValueFfiClockResult α σ),
      evalPanValueFfiClockCodeProg context primitive handler structs code exceptions base top
        bytes fuel locals globals memory ffi clock program access contracts mh evaluator = some
        result → result.2 ≤ clock) := by
  refine ⟨?_, ?_, ?_⟩
  · intro locals globals memory ffi clock info function arguments preserve evaluator result h
    obtain ⟨outcome, clock'⟩ := result
    have hb := (evalPanValueFfiClockCode_clock_bounded context primitive handler structs code
      exceptions base top bytes access contracts mh fuel).1 locals globals memory ffi clock info
      function arguments preserve evaluator
    rw [h] at hb
    exact (panValueFfiClockBounded_some clock outcome clock').mp hb
  · intro locals globals memory ffi clock name shape function arguments body evaluator result h
    obtain ⟨outcome, clock'⟩ := result
    have hb := (evalPanValueFfiClockCode_clock_bounded context primitive handler structs code
      exceptions base top bytes access contracts mh fuel).2.1 locals globals memory ffi clock
      name shape function arguments body evaluator
    rw [h] at hb
    exact (panValueFfiClockBounded_some clock outcome clock').mp hb
  · intro locals globals memory ffi clock program evaluator result h
    obtain ⟨outcome, clock'⟩ := result
    have hb := (evalPanValueFfiClockCode_clock_bounded context primitive handler structs code
      exceptions base top bytes access contracts mh fuel).2.2 locals globals memory ffi clock
      program evaluator
    rw [h] at hb
    exact (panValueFfiClockBounded_some clock outcome clock').mp hb

/-- The clock clamp applied by the code-map evaluator's `Seq`/`While`/`Call`
    clauses is the identity on every returned program result, mirroring HOL
    `fix_clock_evaluate` (`panSemScript.sml:772-778`). -/
theorem evalPanValueFfiClockCodeProg_fixPanClock_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) (program : Prog α)
    (evaluator : Option (PanExprEvaluator α)) (result : PanValueFfiClockResult α σ)
    (h : evalPanValueFfiClockCodeProg context primitive handler structs code exceptions base top
      bytes fuel locals globals memory ffi clock program access contracts mh evaluator = some
      result) :
    fixPanClock clock result = result := by
  obtain ⟨outcome, clock'⟩ := result
  have hle := (evalPanValueFfiClockCode_clock_le context primitive handler structs code exceptions
    base top bytes access contracts mh fuel).2.2 locals globals memory ffi clock program
    evaluator (outcome, clock') h
  exact fixPanClock_eq_self clock outcome clock' hle

/-- A pointwise-correct expression route preserves complete code-map
    evaluation for calls, DecCall, and programs. This covers results, clocks,
    and all state components, including failure and FFI outcomes. -/
theorem evalPanValueFfiClockCode_route_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext) (code : PanSemCodeMap α)
    (exceptions : ExceptionId → Option Shape) (base top bytes : α)
    (access : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) (run : PanExprEvaluator α)
    (h : ∀ locals globals memory e,
      run structs locals globals memory base top bytes access e =
        evalPanValueExp structs locals globals memory base top bytes e access) :
    ∀ fuel,
      (∀ locals globals memory ffi clock info function arguments preserve,
        evalPanValueFfiClockCodeCall context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock info function arguments access contracts mh preserve (some run) =
        evalPanValueFfiClockCodeCall context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock info function arguments access contracts mh preserve none) ∧
      (∀ locals globals memory ffi clock name shape function arguments body,
        evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock name shape function arguments body access contracts mh (some run) =
        evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock name shape function arguments body access contracts mh none) ∧
      (∀ locals globals memory ffi clock program,
        evalPanValueFfiClockCodeProg context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock program access contracts mh (some run) =
        evalPanValueFfiClockCodeProg context primitive handler structs code exceptions base top bytes
          fuel locals globals memory ffi clock program access contracts mh none) := by
  have hsingle : ∀ locals globals memory e,
      evalPanValueExpWith (some run) structs locals globals memory base top bytes e access =
        evalPanValueExp structs locals globals memory base top bytes e access := by
    intro locals globals memory e
    simpa [evalPanValueExpWith] using h locals globals memory e
  have hlist : ∀ locals globals memory es,
      evalPanValueExpsWith (some run) structs locals globals memory base top bytes es access =
        evalPanValueExps structs locals globals memory base top bytes es access := by
    intro locals globals memory es
    exact evalPanValueExpsWith_some_eq run structs locals globals memory base top bytes access
      (h locals globals memory) es
  have hleaf : ∀ locals globals memory ffi clock program,
      evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock
        locals globals memory ffi program access contracts mh (some run) =
      evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock
        locals globals memory ffi program access contracts mh none := by
    intro locals globals memory ffi clock program
    exact
      evalPanValueFfiClockLeaf_some_eq context primitive handler structs
      base top bytes clock locals globals memory ffi program access contracts mh run
      (h locals globals memory)
  intro fuel
  induction fuel with
  | zero =>
    simp [evalPanValueFfiClockCodeCall, evalPanValueFfiClockCodeDecCall, evalPanValueFfiClockCodeProg]
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro locals globals memory ffi clock info function arguments preserve
      simp only [evalPanValueFfiClockCodeCall, panValueCallArgumentsValue,
        evalPanValueExpsWith_none, hlist]
      simp only [ih.2.2]
    · intro locals globals memory ffi clock name shape function arguments body
      simp only [evalPanValueFfiClockCodeDecCall, ih.1, ih.2.2]
    · intro locals globals memory ffi clock program
      cases program <;> simp only [evalPanValueFfiClockCodeProg, panValueDecAcceptedValue,
        panValueIteConditionValue, evalPanValueExpWith_none, hsingle,
        ih.1, ih.2.1, ih.2.2, hleaf]

/-! General source Call exception-dispatch step.  The callee body, argument
values, return shape, exception payload, and handler program are all
parameters; `hcalleeBody` is the source-side induction hypothesis for the
callee.  This exposes the exact clock clamp and handler-local update used by
HOL `evaluate_def` without assuming a fixed callee syntax or a target run. -/
theorem evalPanValueFfiClockCodeCall_catchesRaisedBody
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (handlerVariable : VarName) (handlerProgram body : Prog α)
    (function : FunName) (exception : ExceptionId)
    (arguments : List (Exp α)) (values : List (PanValue α))
    (returnShape : Shape)
    (calleeLocals : VarName → Option (PanValue α))
    (calleeGlobals : VarName → Option (PanValue α))
    (calleeMemory : α → Option (PanValue α)) (calleeFfi : FfiState σ)
    (exceptionValue : PanValue α) (calleeClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (handlerResult : PanValueFfiClockResult α σ)
    (harguments : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hcallee : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, calleeLocals))
    (hclock : clock ≠ 0)
    (calleeRaisedLocals : VarName → Option (PanValue α))
    (hcalleeBody : evalPanValueFfiClockCodeProg context primitive handler
      structs code exceptionShapes baseAddress topAddress bytesInWord fuel
      calleeLocals globals memory ffi (decPanClock clock) body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
        some (.control (.raised calleeRaisedLocals calleeGlobals calleeMemory
          calleeFfi exception exceptionValue), calleeClock))
    (hexceptionShape : ∃ shape, exceptionShapes exception = some shape ∧
      panShapeMatches (panValueShape structs exceptionValue) shape = true)
    (hhandlerAssignment : panValueAssignmentValid structs locals (fun _ => none)
      .local handlerVariable exceptionValue = true)
    (hhandlerBody : evalPanValueFfiClockCodeProg context primitive handler
      structs code exceptionShapes baseAddress topAddress bytesInWord fuel
      (updatePanValueMap locals handlerVariable exceptionValue)
      calleeGlobals calleeMemory calleeFfi
      (min (decPanClock clock) calleeClock) handlerProgram
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) = some handlerResult) :
    evalPanValueFfiClockCodeCall context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals
      globals memory ffi clock
      (some (none, some (exception, handlerVariable, handlerProgram)))
      function arguments (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler) =
        some handlerResult := by
  rcases hexceptionShape with ⟨shape, hshape, hshapeMatch⟩
  simp [evalPanValueFfiClockCodeCall, Option.elim_some, panValueCallArgumentsValue, harguments, hcallee, hclock,
    hcalleeBody, hshape, hshapeMatch, hhandlerAssignment, hhandlerBody, decPanClock]

/-- State-owned code-map Call step for a callee whose single returned value has a
    shape that disagrees with the source code entry's declared `returnShape`.
    Cake's `evaluate (Call ...)` compares `shape_of retv` with `return_sh`
    (`panSemScript.sml:668-670`) and returns `(SOME Error, st)` over the callee
    post-call state.  This mirrors the fallthrough/break/continue/error call
    steps above for the code-map evaluator: the callee body result is an
    abstract hypothesis, so the equation is the generic return-shape rejection
    rather than a fully unfolded concrete entry.  The clock is HOL's `fix_clock`
    clamp `min (decPanClock clock) calleeClock`, and the `Error` carries the
    callee's post-state locals `st.locals` regardless of
    `preserveReturnLocals`, including bindings restored by an enclosing
    `Dec` after the callee's `Return`.  Untagged because the result is the
    reduced structured pair, not HOL's literal `result option × state` pair. -/
theorem evalPanValueFfiClockCodeCall_callee_returnedShapeMismatch_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (body : Prog α) (returnShape : Shape)
    (calleeLocals : VarName → Option (PanValue α))
    (bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (returnedValue : PanValue α)
    (calleeClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (preserveReturnLocals : Bool := false)
    (harguments : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (body, returnShape, calleeLocals))
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockCodeProg context primitive handler
      structs code exceptionShapes baseAddress topAddress bytesInWord fuel
      calleeLocals globals memory ffi (decPanClock clock) body
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
        some (.control (.returned bodyLocals finalGlobals finalMemory finalFfi
          [returnedValue]), calleeClock))
    (hmismatch : panShapeMatches (panValueShape structs returnedValue)
      returnShape = false) :
    evalPanValueFfiClockCodeCall context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord (fuel + 1) locals globals
      memory ffi clock info function arguments (memoryAccess := memoryAccess)
      (contracts := contracts) (memoryHandler := memoryHandler)
      (preserveReturnLocals := preserveReturnLocals) =
        some (.control (.error bodyLocals finalGlobals finalMemory finalFfi),
          min (decPanClock clock) calleeClock) := by
  simp [evalPanValueFfiClockCodeCall, panValueCallArgumentsValue, Option.elim_some,
    harguments, hlookup, hclock, hbody, hmismatch, decPanClock]

/-- State-owned code-map Call step for a callee whose own evaluation finished
    with `Error`.  Cake's catch-all `(res,st) => (res, empty_locals st)`
    (`panSemScript.sml:690`) clears the callee locals, so this is the one
    `Error` origin whose call result carries `fun _ => none`; the callee
    globals, memory and FFI state are kept and the clock is HOL's `fix_clock`
    clamp `min (decPanClock clock) calleeClock`.  The fall-through,
    `break`, `continue`, return-shape rejection and handler-invalid steps
    deliberately preserve the callee locals instead.  Untagged because the
    result is the reduced structured pair, not HOL's `result option × state`
    pair. -/
theorem evalPanValueFfiClockCodeCall_callee_error_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (calleeBody : Prog α) (returnShape : Shape)
    (calleeLocals finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (calleeClock : Nat)
    (access : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (mh : Option (PanValueMemoryFfiHandler α σ) := none)
    (preserveReturnLocals : Bool := false)
    (evaluator : Option (PanExprEvaluator α) := none)
    (harguments : panValueCallArgumentsValue structs baseAddress topAddress bytesInWord
      locals globals memory arguments access evaluator = some values)
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (calleeBody, returnShape, calleeLocals))
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockCodeProg context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi
      (decPanClock clock) calleeBody
      (memoryAccess := access) (contracts := contracts) (memoryHandler := mh)
      (evaluator := evaluator) =
        some (.control (.error finalLocals finalGlobals finalMemory finalFfi), calleeClock)) :
    evalPanValueFfiClockCodeCall context primitive handler structs code exceptionShapes
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock info
      function arguments (memoryAccess := access) (contracts := contracts)
      (memoryHandler := mh) (preserveReturnLocals := preserveReturnLocals)
      (evaluator := evaluator) =
        some (.control (.error (fun _ => none) finalGlobals finalMemory finalFfi),
          min (decPanClock clock) calleeClock) := by
  simp [evalPanValueFfiClockCodeCall, Option.elim_some, harguments, hlookup, hclock, hbody,
    decPanClock]

/-- State-owned `DecCall` forwards a callee-side `Error` as Cake's catch-all
    `(res,st) => (res, empty_locals st)` (`panSemScript.sml:713`): the code-map
    call helper already replaces the callee locals with `fun _ => none` (see
    `evalPanValueFfiClockCodeCall_callee_error_error`), and `DecCall`'s
    `.error` branch preserves that map unchanged, so the forwarded error is
    HOL's cleared-locals catch-all state.  The continuation body is not run on
    this path.  `DecCall` consumes one fuel step before dispatching the inner
    call, hence the `fuel + 2` entry point for a callee evaluated at `fuel`.
    This is the syntactic form of the extensional equality noted in the #1250
    review (report item 6). -/
theorem evalPanValueFfiClockCodeDecCall_callee_error_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (code : PanSemCodeMap α)
    (exceptionShapes : ExceptionId → Option Shape)
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α)
    (values : List (PanValue α)) (calleeBody : Prog α) (returnShape : Shape)
    (calleeLocals finalLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (calleeClock : Nat)
    (access : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (mh : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none)
    (harguments : panValueCallArgumentsValue structs baseAddress topAddress bytesInWord
      locals globals memory arguments access evaluator = some values)
    (hlookup : lookupPanSemCodeCall structs code function values =
      some (calleeBody, returnShape, calleeLocals))
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockCodeProg context primitive handler structs code
      exceptionShapes baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi
      (decPanClock clock) calleeBody
      (memoryAccess := access) (contracts := contracts) (memoryHandler := mh)
      (evaluator := evaluator) =
        some (.control (.error finalLocals finalGlobals finalMemory finalFfi), calleeClock)) :
    evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptionShapes
      baseAddress topAddress bytesInWord (fuel + 2) locals globals memory ffi clock
      name shape function arguments body (memoryAccess := access) (contracts := contracts)
      (memoryHandler := mh) (evaluator := evaluator) =
        some (.control (.error (fun _ => none) finalGlobals finalMemory finalFfi),
          min (decPanClock clock) calleeClock) := by
  simp [evalPanValueFfiClockCodeDecCall, evalPanValueFfiClockCodeCall, Option.elim_some,
    harguments, hlookup, hclock, hbody, decPanClock]
/-! ### Globals shape stability

Cake's `is_valid_value` (`panSemScript.sml:469-474`) compares `shape_of` only,
so a `Global` call destination is checked against the caller state's binding
shape.  The relation below records that two global maps bind the same names
with the same value shapes.  The intended invariant is that every clocked
code-map evaluation preserves it, which lets the Call clause validate a
`Global` destination against the callee post-state globals exactly as HOL
validates it against the caller state (`panSemScript.sml:657-693`), closing
#1250 report item 7.

What is proved here: every leaf result preserves global shapes
(`panValue*Result_globals_stable`), the leaf dispatcher
(`evalPanValueFfiClockLeaf_globals_stable`), the projection and composition
helpers (`panValueFfiClockGlobalsStable_*`), the validated-update lemma
`assignPanValueCallResult_globals_stable`, the verdict congruence
`panValueAssignmentValid_global_congr`, the fuel induction over the three
mutual evaluators (`evalPanValueFfiClockCode_globals_stable`), its DecCall
corollary (`evalPanValueFfiClockCodeDecCall_globals_stable`), and the
`Global`-destination verdict congruences for Call and DecCall
(`evalPanValueFfiClockCodeCall_global_verdict_congr` and
`evalPanValueFfiClockCodeDecCall_global_verdict_congr`).  The only global
writes are a validated `Global` assignment, a `ShMemLoad` validated against
`.word 0`, and the Call/DecCall `Global` destination, and every other clause
passes the input globals through. -/

/-- Two global maps bind the same names with the same value shapes.  This is
    exactly what `is_valid_value` (`panSemScript.sml:469-474`) can observe,
    since it compares `shape_of` and requires the binding to exist. -/
def panValueGlobalsShapeStable (structs : StructContext)
    (before after : VarName → Option (PanValue α)) : Prop :=
  ∀ name, (before name).map (panValueShape structs) =
    (after name).map (panValueShape structs)

/-- The globals component of a control result. -/
def panValueControlGlobals {α : Type u} {σ : Type v} :
    PanValueFfiControlResult α σ → (VarName → Option (PanValue α))
  | .normal _ globals _ _ => globals
  | .error _ globals _ _ => globals
  | .returned _ globals _ _ _ => globals
  | .raised _ globals _ _ _ _ => globals
  | .broke _ globals _ _ => globals
  | .continued _ globals _ _ => globals
  | .finalFfi _ globals _ _ _ => globals

/-- Every `some` control result keeps the input globals shape-stable.  Stated
    over the result pair so case splits can consume the equation directly. -/
def panValueFfiControlGlobalsStable (structs : StructContext)
    (globals : VarName → Option (PanValue α))
    (result : Option (PanValueFfiControlResult α σ)) : Prop :=
  ∀ r, result = some r →
    panValueGlobalsShapeStable structs globals (panValueControlGlobals r)

/-- The globals component of a clocked outcome. -/
def panValueFfiClockOutcomeGlobals {α : Type u} {σ : Type v} :
    PanValueFfiClockOutcome α σ → (VarName → Option (PanValue α))
  | .control control => panValueControlGlobals control
  | .timeout _ globals _ _ => globals

/-- The globals component of a clocked result. -/
def panValueFfiClockResultGlobals {α : Type u} {σ : Type v}
    (result : PanValueFfiClockResult α σ) : VarName → Option (PanValue α) :=
  panValueFfiClockOutcomeGlobals result.1

/-- Every `some` clocked result keeps the input globals shape-stable. -/
def panValueFfiClockGlobalsStable (structs : StructContext)
    (globals : VarName → Option (PanValue α))
    (result : Option (PanValueFfiClockResult α σ)) : Prop :=
  ∀ r, result = some r →
    panValueGlobalsShapeStable structs globals (panValueFfiClockResultGlobals r)

theorem panValueGlobalsShapeStable_refl (structs : StructContext)
    (globals : VarName → Option (PanValue α)) :
    panValueGlobalsShapeStable structs globals globals := by
  intro name
  rfl

theorem panValueGlobalsShapeStable_symm {structs : StructContext}
    {before after : VarName → Option (PanValue α)}
    (h : panValueGlobalsShapeStable structs before after) :
    panValueGlobalsShapeStable structs after before := by
  intro name
  exact (h name).symm

theorem panValueGlobalsShapeStable_trans {structs : StructContext}
    {first second third : VarName → Option (PanValue α)}
    (h₁ : panValueGlobalsShapeStable structs first second)
    (h₂ : panValueGlobalsShapeStable structs second third) :
    panValueGlobalsShapeStable structs first third := by
  intro name
  exact (h₁ name).trans (h₂ name)

mutual
  theorem panShapeMatches_eq_true_iff (left right : Shape) :
      panShapeMatches left right = true ↔ left = right := by
    cases left with
    | one => cases right <;> simp [panShapeMatches]
    | named name => cases right <;> simp [panShapeMatches]
    | comb fields =>
        cases right with
        | one => simp [panShapeMatches]
        | named name => simp [panShapeMatches]
        | comb otherFields =>
            simp only [panShapeMatches]
            rw [panShapeListMatches_eq_true_iff]
            simp
  theorem panShapeListMatches_eq_true_iff (left right : List Shape) :
      panShapeMatches.panShapeListMatches left right = true ↔ left = right := by
    cases left with
    | nil => cases right <;> simp [panShapeMatches.panShapeListMatches]
    | cons head tail =>
        cases right with
        | nil => simp [panShapeMatches.panShapeListMatches]
        | cons otherHead otherTail =>
            simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true, List.cons.injEq]
            rw [panShapeMatches_eq_true_iff, panShapeListMatches_eq_true_iff]
end

/-- A valid `Global` assignment binds an existing value whose shape matches. -/
theorem panValueAssignmentValid_global_true
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (globals : VarName → Option (PanValue α)) (name : VarName) (value : PanValue α)
    (hvalid : panValueAssignmentValid structs locals globals .global name value = true) :
    ∃ oldValue, globals name = some oldValue ∧
      panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) = true := by
  unfold panValueAssignmentValid at hvalid
  cases hg : globals name with
  | none => simp [hg] at hvalid
  | some oldValue => exact ⟨oldValue, rfl, by simpa [hg] using hvalid⟩

/-- Updating a bound global to a shape-matching value keeps the global map
    shape-stable. -/
theorem panValueGlobalsShapeStable_update_of_match
    (structs : StructContext) (globals : VarName → Option (PanValue α))
    (name : VarName) (newValue oldValue : PanValue α)
    (hold : globals name = some oldValue)
    (hmatch : panShapeMatches (panValueShape structs newValue)
      (panValueShape structs oldValue) = true) :
    panValueGlobalsShapeStable structs globals (updatePanValueMap globals name newValue) := by
  have hshape : panValueShape structs newValue = panValueShape structs oldValue :=
    (panShapeMatches_eq_true_iff _ _).mp hmatch
  intro other
  by_cases hsame : other = name
  · subst hsame
    simp only [updatePanValueMap]
    rw [if_pos (by simp), hold]
    simp [hshape]
  · simp only [updatePanValueMap]
    have hbeq : (other == name) = false := by
      by_cases hb : (other == name) = true
      · exact absurd (by simpa using hb) hsame
      · simpa using hb
    rw [if_neg (by simp [hbeq])]

/-- A valid `Global` assignment keeps the global map shape-stable. -/
theorem panValueGlobalsShapeStable_update_of_valid
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (globals : VarName → Option (PanValue α)) (name : VarName) (value : PanValue α)
    (hvalid : panValueAssignmentValid structs locals globals .global name value = true) :
    panValueGlobalsShapeStable structs globals (updatePanValueMap globals name value) := by
  obtain ⟨oldValue, hold, hmatch⟩ :=
    panValueAssignmentValid_global_true structs locals globals name value hvalid
  exact panValueGlobalsShapeStable_update_of_match structs globals name value oldValue hold hmatch

/-- The `Global` destination verdict of `assignPanValueCallResult` depends only
    on the binding shapes, so validating against shape-stable callee globals is
    the same as validating against the caller globals, exactly as HOL's
    `is_valid_value` does (`panSemScript.sml:469-474`). -/
theorem panValueAssignmentValid_global_congr
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (before after : VarName → Option (PanValue α))
    (hstable : panValueGlobalsShapeStable structs before after)
    (name : VarName) (value : PanValue α) :
    panValueAssignmentValid structs locals after .global name value =
      panValueAssignmentValid structs locals before .global name value := by
  unfold panValueAssignmentValid
  have h := hstable name
  cases hb : before name with
  | none =>
      cases ha : after name with
      | none => simp
      | some value' => simp [hb, ha] at h
  | some oldValue =>
      cases ha : after name with
      | none => simp [hb, ha] at h
      | some newValue =>
          simp only [hb, ha] at h ⊢
          have hshape : panValueShape structs oldValue = panValueShape structs newValue := by
            simpa using h
          rw [← hshape]

/-! ### Leaf results preserve global shapes

Every leaf helper either leaves the globals map untouched or performs a single
validated `Global` assignment (`Assign` and `ShMemLoad`), which preserves the
binding shape by `panValueAssignmentValid`. -/

/-- A `ShMemLoad` `Global` destination is validated against `.word 0`, whose
    shape is the same `.one` as the loaded word, so the update preserves the
    binding shape. -/
theorem panValueGlobalsShapeStable_update_word
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (globals : VarName → Option (PanValue α)) (name : VarName) (value : α)
    (hvalid : panValueAssignmentValid structs locals globals .global name (.word 0) = true) :
    panValueGlobalsShapeStable structs globals (updatePanValueMap globals name (.word value)) := by
  obtain ⟨oldValue, hold, hmatch⟩ :=
    panValueAssignmentValid_global_true structs locals globals name (.word 0) hvalid
  have holdShape : panValueShape structs oldValue = .one := by
    cases hshape : panValueShape structs oldValue with
    | one => rfl
    | named shapeName => simp [panValueShape, panShapeMatches, hshape] at hmatch
    | comb shapeFields => simp [panValueShape, panShapeMatches, hshape] at hmatch
  apply panValueGlobalsShapeStable_update_of_match structs globals name (.word value) oldValue hold
  simp [panValueShape, panShapeMatches, holdShape]

theorem panValueAssignLocalResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueAssignLocalResult structs base top bytes locals globals memory ffi name value
        access evaluator) := by
  intro r h
  simp only [panValueAssignLocalResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some value' =>
      by_cases hvalid : panValueAssignmentValid structs locals globals .local name value' = true
      ·
        simp [h', hvalid, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      ·
        simp [h', hvalid, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueAssignGlobalResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueAssignGlobalResult structs base top bytes locals globals memory ffi name value
        access evaluator) := by
  intro r h
  simp only [panValueAssignGlobalResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some value' =>
      by_cases hvalid : panValueAssignmentValid structs locals globals .global name value' = true
      · simp [h', hvalid] at h
        subst r
        simp only [panValueControlGlobals]
        exact panValueGlobalsShapeStable_update_of_valid structs locals globals name value' hvalid
      ·
        simp [h', hvalid, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValuePrimitiveResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (access : Option (PanValueMemoryAccess α)) (primitive : PanPrimitiveHandler α)
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValuePrimitiveResult structs base top bytes locals globals memory ffi name operator
        arguments access primitive evaluator) := by
  intro r h
  simp only [panValuePrimitiveResult] at h ⊢
  cases h' : evalPanValueExpsWith evaluator structs locals globals memory base top bytes arguments
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some values =>
      cases hprim : primitive operator values with
      | none =>
        simp [h', hprim, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | some value' =>
          cases hloc : locals name with
          | none =>
            simp [h', hprim, hloc, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | some oldValue =>
              by_cases hshape : panShapeMatches (panValueShape structs value')
                (panValueShape structs oldValue) = true
              ·
                simp [h', hprim, hloc, hshape, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
              ·
                simp [h', hprim, hloc, hshape, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueStoreResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (address value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueStoreResult structs base top bytes locals globals memory ffi address value
        access evaluator) := by
  intro r h
  simp only [panValueStoreResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes address
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some address' =>
      cases h2 : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
          access with
      | none =>
        simp [h', h2, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | some value' =>
          cases haddr : address' with
          | word a =>
              cases hstore : panValueStoreWithAccess memory bytes a value' access with
              | none =>
                simp [h', h2, haddr, hstore, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | some memory' =>
                simp [h', h2, haddr, hstore, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | rStruct _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | nStruct _ _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueStore32Result_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (address value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueStore32Result structs base top bytes locals globals memory ffi address value
        access evaluator) := by
  intro r h
  simp only [panValueStore32Result] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes address
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some address' =>
      cases h2 : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
          access with
      | none =>
        simp [h', h2, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | some value' =>
          cases haddr : address' with
          | word a =>
              cases hval : value' with
              | word v =>
                  cases hacc : access with
                  | none =>
                      simp only [hacc] at *
                      simp only [h', h2, haddr, hval, Option.some.injEq] at h
                      subst r
                      simp [panValueControlGlobals, panValueGlobalsShapeStable]
                  | some acc =>
                      cases hstore : acc.store32 acc.domain memory bytes a v with
                      | none =>
                          simp only [hacc] at *
                          simp only [h', h2, haddr, hval, hstore, Option.some.injEq] at h
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
                      | some memory' =>
                          simp only [hacc] at *
                          simp only [h', h2, haddr, hval, hstore, Option.some.injEq] at h
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | rStruct _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | nStruct _ _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | rStruct _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | nStruct _ _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueStoreByteResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (address value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueStoreByteResult structs base top bytes locals globals memory ffi address value
        access evaluator) := by
  intro r h
  simp only [panValueStoreByteResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes address
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some address' =>
      cases h2 : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
          access with
      | none =>
        simp [h', h2, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | some value' =>
          cases haddr : address' with
          | word a =>
              cases hval : value' with
              | word v =>
                  cases hacc : access with
                  | none =>
                      simp only [hacc] at *
                      simp only [h', h2, haddr, hval, Option.some.injEq] at h
                      subst r
                      simp [panValueControlGlobals, panValueGlobalsShapeStable]
                  | some acc =>
                      cases hstore : acc.storeByte acc.domain memory bytes a v with
                      | none =>
                          simp only [hacc] at *
                          simp only [h', h2, haddr, hval, hstore, Option.some.injEq] at h
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
                      | some memory' =>
                          simp only [hacc] at *
                          simp only [h', h2, haddr, hval, hstore, Option.some.injEq] at h
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | rStruct _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | nStruct _ _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | rStruct _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | nStruct _ _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueReturnResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (value : Exp α) (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueReturnResult structs base top bytes locals globals memory ffi value access
        evaluator) := by
  intro r h
  simp only [panValueReturnResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some value' =>
      by_cases hlimit : panValuePayloadWithinLimit structs value' = true
      ·
        simp [h', hlimit, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      ·
        simp [h', hlimit, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueRaiseResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (contracts : Option PanValueCallContracts) (exception : VarName) (value : Exp α)
    (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueRaiseResult structs base top bytes locals globals memory ffi contracts exception
        value access evaluator) := by
  intro r h
  simp only [panValueRaiseResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some value' =>
      by_cases hvalid : panValueExceptionValid structs contracts exception value' = true ∧
          panValuePayloadWithinLimit structs value' = true
      ·
        simp [h', hvalid, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      ·
        simp [h', hvalid, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueShMemStoreResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (address value : Exp α)
    (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueShMemStoreResult context structs base top bytes locals globals memory ffi size
        address value access evaluator) := by
  intro r h
  simp only [panValueShMemStoreResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes address
      access with
  | none =>
    simp [h', Option.some.injEq] at *
    subst r
    simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some address' =>
      cases h2 : evalPanValueExpWith evaluator structs locals globals memory base top bytes value
          access with
      | none =>
        simp [h', h2, Option.some.injEq] at *
        subst r
        simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | some value' =>
          cases haddr : address' with
          | word a =>
              cases hval : value' with
              | word v =>
                  cases hstore : panValueFfiSharedStore context ffi size a v with
                  | none =>
                    simp [h', h2, haddr, hval, hstore, Option.some.injEq] at *
                    subst r
                    simp [panValueControlGlobals, panValueGlobalsShapeStable]
                  | some result =>
                      cases result with
                      | loaded _ _ =>
                          simp [h', h2, haddr, hval, hstore, Option.some.injEq] at *
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
                      | stored nextFfi =>
                          simp [h', h2, haddr, hval, hstore, Option.some.injEq] at *
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
                      | final nextFfi event =>
                          simp [h', h2, haddr, hval, hstore, Option.some.injEq] at *
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | rStruct _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
              | nStruct _ _ =>
                simp [h', h2, haddr, hval, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | rStruct _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
          | nStruct _ _ =>
            simp [h', h2, haddr, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueShMemLoadResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp α)
    (access : Option (PanValueMemoryAccess α))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueShMemLoadResult context structs base top bytes locals globals memory ffi size
        kind name address access evaluator) := by
  intro r h
  simp only [panValueShMemLoadResult] at h ⊢
  cases h' : evalPanValueExpWith evaluator structs locals globals memory base top bytes address
      access with
  | none =>
      simp [h', Option.some.injEq] at *
      subst r
      simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | some address' =>
      cases haddr : address' with
      | word a =>
          by_cases hvalid : panValueSharedLoadValid structs locals globals kind name (.word 0) =
            true
          · cases hload : panValueFfiSharedLoad context ffi size a with
            | none =>
                simp [h', haddr, hvalid, hload, Option.some.injEq] at *
                subst r
                simp [panValueControlGlobals, panValueGlobalsShapeStable]
            | some result =>
                cases result with
                | loaded nextFfi value' =>
                    cases kind with
                    | «local» =>
                        simp [h', haddr, hvalid, hload, Option.some.injEq] at *
                        subst r
                        simp [panValueControlGlobals, panValueGlobalsShapeStable]
                    | «global» =>
                        simp [h', haddr, hvalid, hload] at h
                        subst r
                        simp only [panValueControlGlobals]
                        have hassign : panValueAssignmentValid structs locals globals .global
                            name (.word 0) = true := by
                          simpa [panValueSharedLoadValid] using hvalid
                        exact panValueGlobalsShapeStable_update_word structs locals globals
                          name value' hassign
                | stored _ =>
                    simp [h', haddr, hvalid, hload, Option.some.injEq] at *
                    subst r
                    simp [panValueControlGlobals, panValueGlobalsShapeStable]
                | final nextFfi event =>
                    simp [h', haddr, hvalid, hload, Option.some.injEq] at *
                    subst r
                    simp [panValueControlGlobals, panValueGlobalsShapeStable]
          · simp [h', haddr, hvalid, Option.some.injEq] at *
            subst r
            simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | rStruct _ =>
          simp [h', haddr, Option.some.injEq] at *
          subst r
          simp [panValueControlGlobals, panValueGlobalsShapeStable]
      | nStruct _ _ =>
          simp [h', haddr, Option.some.injEq] at *
          subst r
          simp [panValueControlGlobals, panValueGlobalsShapeStable]

theorem panValueFfiExtCallResult_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext) (base top bytes : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (access : Option (PanValueMemoryAccess α))
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiControlGlobalsStable structs globals
      (panValueFfiExtCallResult context handler structs base top bytes locals globals memory ffi
        function configuration configurationLength array arrayLength access mh evaluator) := by
  intro r h
  simp only [panValueFfiExtCallResult] at h ⊢
  cases h' : evalPanValueExpsWith evaluator structs locals globals memory base top bytes
      [configuration, configurationLength, array, arrayLength] access with
  | none => simp [h', Option.some.injEq] at *; subst r; simp [panValueControlGlobals,
      panValueGlobalsShapeStable]
  | some values =>
      cases values with
      | nil => simp [h', Option.some.injEq] at *; subst r; simp [panValueControlGlobals,
          panValueGlobalsShapeStable]
      | cons v1 rest =>
          cases rest with
          | nil => simp [h', Option.some.injEq] at *; subst r; simp [panValueControlGlobals,
              panValueGlobalsShapeStable]
          | cons v2 rest2 =>
              cases rest2 with
              | nil => simp [h', Option.some.injEq] at *; subst r; simp
                  [panValueControlGlobals, panValueGlobalsShapeStable]
              | cons v3 rest3 =>
                  cases rest3 with
                  | nil =>
                      simp [h', Option.some.injEq] at *
                      subst r
                      simp [panValueControlGlobals, panValueGlobalsShapeStable]
                  | cons v4 rest4 =>
                      cases rest4 with
                      | cons _ _ =>
                          simp [h', Option.some.injEq] at *
                          subst r
                          simp [panValueControlGlobals, panValueGlobalsShapeStable]
                      | nil =>
                          cases v1 <;> cases v2 <;> cases v3 <;> cases v4
                          all_goals
                            try simp [h', Option.some.injEq] at *
                            try subst r
                            try simp only [panValueControlGlobals]
                            try exact panValueGlobalsShapeStable_refl structs globals
                          rename_i wordValue3 wordValue2 wordValue1 wordValue
                          cases mh with
                          | none =>
                              cases access with
                              | none =>
                                  cases hhandler : handler function wordValue3 wordValue2
                                      wordValue1 wordValue locals ffi with
                                  | none => simp_all
                                  | some pair =>
                                      obtain ⟨locals', ffi'⟩ := pair
                                      simp_all
                                      subst r
                                      exact panValueGlobalsShapeStable_refl structs globals
                              | some acc =>
                                  cases hext : panValueFfiExtCall acc context memory bytes
                                      ffi function wordValue3 wordValue2 wordValue1 wordValue with
                                  | none =>
                                      simp_all
                                      subst r
                                      exact panValueGlobalsShapeStable_refl structs globals
                                  | some result =>
                                      cases result with
                                      | returned memory' ffi' =>
                                          simp_all
                                          subst r
                                          exact panValueGlobalsShapeStable_refl structs globals
                                      | final ffi' event =>
                                          simp_all
                                          subst r
                                          exact panValueGlobalsShapeStable_refl structs globals
                          | some handler' =>
                              cases hres : handler' function wordValue3 wordValue2 wordValue1
                                  wordValue locals memory ffi with
                              | some triple =>
                                  obtain ⟨locals', memory', ffi'⟩ := triple
                                  simp_all
                                  subst r
                                  exact panValueGlobalsShapeStable_refl structs globals
                              | none =>
                                  cases access with
                                  | none =>
                                      cases hhandler : handler function wordValue3 wordValue2
                                          wordValue1 wordValue locals ffi with
                                      | none => simp_all
                                      | some pair =>
                                          obtain ⟨locals', ffi'⟩ := pair
                                          simp_all
                                          subst r
                                          exact panValueGlobalsShapeStable_refl structs globals
                                  | some acc =>
                                      cases hext : panValueFfiExtCall acc context memory bytes
                                          ffi function wordValue3 wordValue2 wordValue1
                                          wordValue with
                                      | none =>
                                          simp_all
                                          subst r
                                          exact panValueGlobalsShapeStable_refl structs globals
                                      | some result =>
                                          cases result with
                                          | returned memory' ffi' =>
                                              simp_all
                                              subst r
                                              exact panValueGlobalsShapeStable_refl structs globals
                                          | final ffi' event =>
                                              simp_all
                                              subst r
                                              exact panValueGlobalsShapeStable_refl structs globals

/-- A clocked leaf result is the control result at the unchanged clock, so a
    control-level globals-stability fact lifts to the clocked result. -/
theorem panValueFfiClockGlobalsStable_none
    (structs : StructContext) (globals : VarName → Option (PanValue α)) :
    panValueFfiClockGlobalsStable (α := α) (σ := σ) structs globals none := by
  intro r hr
  simp at hr

/-- The `some`-result normalisation for globals stability: a clocked result
    `(outcome, clock)` keeps the input globals shape-stable exactly when the
    outcome's globals component does. -/
theorem panValueFfiClockGlobalsStable_some_iff
    (structs : StructContext) (globals : VarName → Option (PanValue α))
    (outcome : PanValueFfiClockOutcome α σ) (clock : Nat) :
    panValueFfiClockGlobalsStable structs globals (some (outcome, clock)) ↔
      panValueGlobalsShapeStable structs globals (panValueFfiClockOutcomeGlobals outcome) := by
  constructor
  · intro h
    simpa [panValueFfiClockResultGlobals] using h (outcome, clock) rfl
  · intro h r hr
    obtain ⟨nextOutcome, nextClock⟩ := r
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨hnext, _⟩ := hr
    subst nextOutcome
    simpa [panValueFfiClockResultGlobals] using h

/-- Restoring an old local binding keeps the outcome's globals component. -/
theorem panValueFfiClockOutcomeGlobals_restoreLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α))
    (outcome : PanValueFfiClockOutcome α σ) :
    panValueFfiClockOutcomeGlobals (panValueFfiClockRestoreLocal name oldValue outcome) =
      panValueFfiClockOutcomeGlobals outcome := by
  cases outcome with
  | control result => cases result <;> rfl
  | timeout locals globals memory ffi => rfl

/-- A clocked result whose outcome had a local binding restored keeps the input
    globals shape-stable. -/
theorem panValueFfiClockGlobalsStable_some_restoreLocal [BEq String]
    (structs : StructContext) (globals : VarName → Option (PanValue α))
    (name : VarName) (oldValue : Option (PanValue α))
    (outcome : PanValueFfiClockOutcome α σ) (clock : Nat)
    (h : panValueGlobalsShapeStable structs globals (panValueFfiClockOutcomeGlobals outcome)) :
    panValueFfiClockGlobalsStable structs globals
      (some (panValueFfiClockRestoreLocal name oldValue outcome, clock)) := by
  intro r hr
  obtain ⟨nextOutcome, nextClock⟩ := r
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨hnext, _⟩ := hr
  subst nextOutcome
  simp only [panValueFfiClockResultGlobals]
  rw [panValueFfiClockOutcomeGlobals_restoreLocal]
  exact h

/-- Composing two globals-stability facts through an intermediate clocked
    result. -/
theorem panValueFfiClockGlobalsStable_trans
    {structs : StructContext} {globals : VarName → Option (PanValue α)}
    {first : PanValueFfiClockResult α σ}
    (hfirst : panValueGlobalsShapeStable structs globals (panValueFfiClockResultGlobals first))
    {second : Option (PanValueFfiClockResult α σ)}
    (hsecond : panValueFfiClockGlobalsStable structs (panValueFfiClockResultGlobals first)
      second) :
    panValueFfiClockGlobalsStable structs globals second := by
  intro r hr
  exact panValueGlobalsShapeStable_trans hfirst (hsecond r hr)

/-- A successful `assignPanValueCallResult` keeps the callee post-state globals
    shape-stable: the `local` and empty-value clauses return the input globals,
    and the `global` clause performs a validated update. -/
theorem assignPanValueCallResult_globals_stable
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (destination : Option (VarKind × VarName)) (values : List (PanValue α))
    (callerLocals callerGlobals : VarName → Option (PanValue α))
    (h : assignPanValueCallResult locals globals destination values (structs := structs) =
      some (callerLocals, callerGlobals)) :
    panValueGlobalsShapeStable structs globals callerGlobals := by
  cases destination with
  | none =>
      cases values with
      | nil =>
          simp only [assignPanValueCallResult, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, hglobals⟩ := h
          subst callerGlobals
          exact panValueGlobalsShapeStable_refl structs globals
      | cons value rest =>
          cases rest with
          | nil =>
              simp only [assignPanValueCallResult, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, hglobals⟩ := h
              subst callerGlobals
              exact panValueGlobalsShapeStable_refl structs globals
          | cons value' rest' => simp [assignPanValueCallResult] at h
  | some destination =>
      obtain ⟨kind, name⟩ := destination
      cases values with
      | nil => simp [assignPanValueCallResult] at h
      | cons value rest =>
          cases rest with
          | nil =>
              cases kind with
              | «local» =>
                  by_cases hvalid : panValueAssignmentValid structs locals (fun _ => none)
                    .local name value
                  · simp [assignPanValueCallResult, hvalid] at h
                    obtain ⟨_, hglobals⟩ := h
                    subst callerGlobals
                    exact panValueGlobalsShapeStable_refl structs globals
                  · simp [assignPanValueCallResult, hvalid] at h
              | «global» =>
                  by_cases hvalid : panValueAssignmentValid structs locals globals
                    .global name value
                  · simp [assignPanValueCallResult, hvalid] at h
                    obtain ⟨_, hglobals⟩ := h
                    subst callerGlobals
                    exact panValueGlobalsShapeStable_update_of_valid structs locals globals name
                      value hvalid
                  · simp [assignPanValueCallResult, hvalid] at h
          | cons value' rest' => simp [assignPanValueCallResult] at h

theorem panValueFfiClockGlobalsStable_map_control
    (structs : StructContext) (globals : VarName → Option (PanValue α)) (clock : Nat)
    (result : Option (PanValueFfiControlResult α σ))
    (h : panValueFfiControlGlobalsStable structs globals result) :
    panValueFfiClockGlobalsStable structs globals
      (result.map (fun control => (.control control, clock))) := by
  intro r hr
  obtain ⟨outcome, resultClock⟩ := r
  cases hres : result with
  | none => simp [hres] at hr
  | some control =>
      simp only [hres, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨houtcome, _⟩ := hr
      subst outcome
      exact h control hres

/-- Every leaf result keeps the input globals shape-stable.  The leaf clauses
    either leave globals untouched or perform a validated `Global` assignment,
    so the per-leaf control lemmas lift through `evalPanValueFfiClockLeaf`. -/
theorem evalPanValueFfiClockLeaf_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (base top bytes : α) (clock : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (program : Prog α)
    (access : Option (PanValueMemoryAccess α)) (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (evaluator : Option (PanExprEvaluator α) := none) :
    panValueFfiClockGlobalsStable structs globals
      (evalPanValueFfiClockLeaf context primitive handler structs base top bytes clock locals
        globals memory ffi program access contracts mh evaluator) := by
  cases program with
  | skip =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      intro r hr
      simp only [Option.some.injEq] at hr
      subst r
      simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | «break» =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      intro r hr
      simp only [Option.some.injEq] at hr
      subst r
      simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | «continue» =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      intro r hr
      simp only [Option.some.injEq] at hr
      subst r
      simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | annot tag text =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      intro r hr
      simp only [Option.some.injEq] at hr
      subst r
      simp [panValueControlGlobals, panValueGlobalsShapeStable]
  | assign kind name value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      cases kind with
      | «local» =>
          exact panValueAssignLocalResult_globals_stable structs base top bytes locals globals
            memory ffi name value access evaluator
      | «global» =>
          exact panValueAssignGlobalResult_globals_stable structs base top bytes locals globals
            memory ffi name value access evaluator
  | primitive name operator args =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValuePrimitiveResult_globals_stable structs base top bytes locals globals memory
        ffi name operator args access primitive evaluator
  | store address value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueStoreResult_globals_stable structs base top bytes locals globals memory ffi
        address value access evaluator
  | store32 address value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueStore32Result_globals_stable structs base top bytes locals globals memory
        ffi address value access evaluator
  | storeByte address value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueStoreByteResult_globals_stable structs base top bytes locals globals memory
        ffi address value access evaluator
  | extCall function configuration configurationLength array arrayLength =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueFfiExtCallResult_globals_stable context handler structs base top bytes locals
        globals memory ffi function configuration configurationLength array arrayLength access mh
        evaluator
  | «return» value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueReturnResult_globals_stable structs base top bytes locals globals memory ffi
        value access evaluator
  | «raise» exception expression =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueRaiseResult_globals_stable structs base top bytes locals globals memory ffi
        contracts exception expression access evaluator
  | shMemLoad size kind name address =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueShMemLoadResult_globals_stable context structs base top bytes locals globals
        memory ffi size kind name address access evaluator
  | shMemStore size address value =>
      simp only [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl]
      apply panValueFfiClockGlobalsStable_map_control
      exact panValueShMemStoreResult_globals_stable context structs base top bytes locals globals
        memory ffi size address value access evaluator
  | tick => simp [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl,
      panValueFfiClockGlobalsStable]
  | dec name shape value body => simp [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl,
      panValueFfiClockGlobalsStable]
  | seq first second => simp [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl,
      panValueFfiClockGlobalsStable]
  | ite condition thenBranch elseBranch => simp [evalPanValueFfiClockLeaf,
      evalPanValueFfiLeafControl, panValueFfiClockGlobalsStable]
  | «while» conditionExp body => simp [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl,
      panValueFfiClockGlobalsStable]
  | call info function arguments => simp [evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl,
      panValueFfiClockGlobalsStable]
  | decCall name shape function arguments body => simp [evalPanValueFfiClockLeaf,
      evalPanValueFfiLeafControl, panValueFfiClockGlobalsStable]

local macro "globals_stable_refl" : tactic =>
  `(tactic| simp [Option.pure_def, panValueFfiClockGlobalsStable_some_iff,
    panValueFfiClockOutcomeGlobals, panValueFfiClockResultGlobals,
    panValueControlGlobals, panValueGlobalsShapeStable])

local macro "globals_stable_hb" h:term : tactic =>
  `(tactic| simpa [Option.pure_def, panValueFfiClockGlobalsStable_some_iff,
    panValueFfiClockOutcomeGlobals, panValueFfiClockResultGlobals,
    panValueControlGlobals] using $h)

/-- Every `some` result of the fuel-indexed code-map evaluator keeps the input
    globals shape-stable: each clause passes the input globals through, performs
    a validated `Global` assignment, or recurses on globals that are already
    shape-stable.  This is the evaluator-level induction behind the
    `Global`-destination verdict congruence; it is stated for an arbitrary
    expression evaluator because expression evaluation never touches the clock
    or the globals map. -/
theorem evalPanValueFfiClockCode_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ)) :
    ∀ fuel,
      (∀ locals globals memory ffi clock info function arguments preserve
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockGlobalsStable structs globals
          (evalPanValueFfiClockCodeCall context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock info function arguments
            access contracts mh preserve evaluator)) ∧
      (∀ locals globals memory ffi clock name shape function arguments body
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockGlobalsStable structs globals
          (evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock name shape function arguments
            body access contracts mh evaluator)) ∧
      (∀ locals globals memory ffi clock program
          (evaluator : Option (PanExprEvaluator α)),
        panValueFfiClockGlobalsStable structs globals
          (evalPanValueFfiClockCodeProg context primitive handler structs code exceptions
            base top bytes fuel locals globals memory ffi clock program access contracts mh
            evaluator)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;>
        intro <;>
        simp [evalPanValueFfiClockCodeCall, evalPanValueFfiClockCodeDecCall,
          evalPanValueFfiClockCodeProg, panValueFfiClockGlobalsStable]
  | succ fuel ih =>
      obtain ⟨ihCall, ihDecCall, ihProg⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro locals globals memory ffi clock info function arguments preserve evaluator
        simp only [evalPanValueFfiClockCodeCall]
        cases hargs : panValueCallArgumentsValue structs base top bytes locals globals memory
            arguments access evaluator with
        | none =>
            simp only [Option.elim_none, Option.pure_def]
            globals_stable_refl
        | some argValues =>
            simp only [Option.elim_some]
            cases hlook : lookupPanSemCodeCall structs code function argValues with
            | none =>
                simp only [Option.elim_none, Option.pure_def]
                globals_stable_refl
            | some codeTarget =>
                simp only [Option.elim_some]
                obtain ⟨body, returnShape, calleeLocals⟩ := codeTarget
                split
                next =>
                    simp only [panValueFfiClockTimeout, Option.pure_def]
                    globals_stable_refl
                next hclock =>
                  cases hrec : evalPanValueFfiClockCodeProg context primitive handler structs
                      code exceptions base top bytes fuel calleeLocals globals memory ffi
                      (decPanClock clock) body access contracts mh evaluator with
                  | none => exact panValueFfiClockGlobalsStable_none structs globals
                  | some step =>
                      obtain ⟨callOutcome, callClock⟩ := step
                      have hb := ihProg calleeLocals globals memory ffi (decPanClock clock)
                        body evaluator
                      rw [hrec] at hb
                      rw [panValueFfiClockGlobalsStable_some_iff] at hb
                      simp only [Option.bind_eq_bind, Option.bind_some]
                      cases callOutcome with
                      | timeout timeoutLocals timeoutGlobals timeoutMemory timeoutFfi =>
                          simp only [Option.pure_def]
                          globals_stable_hb hb
                      | control result =>
                          cases result with
                          | normal calleeLocals' calleeGlobals' calleeMemory' calleeFfi' =>
                              simp only [Option.pure_def]
                              globals_stable_hb hb
                          | broke calleeLocals' calleeGlobals' calleeMemory' calleeFfi' =>
                              simp only [Option.pure_def]
                              globals_stable_hb hb
                          | continued calleeLocals' calleeGlobals' calleeMemory' calleeFfi' =>
                              simp only [Option.pure_def]
                              globals_stable_hb hb
                          | error calleeLocals' calleeGlobals' calleeMemory' calleeFfi' =>
                              simp only [Option.pure_def]
                              globals_stable_hb hb
                          | returned calleeLocals' calleeGlobals' calleeMemory' calleeFfi'
                              values =>
                              simp only [Option.pure_def]
                              cases values with
                              | nil => globals_stable_hb hb
                              | cons value rest =>
                                  cases rest with
                                  | nil =>
                                      by_cases hvalid :
                                          panShapeMatches (panValueShape structs value)
                                            returnShape = true
                                      · rw [if_pos hvalid]
                                        cases info with
                                        | none => globals_stable_hb hb
                                        | some info' =>
                                            obtain ⟨destination, _⟩ := info'
                                            cases hassign : assignPanValueCallResult locals
                                                calleeGlobals' destination [value]
                                                (structs := structs) with
                                            | none =>
                                                simp only [hassign]
                                                globals_stable_hb hb
                                            | some caller =>
                                                obtain ⟨callerLocals', callerGlobals'⟩ := caller
                                                simp only [hassign,
                                                  panValueFfiClockGlobalsStable_some_iff,
                                                  panValueFfiClockOutcomeGlobals,
                                                  panValueControlGlobals]
                                                exact panValueGlobalsShapeStable_trans hb
                                                  (assignPanValueCallResult_globals_stable structs
                                                    locals calleeGlobals' destination [value]
                                                    callerLocals' callerGlobals' hassign)
                                      · rw [if_neg hvalid]
                                        globals_stable_hb hb
                                  | cons value' rest' => globals_stable_hb hb
                          | raised calleeLocals' calleeGlobals' calleeMemory' calleeFfi'
                              exception value =>
                              simp only [Option.pure_def]
                              cases info with
                              | none => globals_stable_hb hb
                              | some info' =>
                                  obtain ⟨_, exceptionInfo⟩ := info'
                                  cases exceptionInfo with
                                  | none => globals_stable_hb hb
                                  | some exceptionInfo' =>
                                      obtain ⟨caught, handlerVariable, handlerProgram⟩ :=
                                        exceptionInfo'
                                      simp only []
                                      by_cases hcaught : (caught == exception) = true
                                      · rw [if_pos hcaught]
                                        cases hexs : exceptions exception with
                                        | none => globals_stable_hb hb
                                        | some shape =>
                                            simp only []
                                            by_cases hcond :
                                                (panShapeMatches (panValueShape structs value)
                                                    shape &&
                                                  panValueAssignmentValid structs locals
                                                    (fun _ => none) .local handlerVariable
                                                    value) = true
                                            · rw [if_pos hcond]
                                              cases hhandler :
                                                      evalPanValueFfiClockCodeProg context primitive
                                                        handler structs code exceptions base top
                                                        bytes fuel
                                                        (updatePanValueMap locals handlerVariable
                                                          value)
                                                        calleeGlobals' calleeMemory' calleeFfi'
                                                        (min (decPanClock clock) callClock)
                                                        handlerProgram access contracts mh
                                                        evaluator with
                                                  | none =>
                                                      exact panValueFfiClockGlobalsStable_none
                                                        structs globals
                                                  | some step2 =>
                                                      obtain ⟨handlerOutcome, handlerClock⟩ :=
                                                        step2
                                                      have hb2 := ihProg
                                                        (updatePanValueMap locals handlerVariable
                                                          value)
                                                        calleeGlobals' calleeMemory' calleeFfi'
                                                        (min (decPanClock clock) callClock)
                                                        handlerProgram evaluator
                                                      rw [hhandler] at hb2
                                                      exact panValueFfiClockGlobalsStable_trans
                                                        (first :=
                                                          ((PanValueFfiClockOutcome.control
                                                            (PanValueFfiControlResult.raised
                                                              calleeLocals' calleeGlobals'
                                                              calleeMemory' calleeFfi'
                                                              exception value), callClock)))
                                                        hb hb2
                                            · rw [if_neg hcond]
                                              globals_stable_hb hb
                                      · rw [if_neg hcaught]
                                        globals_stable_hb hb
                          | finalFfi calleeLocals' calleeGlobals' calleeMemory' calleeFfi' event =>
                              simp only [Option.pure_def]
                              globals_stable_hb hb
      · intro locals globals memory ffi clock name shape function arguments body evaluator
        simp only [evalPanValueFfiClockCodeDecCall]
        cases hcall : evalPanValueFfiClockCodeCall context primitive handler structs code
            exceptions base top bytes fuel locals globals memory ffi clock none function
            arguments access contracts mh true evaluator with
        | none => exact panValueFfiClockGlobalsStable_none structs globals
        | some step =>
            obtain ⟨callOutcome, callClock⟩ := step
            have hb := ihCall locals globals memory ffi clock none function arguments true evaluator
            rw [hcall] at hb
            rw [panValueFfiClockGlobalsStable_some_iff] at hb
            simp only [Option.bind_eq_bind, Option.bind_some]
            cases callOutcome with
            | timeout nextLocals nextGlobals nextMemory nextFfi =>
                simp only [Option.pure_def]
                globals_stable_hb hb
            | control result =>
                cases result with
                | returned nextLocals nextGlobals nextMemory nextFfi values =>
                    simp only [Option.pure_def]
                    cases values with
                    | nil => exact panValueFfiClockGlobalsStable_none structs globals
                    | cons value rest =>
                        cases rest with
                        | nil =>
                            simp only []
                            by_cases hvalid :
                                panShapeMatches (panValueShape structs value) shape = true
                            · rw [if_pos hvalid]
                              cases hcont : evalPanValueFfiClockCodeProg context primitive
                                    handler structs code exceptions base top bytes fuel
                                    (updatePanValueMap locals name value) nextGlobals nextMemory
                                    nextFfi callClock body access contracts mh evaluator with
                                | none => exact panValueFfiClockGlobalsStable_none structs globals
                                | some step2 =>
                                    obtain ⟨bodyOutcome, bodyClock⟩ := step2
                                    have hb2 := ihProg (updatePanValueMap locals name value)
                                      nextGlobals nextMemory nextFfi callClock body evaluator
                                    rw [hcont] at hb2
                                    simp only [Option.bind_some]
                                    exact panValueFfiClockGlobalsStable_some_restoreLocal structs
                                      globals name (locals name) bodyOutcome bodyClock
                                      (panValueGlobalsShapeStable_trans hb
                                        (hb2 (bodyOutcome, bodyClock) rfl))
                            · rw [if_neg hvalid]
                              globals_stable_hb hb
                        | cons value' rest' =>
                            exact panValueFfiClockGlobalsStable_none structs globals
                | raised nextLocals nextGlobals nextMemory nextFfi exception value =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
                | normal nextLocals nextGlobals nextMemory nextFfi =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
                | broke nextLocals nextGlobals nextMemory nextFfi =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
                | continued nextLocals nextGlobals nextMemory nextFfi =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
                | error nextLocals nextGlobals nextMemory nextFfi =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
                | finalFfi nextLocals nextGlobals nextMemory nextFfi event =>
                    simp only [Option.pure_def]
                    globals_stable_hb hb
      · intro locals globals memory ffi clock program evaluator
        cases program with
        | skip =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi .skip access contracts mh evaluator
        | «break» =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi .break access contracts mh evaluator
        | «continue» =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi .continue access contracts mh
              evaluator
        | annot tag text =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.annot tag text) access contracts mh
              evaluator
        | assign kind name value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.assign kind name value) access
              contracts mh evaluator
        | primitive name operator args =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.primitive name operator args)
              access contracts mh evaluator
        | store address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.store address value) access
              contracts mh evaluator
        | store32 address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.store32 address value) access
              contracts mh evaluator
        | storeByte address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.storeByte address value) access
              contracts mh evaluator
        | extCall function configuration configurationLength array arrayLength =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi
              (.extCall function configuration configurationLength array arrayLength) access
              contracts mh evaluator
        | «return» value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.return value) access contracts mh
              evaluator
        | shMemLoad size kind name address =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.shMemLoad size kind name address)
              access contracts mh evaluator
        | shMemStore size address value =>
            simp only [evalPanValueFfiClockCodeProg]
            exact evalPanValueFfiClockLeaf_globals_stable context primitive handler structs
              base top bytes clock locals globals memory ffi (.shMemStore size address value)
              access contracts mh evaluator
        | dec name shape value body =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hdecAccept : panValueDecAcceptedValue structs base top bytes locals globals
                memory value access shape evaluator with
            | none =>
                simp only [Option.elim_none, Option.pure_def]
                globals_stable_refl
            | some evaluated =>
                simp only [Option.elim_some]
                cases hrec : evalPanValueFfiClockCodeProg context primitive handler structs code
                    exceptions base top bytes fuel (updatePanValueMap locals name evaluated) globals
                    memory ffi clock body access contracts mh evaluator with
                | none => exact panValueFfiClockGlobalsStable_none structs globals
                | some step =>
                    obtain ⟨nextOutcome, nextClock⟩ := step
                    have hb := ihProg (updatePanValueMap locals name evaluated) globals memory
                      ffi clock body evaluator
                    rw [hrec] at hb
                    exact panValueFfiClockGlobalsStable_some_restoreLocal structs globals name
                      (locals name) nextOutcome nextClock (hb (nextOutcome, nextClock) rfl)
        | seq first second =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hfirst : evalPanValueFfiClockCodeProg context primitive handler structs code
                exceptions base top bytes fuel locals globals memory ffi clock first access
                contracts mh evaluator with
            | none => exact panValueFfiClockGlobalsStable_none structs globals
            | some step =>
                obtain ⟨firstOutcome, firstClock⟩ := step
                have hb := ihProg locals globals memory ffi clock first evaluator
                rw [hfirst] at hb
                rw [panValueFfiClockGlobalsStable_some_iff] at hb
                simp only [Option.bind_eq_bind, Option.bind_some]
                simp only [Option.pure_def]
                cases firstOutcome with
                | timeout firstLocals firstGlobals firstMemory firstFfi =>
                    globals_stable_hb hb
                | control result =>
                    cases result with
                    | normal nextLocals' nextGlobals' nextMemory' nextFfi' =>
                        simp only []
                        cases hsecond : evalPanValueFfiClockCodeProg context primitive handler
                            structs code exceptions base top bytes fuel nextLocals' nextGlobals'
                            nextMemory' nextFfi' (min clock firstClock) second access contracts mh
                            evaluator with
                        | none => exact panValueFfiClockGlobalsStable_none structs globals
                        | some step2 =>
                            obtain ⟨secondOutcome, secondClock⟩ := step2
                            have hb2 := ihProg nextLocals' nextGlobals' nextMemory' nextFfi'
                              (min clock firstClock) second evaluator
                            rw [hsecond] at hb2
                            rw [panValueFfiClockGlobalsStable_some_iff] at hb2
                            rw [panValueFfiClockGlobalsStable_some_iff]
                            exact panValueGlobalsShapeStable_trans hb hb2
                    | broke nextLocals' nextGlobals' nextMemory' nextFfi' =>
                        simp only []
                        globals_stable_hb hb
                    | continued nextLocals' nextGlobals' nextMemory' nextFfi' =>
                        simp only []
                        globals_stable_hb hb
                    | error nextLocals' nextGlobals' nextMemory' nextFfi' =>
                        simp only []
                        globals_stable_hb hb
                    | returned nextLocals' nextGlobals' nextMemory' nextFfi' values =>
                        simp only []
                        globals_stable_hb hb
                    | raised nextLocals' nextGlobals' nextMemory' nextFfi' exception value =>
                        simp only []
                        globals_stable_hb hb
                    | finalFfi nextLocals' nextGlobals' nextMemory' nextFfi' event =>
                        simp only []
                        globals_stable_hb hb
        | ite condition thenBranch elseBranch =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hcond : panValueIteConditionValue structs base top bytes locals globals memory
                condition access evaluator with
            | none =>
                simp only [Option.elim_none, Option.pure_def]
                globals_stable_refl
            | some conditionValue =>
                simp only [Option.elim_some]
                split
                next => exact ihProg locals globals memory ffi clock thenBranch evaluator
                next => exact ihProg locals globals memory ffi clock elseBranch evaluator
        | call info function arguments =>
            simp only [evalPanValueFfiClockCodeProg]
            exact ihCall locals globals memory ffi clock info function arguments false evaluator
        | decCall name shape function arguments body =>
            simp only [evalPanValueFfiClockCodeProg]
            exact ihDecCall locals globals memory ffi clock name shape function arguments body
              evaluator
        | raise exception expression =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hexp : evalPanValueExpWith evaluator structs locals globals memory base top bytes
                expression access with
            | none =>
                simp only [Option.pure_def]
                globals_stable_refl
            | some value =>
                simp only [Option.pure_def]
                cases hexs : exceptions exception with
                | none => globals_stable_refl
                | some shape =>
                    simp only []
                    by_cases hcond :
                        (panShapeMatches (panValueShape structs value) shape &&
                          panValuePayloadWithinLimit structs value) = true
                    · rw [if_pos hcond]
                      globals_stable_refl
                    · rw [if_neg hcond]
                      globals_stable_refl
        | «while» conditionExp body =>
            simp only [evalPanValueFfiClockCodeProg]
            cases hcond : panValueIteConditionValue structs base top bytes locals globals memory
                conditionExp access evaluator with
            | none =>
                simp only [Option.elim_none, Option.pure_def]
                globals_stable_refl
            | some conditionValue =>
                simp only [Option.elim_some]
                split
                next =>
                    simp only [Option.pure_def]
                    globals_stable_refl
                next =>
                    split
                    next =>
                        simp only [panValueFfiClockTimeout, Option.pure_def]
                        globals_stable_refl
                    next =>
                        cases hbody : evalPanValueFfiClockCodeProg context primitive handler
                            structs code exceptions base top bytes fuel locals globals memory ffi
                            (decPanClock clock) body access contracts mh evaluator with
                        | none => exact panValueFfiClockGlobalsStable_none structs globals
                        | some step =>
                            obtain ⟨bodyOutcome, bodyClock⟩ := step
                            have hb := ihProg locals globals memory ffi (decPanClock clock) body
                              evaluator
                            rw [hbody] at hb
                            rw [panValueFfiClockGlobalsStable_some_iff] at hb
                            simp only [Option.bind_eq_bind, Option.bind_some]
                            simp only [Option.pure_def]
                            cases bodyOutcome with
                            | timeout bodyLocals bodyGlobals bodyMemory bodyFfi =>
                                globals_stable_hb hb
                            | control result =>
                                cases result with
                                | normal nextLocals' nextGlobals' nextMemory' nextFfi' =>
                                    simp only []
                                    cases hrec : evalPanValueFfiClockCodeProg context primitive
                                        handler structs code exceptions base top bytes fuel
                                        nextLocals' nextGlobals' nextMemory' nextFfi'
                                        (min (decPanClock clock) bodyClock)
                                        (.while conditionExp body) access contracts mh evaluator
                                        with
                                    | none =>
                                        exact panValueFfiClockGlobalsStable_none structs globals
                                    | some step2 =>
                                        obtain ⟨whileOutcome, whileClock⟩ := step2
                                        have hb2 := ihProg nextLocals' nextGlobals' nextMemory'
                                          nextFfi' (min (decPanClock clock) bodyClock)
                                          (.while conditionExp body) evaluator
                                        rw [hrec] at hb2
                                        rw [panValueFfiClockGlobalsStable_some_iff] at hb2
                                        rw [panValueFfiClockGlobalsStable_some_iff]
                                        exact panValueGlobalsShapeStable_trans hb hb2
                                | continued nextLocals' nextGlobals' nextMemory' nextFfi' =>
                                    simp only []
                                    cases hrec : evalPanValueFfiClockCodeProg context primitive
                                        handler structs code exceptions base top bytes fuel
                                        nextLocals' nextGlobals' nextMemory' nextFfi'
                                        (min (decPanClock clock) bodyClock)
                                        (.while conditionExp body) access contracts mh evaluator
                                        with
                                    | none =>
                                        exact panValueFfiClockGlobalsStable_none structs globals
                                    | some step2 =>
                                        obtain ⟨whileOutcome, whileClock⟩ := step2
                                        have hb2 := ihProg nextLocals' nextGlobals' nextMemory'
                                          nextFfi' (min (decPanClock clock) bodyClock)
                                          (.while conditionExp body) evaluator
                                        rw [hrec] at hb2
                                        rw [panValueFfiClockGlobalsStable_some_iff] at hb2
                                        rw [panValueFfiClockGlobalsStable_some_iff]
                                        exact panValueGlobalsShapeStable_trans hb hb2
                                | broke nextLocals' nextGlobals' nextMemory' nextFfi' =>
                                    simp only []
                                    globals_stable_hb hb
                                | _ =>
                                    simp only []
                                    globals_stable_hb hb
        | tick =>
            simp only [evalPanValueFfiClockCodeProg]
            split
            next =>
                simp only [panValueFfiClockTimeout, Option.pure_def]
                globals_stable_refl
            next =>
                simp only [Option.pure_def]
                globals_stable_refl

/-- The fuel induction's `DecCall` component: every `some` DecCall result keeps
    the input globals shape-stable. -/
theorem evalPanValueFfiClockCodeDecCall_globals_stable
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (fuel : Nat) (locals globals memory ffi clock : _)
    (name : VarName) (shape : Shape) (function : FunName) (arguments : List (Exp α))
    (body : Prog α) (evaluator : Option (PanExprEvaluator α)) :
    panValueFfiClockGlobalsStable structs globals
      (evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions
        base top bytes fuel locals globals memory ffi clock name shape function arguments
        body access contracts mh evaluator) :=
  (evalPanValueFfiClockCode_globals_stable context primitive handler structs code exceptions
    base top bytes access contracts mh fuel).2.1 locals globals memory ffi clock name shape
    function arguments body evaluator

/-- On any `some` Call result, the `Global`-destination verdict against the
    callee post-state globals equals the verdict against the caller globals:
    HOL's `is_valid_value s Global ...` (`panSemScript.sml:469-474`) observes
    only binding shapes, and every code-map evaluation preserves them.  This is
    #1250 report item 7. -/
theorem evalPanValueFfiClockCodeCall_global_verdict_congr
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (fuel : Nat) (locals globals memory ffi clock : _)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) (preserve : Bool)
    (evaluator : Option (PanExprEvaluator α))
    {outcome : PanValueFfiClockOutcome α σ} {resultClock : Nat}
    (h : evalPanValueFfiClockCodeCall context primitive handler structs code exceptions
      base top bytes fuel locals globals memory ffi clock info function arguments
      access contracts mh preserve evaluator = some (outcome, resultClock))
    (name : VarName) (value : PanValue α) :
    panValueAssignmentValid structs locals (panValueFfiClockOutcomeGlobals outcome)
        .global name value =
      panValueAssignmentValid structs locals globals .global name value := by
  have hstable := (evalPanValueFfiClockCode_globals_stable context primitive handler structs
    code exceptions base top bytes access contracts mh fuel).1 locals globals memory ffi clock
    info function arguments preserve evaluator
  exact panValueAssignmentValid_global_congr structs locals globals
    (panValueFfiClockOutcomeGlobals outcome)
    (hstable (outcome, resultClock) h) name value

/-- On any `some` DecCall result, the `Global`-destination verdict against the
    result's globals equals the verdict against the caller globals. -/
theorem evalPanValueFfiClockCodeDecCall_global_verdict_congr
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (code : PanSemCodeMap α) (exceptions : ExceptionId → Option Shape)
    (base top bytes : α) (access : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (mh : Option (PanValueMemoryFfiHandler α σ))
    (fuel : Nat) (locals globals memory ffi clock : _)
    (name : VarName) (shape : Shape) (function : FunName) (arguments : List (Exp α))
    (body : Prog α) (evaluator : Option (PanExprEvaluator α))
    {outcome : PanValueFfiClockOutcome α σ} {resultClock : Nat}
    (h : evalPanValueFfiClockCodeDecCall context primitive handler structs code exceptions
      base top bytes fuel locals globals memory ffi clock name shape function arguments
      body access contracts mh evaluator = some (outcome, resultClock))
    (destination : VarName) (value : PanValue α) :
    panValueAssignmentValid structs locals (panValueFfiClockOutcomeGlobals outcome)
        .global destination value =
      panValueAssignmentValid structs locals globals .global destination value := by
  have hstable := (evalPanValueFfiClockCode_globals_stable context primitive handler structs
    code exceptions base top bytes access contracts mh fuel).2.1 locals globals memory ffi clock
    name shape function arguments body evaluator
  exact panValueAssignmentValid_global_congr structs locals globals
    (panValueFfiClockOutcomeGlobals outcome)
    (hstable (outcome, resultClock) h) destination value

/-! This declaration-boundary adapter exposes the executed source-owned call
    after declaration evaluation. It shares the exact code-map conversion,
    exception-shape lookup, and return-contract path used by the public
    program evaluator, so correctness lemmas do not assume a separate legacy
    functions-list call result. The adapter itself is Flapjack infrastructure
    with no single HOL declaration. -/
def evalPanValueFfiClockProgramCodeCall
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanValueProgramState α)
    (fuel : Nat) (globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat) (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiClockResult α σ) := do
  let code ← panValueProgramStateCodeMap state
  let contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  evalPanValueFfiClockCodeCall context primitive handler state.structs code
    (fun exception => lookupInfo exception state.exceptions)
    state.baseAddress state.topAddress state.bytesInWord fuel (fun _ => none)
    globals memory ffi clock none entry arguments
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler) (evaluator := evaluator)

/-- The declaration-to-entry tail shared by the generic program runner and the
    RV64 HOL-routed runner: evaluate the entry call from an already-evaluated
    declaration state, then enforce `panSem`'s single-value return shape. The
    state supplies the structure context, code map, globals, memory and return
    metadata, so the entry call and its shape check always read the same
    evaluated declaration state.

    It is modelled on the `semantics s' start` tail of HOL's `semantics_decls`
    (`cakeml/pancake/semantics/panSemScript.sml:861`). It is not an exact port
    and carries no `@[hol]` tag, for these reasons:

    - HOL's `semantics` calls `start` with no arguments (`Call NONE start []`),
      while this adapter takes arbitrary `arguments`.
    - HOL's `semantics` classifies Fail/Terminate/Diverge over every clock,
      while this adapter returns one fuel- and clock-bounded outcome.
    - This adapter adds the single-value return-shape check. -/
def evalPanValueFfiClockProgramEntry
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanValueProgramState α)
    (fuel : Nat) (entryFfi : FfiState σ) (clock : Nat)
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiClockResult α σ) := do
  let (outcome, nextClock) ← evalPanValueFfiClockProgramCodeCall context primitive
    handler state fuel state.globals state.memory entryFfi clock entry arguments
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) (evaluator := evaluator)
  match lookupInfo entry state.returnShapes, outcome with
  | some shape, .control (.returned locals globals memory ffi [value]) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.control (.returned locals globals memory ffi [value]), nextClock)
      else none
  | some _, .control (.returned _ _ _ _ _) => none
  | _, outcome => some (outcome, nextClock)

/-- A pointwise-correct route preserves the shared declaration-to-entry tail:
    the entry call and its single-value return-shape check agree for the routed
    and generic evaluators. This is Flapjack infrastructure with no single HOL
    declaration. `evalPanValueFfiClockProgram_route_eq` uses it for the generic
    program runner. The RV64 HOL-routed runner has no route-equality theorem
    yet: its guarded route falls back to `evalPanSemStateExp` and reads the
    owner's memory domains and endianness, so it is not pointwise equal to
    `evalPanValueExp` without a memory-relation or byte-ranged premise. That
    obligation is tracked in #1245, which this work references rather than
    closes. -/
theorem evalPanValueFfiClockProgramEntry_route_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanValueProgramState α)
    (fuel : Nat) (entryFfi : FfiState σ) (clock : Nat)
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (run : PanExprEvaluator α)
    (h : ∀ locals globals memory e,
      run state.structs locals globals memory state.baseAddress state.topAddress
        state.bytesInWord memoryAccess e =
      evalPanValueExp state.structs locals globals memory state.baseAddress state.topAddress
        state.bytesInWord e memoryAccess) :
    evalPanValueFfiClockProgramEntry context primitive handler state fuel entryFfi clock entry arguments
      memoryAccess memoryHandler (some run) =
    evalPanValueFfiClockProgramEntry context primitive handler state fuel entryFfi clock entry arguments
      memoryAccess memoryHandler none := by
  simp only [evalPanValueFfiClockProgramEntry, evalPanValueFfiClockProgramCodeCall]
  cases hc : panValueProgramStateCodeMap state with
  | none => simp
  | some code =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hrun := (evalPanValueFfiClockCode_route_eq context primitive handler state.structs code
      (fun exception => lookupInfo exception state.exceptions) state.baseAddress state.topAddress
      state.bytesInWord memoryAccess
      (some (PanValueCallContracts.mk state.returnShapes state.exceptions
        state.parameterShapes)) memoryHandler run h fuel).1
      (fun _ => none) state.globals state.memory entryFfi clock none entry arguments false
    rw [hrun]

/-- Evaluate a program with a route builder that receives the collected
    structure context. The builder's evaluator is produced once and reused for
    the declaration and entry phases, so the RV64 HOL-routed runner does not
    repeat the declaration setup. `evalPanValueFfiClockProgram` is the
    constant-builder case and is defined through this function, so the two
    runners cannot drift.

    It has no single HOL declaration: HOL's `semantics_decls` runs
    `decs_stcnames`, then `evaluate_decls`, then `semantics s' start`; this
    runner performs the same sequence with the fuel/clock evaluator, and HOL
    fixes one expression evaluator, so choosing one from the collected
    structure context is Flapjack-only plumbing over the same sequence. The
    differences from HOL are the ones listed on
    `evalPanValueFfiClockProgramEntry`, plus the struct-context seed noted on
    `evalPanValueFfiClockProgram`. -/
def evalPanValueFfiClockProgramWithRoute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (route : StructContext → Option (PanExprEvaluator α)) :
    Option (PanValueFfiClockResult α σ) := do
  let (state, evaluator) ← evalPanValueDeclarationsWithRoute initial.source declarations
    memoryAccess route
  evalPanValueFfiClockProgramEntry context primitive handler state
    (fuel := fuel) (entryFfi := initial.ffi) (clock := clock) entry arguments
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    (evaluator := evaluator)

/-- Evaluate a program through the source boundary: evaluate its declarations
    with the selected expression route, then run the entry call and enforce the
    single-value return shape. Defined through `evalPanValueFfiClockProgramWithRoute`
    with a constant route builder, so the generic and routed runners share one
    declaration/entry sequence.

    It has no single HOL declaration: HOL's `semantics_decls` runs
    `decs_stcnames`, then `evaluate_decls`, then `semantics s' start`; this
    runner performs the same sequence with the fuel/clock evaluator. The
    differences from HOL are the ones listed on `evalPanValueFfiClockProgramEntry`,
    plus the struct-context seed: HOL's `decs_stcnames []` starts from an empty
    context, while this runner collects structs from the initial source
    context. -/
def evalPanValueFfiClockProgram
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (initial : PanValueFfiProgramState α σ)
    (clock : Nat)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α))
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiClockResult α σ) :=
  evalPanValueFfiClockProgramWithRoute context initial clock primitive handler fuel
    declarations entry arguments memoryAccess memoryHandler (fun _ => evaluator)

/-- Unfolded form of `evalPanValueFfiClockProgram`: the constant-builder case of
    `evalPanValueFfiClockProgramWithRoute`, with declaration evaluation written
    through `evalPanValueDeclarations`. Kept as the shape the program-level
    route proofs reason about. -/
theorem evalPanValueFfiClockProgram_unfolded
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (initial : PanValueFfiProgramState α σ)
    (clock : Nat) (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ))
    (evaluator : Option (PanExprEvaluator α)) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel declarations entry arguments
      memoryAccess memoryHandler evaluator =
      (do
        let state ← evalPanValueDeclarations initial.source declarations
          (memoryAccess := memoryAccess) (evaluator := evaluator)
        evalPanValueFfiClockProgramEntry context primitive handler state
          (fuel := fuel) (entryFfi := initial.ffi) (clock := clock) entry arguments
          (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
          (evaluator := evaluator)) := by
  simp only [evalPanValueFfiClockProgram, evalPanValueFfiClockProgramWithRoute,
    evalPanValueDeclarationsWithRoute, evalPanValueDeclarations_eq]
  cases hstructs : collectPanValueStructs declarations initial.source.structs with
  | none => simp
  | some structs =>
    cases hstate : evalPanValueDeclarationsWithStructs structs
        { initial.source with structs := structs } declarations memoryAccess evaluator with
    | none => simp [hstate]
    | some st => simp [hstate]

/-- A pointwise-correct route preserves the full program result from
    declaration initializers through the clocked entry call. -/
theorem evalPanValueFfiClockProgram_route_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (initial : PanValueFfiProgramState α σ)
    (clock : Nat) (primitive : PanPrimitiveHandler α) (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (decls : List (Decl α)) (entry : FunName) (arguments : List (Exp α))
    (access : Option (PanValueMemoryAccess α)) (mh : Option (PanValueMemoryFfiHandler α σ))
    (run : PanExprEvaluator α)
    (h : ∀ structs locals globals memory base top e,
      run structs locals globals memory base top initial.source.bytesInWord access e =
        evalPanValueExp structs locals globals memory base top initial.source.bytesInWord e access) :
    evalPanValueFfiClockProgram context initial clock primitive handler fuel decls entry arguments
      access mh (some run) =
    evalPanValueFfiClockProgram context initial clock primitive handler fuel decls entry arguments
      access mh none := by
  have hdecl := evalPanValueDeclarations_route_eq initial.source.bytesInWord access run
    (fun structs globals memory base top e => h structs (fun _ => none) globals memory base top e)
    initial.source rfl decls
  simp only [evalPanValueFfiClockProgram_unfolded, hdecl]
  cases hd : evalPanValueDeclarations initial.source decls access none with
  | none => simp
  | some state =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hb : state.bytesInWord = initial.source.bytesInWord :=
      evalPanValueDeclarations_bytesInWord initial.source state decls access none hd
    exact evalPanValueFfiClockProgramEntry_route_eq context primitive handler state
      (fuel := fuel) (entryFfi := initial.ffi) (clock := clock) entry arguments access mh run
      (fun locals globals memory e => by
        simpa [hb] using h state.structs locals globals memory state.baseAddress state.topAddress e)

end Flapjack
