module

public import Flapjack.PanValueFfiCore
public import Flapjack.PanBst

@[expose] public section

/-!
# Clocked structured Pancake semantics

This module adds the clock/timeout part of CakeML's `panSem` boundary to the
canonical structured, stateful-FFI evaluator.  The existing evaluator remains
available for compatibility and for proofs that do not model a clock.  The
clocked evaluator charges one unit at a function call, at each executed while
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

/-- The leaf statements: exactly those that `evalPanValueFfiClockProg` hands
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


/-! The functions-list evaluator below is compatibility infrastructure, not a
HOL-faithful `panSem$evaluate` port. Its `functions` entries have parameter
names and a body but no `returnShape`; consequently its Call return branch
cannot perform HOL's state-code return-shape check and may accept a returned
value that HOL rejects. The separate state-owned code-map evaluator is the
HOL-shaped path used for correctness work. -/
mutual
  def evalPanValueFfiClockCall
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
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        (preserveReturnLocals : Bool := false) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, info, function, arguments,
        memoryAccess, contracts, memoryHandler, preserveReturnLocals => do
        (panValueCallArgumentsValue structs baseAddress topAddress bytesInWord locals globals memory
          arguments memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun values =>
            (panValueCallTarget structs contracts function functions values).elim
              (pure (.control (.error locals globals memory ffi), clock))
              (fun callTarget => do
              let (body, calleeLocals) := callTarget
              if clock = 0 then
                pure (panValueFfiClockTimeout globals memory ffi clock)
              else
                let (outcome, calleeClock) ← evalPanValueFfiClockProg context primitive handler
                  structs functions baseAddress topAddress bytesInWord fuel calleeLocals
                  globals memory ffi (decPanClock clock) body
                  (memoryAccess := memoryAccess) (contracts := contracts)
                  (memoryHandler := memoryHandler)
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
                    | .returned _ calleeGlobals calleeMemory calleeFfi values =>
                        -- This functions-list compatibility carrier stores only
                        -- parameter names and the body; unlike HOL `state.code`,
                        -- it has no source `returnShape`.  Do not substitute the
                        -- optional, independently supplied `contracts` table for
                        -- that missing code-map field: doing so can reject a
                        -- return that HOL accepts.  The state-owned code-map
                        -- evaluator below performs the actual HOL shape check.
                        match info with
                        | none =>
                            let returnedLocals :=
                              if preserveReturnLocals then calleeLocals else fun _ => none
                            pure (.control
                            (.returned returnedLocals calleeGlobals calleeMemory
                              calleeFfi values), calleeClock)
                        | some (destination, _) => do
                            let (callerLocals, callerGlobals) ←
                              assignPanValueCallResult locals calleeGlobals destination values
                                (structs := structs)
                            pure (.control (.normal callerLocals callerGlobals
                              calleeMemory calleeFfi), calleeClock)
                    | .raised _ calleeGlobals calleeMemory calleeFfi exception value =>
                        if panValueExceptionValid structs contracts exception value &&
                            panValuePayloadWithinLimit structs value then
                          match info with
                          | some (_, some (caught, handlerVariable, handlerProgram)) =>
                              if caught == exception then
                                if panValueHandlerValid structs contracts locals handlerVariable value then
                                  evalPanValueFfiClockProg context primitive handler structs functions
                                    baseAddress topAddress bytesInWord fuel
                                    (updatePanValueMap locals handlerVariable value) calleeGlobals
                                    calleeMemory calleeFfi calleeClock handlerProgram
                                    (memoryAccess := memoryAccess) (contracts := contracts)
                                    (memoryHandler := memoryHandler)
                                else none
                              else pure (.control (.raised (fun _ => none) calleeGlobals
                                calleeMemory calleeFfi exception value), calleeClock)
                          | _ => pure (.control (.raised (fun _ => none) calleeGlobals
                              calleeMemory calleeFfi exception value), calleeClock)
                        else none
                    | .finalFfi _ calleeGlobals calleeMemory calleeFfi event =>
                        pure (.control (.finalFfi (fun _ => none) calleeGlobals
                          calleeMemory calleeFfi event), calleeClock)
              ))
    termination_by fuel _ _ _ _ _ _ _ _ _ => fuel

  def evalPanValueFfiClockProg
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
        (VarName → Option (PanValue α)) →
        (α → Option (PanValue α)) → FfiState σ → Nat → Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) →
        Option (PanValueFfiClockResult α σ)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, ffi, clock, .dec name shape value body,
        memoryAccess, contracts, memoryHandler =>
        (panValueDecAcceptedValue structs baseAddress topAddress bytesInWord locals globals memory
          value memoryAccess shape).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun evaluated => do
            let oldValue := locals name
            let (outcome, nextClock) ← evalPanValueFfiClockProg context primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              (updatePanValueMap locals name evaluated) globals memory ffi clock body
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
            pure (panValueFfiClockRestoreLocal name oldValue outcome, nextClock))
    | fuel + 1, locals, globals, memory, ffi, clock, .seq first second,
        memoryAccess, contracts, memoryHandler => do
        let (firstOutcome, firstClock) ← evalPanValueFfiClockProg context primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
          clock first (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match firstOutcome with
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
            evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
              firstClock second (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler)
        | _ => pure (firstOutcome, firstClock)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory condition memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun condition =>
            evalPanValueFfiClockProg context primitive handler structs functions
              baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
              (if condition != 0 then thenBranch else elseBranch)
              (memoryAccess := memoryAccess) (contracts := contracts)
              (memoryHandler := memoryHandler))
    | fuel + 1, locals, globals, memory, ffi, clock,
        .call info function arguments, memoryAccess, contracts, memoryHandler =>
        evalPanValueFfiClockCall context primitive handler structs functions
          baseAddress topAddress bytesInWord fuel locals globals memory ffi clock info function
          arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, ffi, clock,
        .decCall name shape function arguments body, memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let (outcome, nextClock) ← evalPanValueFfiClockCall context primitive handler structs
          functions baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
          none function arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler) (preserveReturnLocals := true)
        match outcome with
        | .control (.returned nextLocals nextGlobals nextMemory nextFfi [value]) =>
            if panShapeMatches (panValueShape structs value) shape then
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) nextGlobals nextMemory nextFfi nextClock body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (panValueFfiClockRestoreLocal name oldValue bodyOutcome, bodyClock)
            -- HOL's mismatch branch returns the callee post-state `st`.
            else pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.raised _ nextGlobals nextMemory nextFfi exception value) =>
            pure (.control (.raised (fun _ => none) nextGlobals nextMemory nextFfi
              exception value), nextClock)
        | .timeout nextLocals nextGlobals nextMemory nextFfi =>
            pure (.timeout nextLocals nextGlobals nextMemory nextFfi, nextClock)
        | .control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event) =>
            pure (.control (.finalFfi nextLocals nextGlobals nextMemory nextFfi event),
              nextClock)
        | .control (.returned _ _ _ _ _) => none
        | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
            .control (.broke nextLocals nextGlobals nextMemory nextFfi) |
            .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
            -- HOL `DecCall` turns callee NONE/Break/Continue into Error and
            -- returns the fixed callee post-state unchanged.
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
        | .control (.error nextLocals nextGlobals nextMemory nextFfi) =>
            pure (.control (.error nextLocals nextGlobals nextMemory nextFfi), nextClock)
    | fuel + 1, locals, globals, memory, ffi, clock, .while conditionExp body,
        memoryAccess, contracts, memoryHandler =>
        (panValueIteConditionValue structs baseAddress topAddress bytesInWord locals globals
          memory conditionExp memoryAccess).elim
          (pure (.control (.error locals globals memory ffi), clock))
          (fun conditionValue =>
            if conditionValue == 0 then
              pure (.control (.normal locals globals memory ffi), clock)
            else if clock == 0 then
              pure (panValueFfiClockTimeout globals memory ffi clock)
            else do
              let (bodyOutcome, bodyClock) ← evalPanValueFfiClockProg context primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory ffi
                (decPanClock clock) body (memoryAccess := memoryAccess)
                (contracts := contracts)
                (memoryHandler := memoryHandler)
              match bodyOutcome with
              | .control (.normal nextLocals nextGlobals nextMemory nextFfi) |
                  .control (.continued nextLocals nextGlobals nextMemory nextFfi) =>
                  evalPanValueFfiClockProg context primitive handler structs functions
                    baseAddress topAddress bytesInWord fuel nextLocals nextGlobals nextMemory nextFfi
                    bodyClock (.while conditionExp body)
                    (memoryAccess := memoryAccess) (contracts := contracts)
                    (memoryHandler := memoryHandler)
              | .control (.broke nextLocals nextGlobals nextMemory nextFfi) =>
                  pure (.control (.normal nextLocals nextGlobals nextMemory nextFfi), bodyClock)
              | _ => pure (bodyOutcome, bodyClock))
    | _fuel + 1, locals, globals, memory, ffi, clock, .tick, _, _, _ =>
        if clock = 0 then
          pure (panValueFfiClockTimeout globals memory ffi clock)
        else
          pure (.control (.normal locals globals memory ffi), decPanClock clock)
    | _fuel + 1, locals, globals, memory, ffi, clock, program, memoryAccess, contracts,
        memoryHandler =>
        evalPanValueFfiClockLeaf context primitive handler structs
          baseAddress topAddress bytesInWord clock locals globals memory ffi program
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    termination_by fuel _ _ _ _ _ _ _ => fuel
end

/-! Source-state clock evaluator. Unlike the compatibility evaluator above,
    every Call and DecCall resolves directly from the finite code map that is
    threaded unchanged through recursive evaluation. This is an executable
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
                          -- Call checks that shape directly. `contracts` is a
                          -- compatibility input and is not part of the HOL
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

    It has no single HOL declaration: HOL's `panSem` evaluates declarations and
    the entry call in one `evaluate_decls` step, while the Lean runners keep the
    already-evaluated declaration state separate so both runners can share this
    entry step. This adapter is therefore Flapjack infrastructure. -/
def evalPanValueFfiClockProgramEntry
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanValueProgramState α)
    (fuel : Nat) (ffi : FfiState σ) (clock : Nat)
    (entry : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (evaluator : Option (PanExprEvaluator α) := none) :
    Option (PanValueFfiClockResult α σ) := do
  let (outcome, nextClock) ← evalPanValueFfiClockProgramCodeCall context primitive
    handler state fuel state.globals state.memory ffi clock entry arguments
    (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) (evaluator := evaluator)
  match lookupInfo entry state.returnShapes, outcome with
  | some shape, .control (.returned locals globals memory ffi [value]) =>
      if panShapeMatches (panValueShape state.structs value) shape then
        some (.control (.returned locals globals memory ffi [value]), nextClock)
      else none
  | some _, .control (.returned _ _ _ _ _) => none
  | _, outcome => some (outcome, nextClock)

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
    Option (PanValueFfiClockResult α σ) := do
  let state ← evalPanValueDeclarations initial.source declarations
    (memoryAccess := memoryAccess) (evaluator := evaluator)
  evalPanValueFfiClockProgramEntry context primitive handler state fuel initial.ffi clock
    entry arguments (memoryAccess := memoryAccess) (memoryHandler := memoryHandler)
    (evaluator := evaluator)

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
  simp only [evalPanValueFfiClockProgram, evalPanValueFfiClockProgramEntry, hdecl]
  cases hd : evalPanValueDeclarations initial.source decls access none with
  | none => simp
  | some state =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hb : state.bytesInWord = initial.source.bytesInWord :=
      evalPanValueDeclarations_bytesInWord initial.source state decls access none hd
    simp only [evalPanValueFfiClockProgramCodeCall]
    cases hc : panValueProgramStateCodeMap state with
    | none => simp
    | some code =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hrun := (evalPanValueFfiClockCode_route_eq context primitive handler state.structs code
        (fun exception => lookupInfo exception state.exceptions) state.baseAddress state.topAddress
        state.bytesInWord access (some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes)) mh run
        (fun locals globals memory e => by
          simpa [hb] using (h state.structs locals globals memory state.baseAddress state.topAddress e)) fuel).1
        (fun _ => none) state.globals state.memory initial.ffi clock none entry arguments false
      rw [hrun]

/-! A callee that falls through (`panSem`'s `NONE`) is a call failure: Cake's
    `evaluate (Call ...)` maps `(NONE,st) => (SOME Error,st)`, preserving the
    callee's post-call locals, globals, memory, FFI state and clock.  This is
    the direct-call `NONE` rejection branch. -/
theorem evalPanValueFfiClockCall_callee_normal_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.normal bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A callee that finishes with `break` is a call failure: Cake's
    `evaluate (Call ...)` maps `(SOME Break,st) => (SOME Error,st)`, preserving
    the callee's post-call locals, globals, memory, FFI state and clock. -/
theorem evalPanValueFfiClockCall_callee_broke_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.broke bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-! A callee that finishes with `continue` is a call failure: Cake's
    `evaluate (Call ...)` maps `(SOME Continue,st) => (SOME Error,st)`, preserving
    the callee's post-call locals, globals, memory, FFI state and clock. -/
theorem evalPanValueFfiClockCall_callee_continued_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.continued bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]

/-- Flapjack's clocked Call equation for a callee Error: the catch-all Call
    branch preserves the callee's final nonlocal state and clears its locals.
    Untagged because this evaluator uses a structured control result rather
    than HOL's `result option × state` pair. -/
theorem evalPanValueFfiClockCall_callee_error_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α)
    (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ)
    (clock : Nat)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (body : Prog α) (finalClock : Nat)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none)
    (hargs : evalPanValueExps structs locals globals memory
      baseAddress topAddress bytesInWord arguments
      (memoryAccess := memoryAccess) = some values)
    (hlookup : lookupPanFunction function functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters : panValueParametersValid structs contracts function values = true)
    (hclock : clock ≠ 0)
    (hbody : evalPanValueFfiClockProg context primitive handler structs functions
      baseAddress topAddress bytesInWord fuel calleeLocals globals memory ffi (clock - 1)
      body (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    evalPanValueFfiClockCall context primitive handler structs functions
      baseAddress topAddress bytesInWord (fuel + 1) locals globals memory ffi clock
      info function arguments (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      some (.control (.error (fun _ => none) finalGlobals finalMemory finalFfi), finalClock) := by
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, panValueCallTarget,
    Option.elim_some, hargs, hlookup, hbind, hparameters, hclock, hbody]


end Flapjack
