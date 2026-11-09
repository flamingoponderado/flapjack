module

public import Flapjack.Pancake.Semantics.PanSem.EvalExecutedBridge

@[expose] public section

/-! Executable byte-name guards for the production-to-HOL expression route.
The guard only inspects the finite names read by an expression, its lookup
values, and the finite structure context. Outside that boundary, the original
production evaluator preserves support for arbitrary Lean strings. -/

namespace Flapjack
open Flapjack.Pancake.PanLang

mutual
  def panSemShapeRangedDec : (s : Shape) → Decidable (ShapeByteRanged s)
    | .one => isTrue (by simp [ShapeByteRanged])
    | .named n => by
      apply decidable_of_iff (∀ c ∈ n.toList, c.toNat < 256)
      simp [ShapeByteRanged]
    | .comb xs => by
      letI := panSemShapeListRangedDec xs
      apply decidable_of_iff (∀ v ∈ xs, ShapeByteRanged v)
      simp [ShapeByteRanged]
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf <;> omega
  def panSemShapeListRangedDec : (xs : List Shape) → Decidable (∀ v ∈ xs, ShapeByteRanged v)
    | [] => isTrue (by simp)
    | x :: xs => by
      letI := panSemShapeRangedDec x
      letI := panSemShapeListRangedDec xs
      exact decidable_of_iff (ShapeByteRanged x ∧ ∀ v ∈ xs, ShapeByteRanged v) (by simp)
  termination_by xs => sizeOf xs
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  def panSemExpRangedDec : (e : Exp (BitVec 64)) → Decidable (ExpByteRanged e)
    | .const _ => isTrue trivial
    | .var _ n => inferInstanceAs (Decidable (∀ c ∈ n.toList, c.toNat < 256))
    | .rStruct es => panSemExpListRangedDec es
    | .rField _ e => panSemExpRangedDec e
    | .nStruct n fs => by
      letI := panSemFieldListRangedDec fs
      exact inferInstanceAs (Decidable ((∀ c ∈ n.toList, c.toNat < 256) ∧ ListFieldByteRanged fs))
    | .nField n e => by
      letI := panSemExpRangedDec e
      exact inferInstanceAs (Decidable ((∀ c ∈ n.toList, c.toNat < 256) ∧ ExpByteRanged e))
    | .load shape e => by
      letI := panSemShapeRangedDec shape
      letI := panSemExpRangedDec e
      exact inferInstanceAs (Decidable (ShapeByteRanged shape ∧ ExpByteRanged e))
    | .load32 e | .loadByte e => panSemExpRangedDec e
    | .op _ es | .panOp _ es => panSemExpListRangedDec es
    | .cmp _ l r | .shift _ l r => by
      letI := panSemExpRangedDec l
      letI := panSemExpRangedDec r
      exact inferInstanceAs (Decidable (ExpByteRanged l ∧ ExpByteRanged r))
    | .baseAddr | .topAddr | .bytesInWord => isTrue trivial
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf <;> omega
  def panSemExpListRangedDec : (es : List (Exp (BitVec 64))) → Decidable (ListExpByteRanged es)
    | [] => isTrue trivial
    | e :: es => by
      letI := panSemExpRangedDec e
      letI := panSemExpListRangedDec es
      exact inferInstanceAs (Decidable (ExpByteRanged e ∧ ListExpByteRanged es))
  termination_by es => sizeOf es
  decreasing_by all_goals simp_wf <;> omega
  def panSemFieldListRangedDec : (fs : List (String × Exp (BitVec 64))) → Decidable (ListFieldByteRanged fs)
    | [] => isTrue trivial
    | (n,e) :: fs => by
      letI := panSemExpRangedDec e
      letI := panSemFieldListRangedDec fs
      exact inferInstanceAs (Decidable ((∀ c ∈ n.toList, c.toNat < 256) ∧ ExpByteRanged e ∧ ListFieldByteRanged fs))
  termination_by fs => sizeOf fs
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  def panSemValueRangedDec : (v : PanValue (BitVec 64)) → Decidable (PanValueByteRanged v)
    | .word _ => isTrue (by simp [PanValueByteRanged])
    | .rStruct vs => by
      letI := panSemValueListRangedDec vs
      apply decidable_of_iff (∀ v ∈ vs, PanValueByteRanged v)
      simp [PanValueByteRanged]
    | .nStruct n fs => by
      letI := panSemValueFieldRangedDec fs
      apply decidable_of_iff (NameRanged n ∧ ∀ p ∈ fs, NameRanged p.1 ∧ PanValueByteRanged p.2)
      simp [PanValueByteRanged]
  termination_by v => sizeOf v
  decreasing_by all_goals simp_wf <;> omega
  def panSemValueListRangedDec : (vs : List (PanValue (BitVec 64))) → Decidable (∀ v ∈ vs, PanValueByteRanged v)
    | [] => isTrue (by simp)
    | v :: vs => by
      letI := panSemValueRangedDec v
      letI := panSemValueListRangedDec vs
      exact decidable_of_iff (PanValueByteRanged v ∧ ∀ x ∈ vs, PanValueByteRanged x) (by simp)
  termination_by vs => sizeOf vs
  decreasing_by all_goals simp_wf <;> omega
  def panSemValueFieldRangedDec : (fs : List (String × PanValue (BitVec 64))) →
      Decidable (∀ p ∈ fs, NameRanged p.1 ∧ PanValueByteRanged p.2)
    | [] => isTrue (by simp)
    | (n,v) :: fs => by
      letI := panSemValueRangedDec v
      letI := panSemValueFieldRangedDec fs
      exact decidable_of_iff
        ((NameRanged n ∧ PanValueByteRanged v) ∧ ∀ p ∈ fs, NameRanged p.1 ∧ PanValueByteRanged p.2) (by simp)
  termination_by fs => sizeOf fs
  decreasing_by all_goals simp_wf <;> omega
end
def panSemContextRangedDec (ctx : StructContextHOL) : Decidable (StructContextByteRanged ctx) := by
  letI (p : String × Shape) : Decidable (ParamByteRanged p) := by
    letI := panSemShapeRangedDec p.2
    exact inferInstanceAs (Decidable (NameRanged p.1 ∧ ShapeByteRanged p.2))
  letI (info : StructInfoHOL) : Decidable (StructInfoByteRanged info) := by
    exact inferInstanceAs (Decidable (∀ p ∈ info.fields, ParamByteRanged p))
  letI (entry : String × StructInfoHOL) : Decidable (NameRanged entry.1 ∧ StructInfoByteRanged entry.2) :=
    inferInstance
  exact inferInstanceAs (Decidable (∀ p ∈ ctx, NameRanged p.1 ∧ StructInfoByteRanged p.2))
def panSemLookupRangedDec (lookup : String → Option (PanValue (BitVec 64))) (name : String) :
    Decidable (∀ value, lookup name = some value → PanValueByteRanged value) := by
  cases h : lookup name with
  | none => exact isTrue (by simp)
  | some value =>
    letI := panSemValueRangedDec value
    apply decidable_of_iff (PanValueByteRanged value)
    simp

def panSemExpressionInputsRangedDec (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : Decidable (PanSemExpressionInputsRanged s e) := by
  letI (name : String) := panSemLookupRangedDec s.locals name
  letI (name : String) := panSemLookupRangedDec s.globals name
  letI := panSemContextRangedDec s.structs.toHOL
  exact inferInstanceAs (Decidable
    ((∀ n ∈ expLocalVars e, ∀ v, s.locals n = some v → PanValueByteRanged v) ∧
     (∀ n ∈ expGlobalVars e, ∀ v, s.globals n = some v → PanValueByteRanged v) ∧
     StructContextByteRanged s.structs.toHOL))

/-- Inspect the exact per-expression dispatch decision. A false result means
    execution takes the generic String-compatible fallback. -/
def panSemExpressionUsesHOL (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : Bool :=
  letI := panSemExpRangedDec e
  letI := panSemExpressionInputsRangedDec s e
  decide (ExpByteRanged e ∧ PanSemExpressionInputsRanged s e)

/-- Run the HOL expression evaluator when the observable guard accepts the
    inputs, otherwise preserve the generic evaluator's String behavior. -/
def evalPanSemStateExpViaHOLGuarded (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  if panSemExpressionUsesHOL s e then
    evalPanSemStateExpViaHOLWordDomain s e
  else evalPanSemStateExp s e

/-- Cache the fixed structure context once for a code-map run. -/
structure PanSemExpressionContextCache where
  ranged : Bool
  hol : StructContextExact

def panSemExpressionContextCache (structs : StructContext) : PanSemExpressionContextCache :=
  letI := panSemContextRangedDec structs.toHOL
  { ranged := decide (StructContextByteRanged structs.toHOL)
    hol := panStructContextToHOL structs }

def panSemExpressionUsesHOLCached (cache : PanSemExpressionContextCache)
    (s : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64)) : Bool :=
  letI := panSemExpRangedDec e
  letI (name : String) := panSemLookupRangedDec s.locals name
  letI (name : String) := panSemLookupRangedDec s.globals name
  cache.ranged && decide (ExpByteRanged e ∧
    (∀ n ∈ expLocalVars e, ∀ v, s.locals n = some v → PanValueByteRanged v) ∧
    (∀ n ∈ expGlobalVars e, ∀ v, s.globals n = some v → PanValueByteRanged v))

def evalPanSemStateExpViaHOLCached (cache : PanSemExpressionContextCache)
    (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (_coherent : cache = panSemExpressionContextCache s.structs)
    (e : Exp (RiscV.Word 64)) : Option (PanValue (RiscV.Word 64)) :=
  if panSemExpressionUsesHOLCached cache s e then
    let state := panSemExpressionWordDomain s
    (@PanSemStateFiniteExact.evalHOLFinite 64 σ _
      (panSemExpressionSliceRuntimeViewWithStructs state e cache.hol)
      (fun address => inferInstanceAs (Decidable (state.memaddrs address = true))) (expToHOL e)).map
        panValueOfHOL
  else evalPanSemStateExp s e

/-- The guarded HOL expression route and the memory access derived from the
    same owner state. The structure groups the two so callers can take both
    from one construction; it does not prevent a caller from building a
    mismatched pair, so use the fields of a single value. -/
structure PanSemExpressionRoute where
  run : PanExprEvaluator (RiscV.Word 64)
  access : Option (PanValueMemoryAccess (RiscV.Word 64))

/-- Build the guarded HOL expression route and its memory access for one
    state-owned run. The route pins the owner's structure context, word size and
    memory domains; the per-call `structs`, `bytes` and `access` arguments that
    the evaluator signature supplies are ignored, so every expression in the run
    sees the same settings. The structure-context cache is computed once per
    route construction, outside the per-expression lambda: `panSemExpressionRoute`
    is marked `@[noinline]`, so the `let cache` is evaluated once when the route
    value is built (Lean is strict) and captured by the closure. Without that
    attribute a call site could inline the definition and float the `let` into
    the lambda, recomputing the cache for every expression. The access is
    `some (panSemBitVec64MemoryAccess owner)`, and
    `panSemExpressionRoute_access_structs` records that re-pinning the structure
    context leaves it unchanged. The generic fallback `evalPanSemStateExp`
    derives its access with `panSemWordMemoryAccess`, which agrees with
    `panSemBitVec64MemoryAccess` at width 64 (`panSemWordMemoryAccess_64`), so
    the routed and fallback paths read the same memory domains. The dispatch
    guard itself is Flapjack infrastructure with no single HOL declaration:
    HOL's `panSem` has one expression evaluator, while the Lean runner must
    choose between the HOL-shaped evaluator and the String-compatible
    fallback. -/
@[noinline]
def panSemExpressionRoute (owner : PanSemState (RiscV.Word 64) (FfiState σ)) :
    PanSemExpressionRoute :=
  let cache := panSemExpressionContextCache owner.structs
  { run := fun _structs locals globals memory base top _bytes _access e =>
      evalPanSemStateExpViaHOLCached cache
        { owner with
          locals := locals
          globals := globals
          memory := memory
          baseAddress := base
          topAddress := top } rfl e
    access := some (panSemBitVec64MemoryAccess owner) }

/-- Re-pinning the structure context leaves the route's access unchanged: the
    access is derived only from the owner's memory domains and byte order. -/
theorem panSemExpressionRoute_access_structs
    (owner : PanSemState (RiscV.Word 64) (FfiState σ)) (structs : StructContext) :
    (panSemExpressionRoute { owner with structs := structs }).access =
      (panSemExpressionRoute owner).access := rfl

/-- State-owned RV64 code evaluation with the guarded HOL expression route.
    The code-map runner carries the route through calls, branches, and leaves;
    its memory access is derived from the same source state as the route. -/
def panSemEvaluateRiscV64CodeStateViaHOL
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (program : Prog (RiscV.Word 64)) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  let route := panSemExpressionRoute state
  evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
    state.exceptionShapes state.baseAddress state.topAddress panSemBitVec64BytesInWord
    (panSemCodeEvaluateFuel state program) state.locals state.globals state.memory state.ffi
    state.clock program (memoryAccess := route.access) (evaluator := some route.run)

/-- State-owned RV64 HOL-routed code evaluation with its observable post-state. -/
def panSemEvaluateRiscV64CodeStateViaHOLWithPostState
    (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (program : Prog (RiscV.Word 64)) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ ×
      PanSemState (RiscV.Word 64) (FfiState σ)) :=
  (panSemEvaluateRiscV64CodeStateViaHOL context primitive handler state program).map
    (fun result => (result, panSemCodeStateAfter state result))

/-- A single RV64 program input owns both its declaration state and the
    source memory domains and byte order used throughout evaluation. -/
structure PanSemRiscV64ProgramInput (σ : Type) where
  initial : PanValueFfiProgramState (RiscV.Word 64) σ
  memaddrs : RiscV.Word 64 → Bool
  sharedMemaddrs : RiscV.Word 64 → Bool
  bigEndian : Bool

/-- Build the expression-route owner from the same input as the declarations;
    code and locals are supplied by the runner and are unused by expressions. -/
def PanSemRiscV64ProgramInput.toOwner (input : PanSemRiscV64ProgramInput σ) :
    PanSemState (RiscV.Word 64) (FfiState σ) where
  locals := fun _ => none
  globals := input.initial.source.globals
  structs := input.initial.source.structs
  code := []
  exceptionShapes := fun _ => none
  memory := input.initial.source.memory
  memaddrs := input.memaddrs
  sharedMemaddrs := input.sharedMemaddrs
  clock := 0
  be := input.bigEndian
  ffi := input.initial.ffi
  baseAddress := input.initial.source.baseAddress
  topAddress := input.initial.source.topAddress

/-- RV64 declaration-to-entry execution through the HOL expression route.
    The input supplies the source memory domains and byte order. A non-RV64
    byte count keeps the generic evaluator, preserving its previous behavior.
    The routed branch delegates to `evalPanValueFfiClockProgramWithRoute`, so
    the declaration setup lives in the generic runner instead of being copied
    here.

    Both branches take the access from `panSemExpressionRoute input.toOwner`, so
    the access used for every phase is a field of the route value itself.
    `panSemExpressionRoute_access_structs` records that the per-structs routes
    built below keep that access. The struct-context seed is a difference from
    HOL: `semantics_decls` runs `decs_stcnames []`, which starts from an empty
    context, while the generic runner collects structs from
    `input.initial.source.structs` (also noted on
    `evalPanValueFfiClockProgram`). The remaining differences from HOL are listed
    on `evalPanValueFfiClockProgramEntry`. -/
def panSemEvaluateRiscV64ProgramViaHOL
    (context : PanValueFfiContext (RiscV.Word 64))
    (input : PanSemRiscV64ProgramInput σ)
    (clock : Nat) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (fuel : Nat) (decls : List (Decl (RiscV.Word 64)))
    (entry : FunName) (arguments : List (Exp (RiscV.Word 64)))
    (memoryHandler : Option (PanValueMemoryFfiHandler (RiscV.Word 64) σ) := none) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  if input.initial.source.bytesInWord = panSemBitVec64BytesInWord then
    evalPanValueFfiClockProgramWithRoute context input.initial clock primitive handler fuel decls
      entry arguments (panSemExpressionRoute input.toOwner).access memoryHandler
      (fun structs => some (panSemExpressionRoute { input.toOwner with structs := structs }).run)
  else
    evalPanValueFfiClockProgram context input.initial clock primitive handler fuel decls entry arguments
      (panSemExpressionRoute input.toOwner).access memoryHandler

end Flapjack
