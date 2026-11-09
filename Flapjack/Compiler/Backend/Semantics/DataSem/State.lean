module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Value
public import Flapjack.Compiler.Backend.DataLang.Syntax
public import Flapjack.Pancake.Semantics.CrepSem.HOLState

@[expose] public section

/-! Source-shaped data-language state and elementary state operations. -/
namespace Flapjack.Compiler.Backend.DataSem

/-- Stack frames preserve their optional size and sparse local environment. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "stack"]
inductive Stack where
  | env : Option Nat → Spt Value → Stack
  | exc : Option Nat → Spt Value → Nat → Stack

/-- Space limits and architecture features used by the data evaluator. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "limits"]
structure Limits where
  heapLimit : Nat
  lengthLimit : Nat
  stackLimit : Nat
  arch64Bit : Bool
  hasFpOps : Bool
  hasFpTops : Bool

/-- Compiler callback over labeled data-language programs. -/
abbrev Compiler (C : Type) := C → List (Nat × Nat × DataLang.Prog) →
  Option (List (BitVec 8) × List (BitVec 64) × C)

/-- Sequence of future compiler configurations and data programs. -/
abbrev CompileOracle (C : Type) := Nat → C × List (Nat × Nat × DataLang.Prog)

/-- Runtime data-language state, including space and timestamp accounting. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "state"]
structure State (C F : Type) where
  locals : Spt Value
  localsSize : Option Nat
  stack : List Stack
  stackMax : Option Nat
  stackFrameSizes : Spt Nat
  global : Option Nat
  handler : Nat
  refs : Spt (BvlSem.Ref Value)
  compile : Compiler C
  clock : Nat
  code : Spt (Nat × DataLang.Prog)
  ffi : HolFfiState F
  space : Nat
  tstamps : Option Nat
  limits : Limits
  safeForSpace : Bool
  peakHeapLength : Nat
  compileOracle : CompileOracle C

/-- Word size used by heap-space accounting. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "arch_size_def"]
def archSize (limits : Limits) : Nat := if limits.arch64Bit then 64 else 32

/-- An integer is immediate when it fits the source architecture's range. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "small_num_def"]
def smallNum (arch64 : Bool) (value : Int) : Prop :=
  if arch64 then -(2 ^ 61 : Int) ≤ value ∧ value < (2 ^ 61 : Int)
  else -(2 ^ 29 : Int) ≤ value ∧ value < (2 ^ 29 : Int)

/-- Read a local variable from a sparse environment. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "get_var_def"]
def getVar {α : Type} (name : Nat) (env : Spt α) : Option α := sptLookup name env

/-- Read the requested local variables in order, failing on a missing name. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "get_vars_def"]
def getVars {α : Type} : List Nat → Spt α → Option (List α)
  | [], _ => some []
  | name :: names, env => do
      let value ← getVar name env
      let values ← getVars names env
      pure (value :: values)

/-- Insert a local binding into the sparse environment. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "set_var_def"]
def setVar {C F : Type} (name : Nat) (value : Value) (state : State C F) : State C F :=
  { state with locals := sptInsert name value state.locals }

/-- Decrement the source clock by one. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "dec_clock_def"]
def decClock {C F : Type} (state : State C F) : State C F := { state with clock := state.clock - 1 }

/-- Clamp the final clock without identifying the source and target state carriers. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "fix_clock_def"]
def fixClock {C F D G R : Type} (state : State C F) (result : R × State D G) : R × State D G :=
  (result.1, { result.2 with clock := min state.clock result.2.clock })

/-- Construct the data evaluator's initial state. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "initial_state_def"]
def initialState {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × DataLang.Prog))
    (oracle : CompileOracle C) (compiler : Compiler C) (stamps : Bool) (limits : Limits)
    (stackFrameSizes : Spt Nat) (clock : Nat) : State C F :=
  ⟨.ln, some 0, [], some 1, stackFrameSizes, none, 0, .ln, compiler, clock, code, ffi, 0,
    if stamps then some 0 else none, limits, stamps, 0, oracle⟩

end Flapjack.Compiler.Backend.DataSem
