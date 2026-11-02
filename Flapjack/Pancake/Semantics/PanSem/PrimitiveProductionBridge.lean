module

public import Flapjack.Pancake.Semantics.PanSemStateEval
public import Flapjack.Pancake.Semantics.PanSem.Primop
public import Flapjack.Pancake.Semantics.PanSem.EvalRuntimeRoute
public import Flapjack.Pancake.Semantics.PanSem.ValueHOL

@[expose] public section

/-!
# Concrete production primitive wiring for state-based PanSem

The generic state evaluator accepts a `PanPrimitiveHandler` so proofs and
clients can state explicit contracts. This module adds the concrete 64-bit
source-state entry point that runs the reviewed production `panPrimopHOL`.
That handler is a String/PanValue analogue rather than a direct HOL definition;
the exact definition is `panPrimopHOLExact` and no HOL tag is claimed for the
runner. `TotalEvalExpBridge` records the production/exact handler relation and
its byte-rangedness proof.

These are source-semantics execution entry points. `flapjack-compile` translates
a source program; it does not run the source evaluator while compiling it.
Consequently these entries do not assert that the compiler executable calls
`panSem` evaluation or that the compiled target program uses this evaluator.
-/

namespace Flapjack

/-- State-based production source evaluation with its concrete AddCarry
    primitive handler fixed to `panPrimopHOL`. Expressions execute through the
    guarded HOL route with the canonical RV64 word operations. -/
def panSemEvaluateRiscV64CodeStateWithProductionPrimop
    (context : PanValueFfiContext (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (program : Prog (RiscV.Word 64)) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  panSemEvaluateRiscV64CodeStateViaHOL context panPrimopHOL handler state program

/-- The concrete runner is the generic source-state evaluator with exactly the
    fixed production handler; its original parameterized interface is retained
    for explicit-handler proofs. -/
theorem panSemEvaluateRiscV64CodeStateWithProductionPrimop_eq
    (context : PanValueFfiContext (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (program : Prog (RiscV.Word 64)) :
    panSemEvaluateRiscV64CodeStateWithProductionPrimop context handler state program =
      panSemEvaluateRiscV64CodeState context panPrimopHOL handler state program :=
  panSemEvaluateRiscV64CodeStateViaHOL_eq context panPrimopHOL handler state program


/-- Declaration-to-entry RV64 source execution with the production primitive
    handler and the guarded HOL expression route. The input owns the source
    memory domains and byte order for both declarations and the body. -/
def panSemEvaluateRiscV64ProgramWithProductionPrimop
    (context : PanValueFfiContext (RiscV.Word 64))
    (input : PanSemRiscV64ProgramInput σ)
    (clock : Nat) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (fuel : Nat) (decls : List (Decl (RiscV.Word 64)))
    (entry : FunName) (arguments : List (Exp (RiscV.Word 64)))
    (memoryHandler : Option (PanValueMemoryFfiHandler (RiscV.Word 64) σ) := none) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  panSemEvaluateRiscV64ProgramViaHOL context input clock panPrimopHOL handler
    fuel decls entry arguments (memoryHandler := memoryHandler)

/-- The concrete declaration-to-entry route retains the full previous result. -/
theorem panSemEvaluateRiscV64ProgramWithProductionPrimop_eq
    (context : PanValueFfiContext (RiscV.Word 64))
    (input : PanSemRiscV64ProgramInput σ)
    (clock : Nat) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (fuel : Nat) (decls : List (Decl (RiscV.Word 64)))
    (entry : FunName) (arguments : List (Exp (RiscV.Word 64)))
    (memoryHandler : Option (PanValueMemoryFfiHandler (RiscV.Word 64) σ) := none) :
    panSemEvaluateRiscV64ProgramWithProductionPrimop context input clock handler
      fuel decls entry arguments (memoryHandler := memoryHandler) =
    evalPanValueFfiClockProgram context input.initial clock panPrimopHOL handler fuel decls entry arguments
      (memoryAccess := some (panSemBitVec64MemoryAccess input.toOwner)) (memoryHandler := memoryHandler) :=
  panSemEvaluateRiscV64ProgramViaHOL_eq context input clock panPrimopHOL handler
    fuel decls entry arguments (memoryHandler := memoryHandler)

end Flapjack
