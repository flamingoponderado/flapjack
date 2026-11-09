import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiCore

/-!
Direct regression for the source `PanSemState` code-map `Dec` error
equations.  HOL `panSemScript.sml:558-565` rejects a `Dec` whose initialiser
expression fails to evaluate, or whose value does not match the declared
shape, with `SOME Error` over the unchanged state.  The expected values are the
original-HOL `EVAL` rows in `scripts/hol-probes/pan_sem_dec_e2e_probe.out`:

* `dec_eval_missing_result=SOME Error`, `dec_eval_missing_locals=SOME (ValWord 3w)`,
  `dec_eval_missing_clock=5`;
* `dec_shape_mismatch_result=SOME Error`,
  `dec_shape_mismatch_locals=SOME (ValWord 3w)`,
  `dec_shape_mismatch_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemDecErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def localsWithX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state with a present memory cell at address `8` and
    local `x`, evaluated at clock 5. -/
private def memoryState : PanSemState Word64 (FfiState Unit) :=
  { locals := localsWithX
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := exactMemory
    memaddrs := exactDomain
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def decEvalFailProgram : Prog Word64 :=
  .dec "d" Shape.one (.load Shape.one (.const 11)) .skip

private def decShapeMismatchProgram : Prog Word64 :=
  .dec "d" (Shape.named "Other") (.const 7) .skip

private def evaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

/-- An `Error` control result at `clock` that keeps local `x` at `localValue`. -/
private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock &&
            (match locals "x" with
             | some (.word value) => value == BitVec.ofNat 64 localValue
             | _ => false)
      | _ => false
  | _ => false

private def decEvalFailGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState decEvalFailProgram)

private def decShapeMismatchGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState decShapeMismatchProgram)

private def decErrorGuard : Bool :=
  decEvalFailGuard && decShapeMismatchGuard

#guard decErrorGuard

def runChecks : IO Bool := do
  IO.println (if decEvalFailGuard then
    "PASS source Dec failing initialiser keeps state and clock"
   else "FAIL source Dec failing initialiser keeps state and clock")
  IO.println (if decShapeMismatchGuard then
    "PASS source Dec shape mismatch keeps state and clock"
   else "FAIL source Dec shape mismatch keeps state and clock")
  pure decErrorGuard

end Flapjack.Test.PanSemDecErrorExactParity
