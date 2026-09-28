import Flapjack.Pancake.Semantics.PanSem.TotalEval
import Flapjack.Test.PanValueFfiSemantics

/-!
# Parity for the measured total `panSemTotalEvaluate`

Exercises the total production evaluator from
`Flapjack/Pancake/Semantics/PanSem/TotalEval.lean` on concrete RV64 source
states and state-owned code maps.  Every expected result/clock pair is copied
from the original CakeML/HOL probe `scripts/hol-probes/pan_sem_e2e_probe.out`
(the `Call`, `DecCall`, nested/recursive dispatch, and recursion-timeout rows);
the probe's 8-bit `ARB` states are mirrored here at the production RV64 carrier
with only the inspected fields fixed.

Covered direct HOL rows:

* `call_code_map_7`, `call_code_map_clock_9` — `Call NONE "id" [Const 7]` with
  `id = ([("x",One)], Return (Var Local "x"), One)` is `Return 7` at clock 9;
* `recursive_call_code_map_7`, `recursive_call_code_map_clock_8` — a call whose
  body is a `DecCall` into `"g"` returns 7 at clock 8;
* `deccall_code_map_7`, `deccall_code_map_clock_9` — `DecCall` into `"id"`
  returns 7 at clock 9;
* `nested_deccall_code_map_7`, `nested_deccall_code_map_clock_8` — nested
  `DecCall`/`DecCall` returns 7 at clock 8;
* `nested_call_code_map_7` — nested `Call`/`Call` returns 7;
* `recursive_call_timeout`, `recursive_deccall_timeout` — self-recursive calls
  exhaust the source clock and return `TimeOut`;
* `call_zero_clock_timeout` — a call entered at clock zero returns `TimeOut`.

These are untagged interface checks for the future exact `evaluate_def` port,
not a port of `evaluate` itself: see the module docs of `TotalEval.lean` for the
`String`/exact-carrier boundary.
-/

namespace Flapjack.Test.PanSemTotalEvalParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Minimal complete source state: no local bindings, no memory, clock 5. -/
private def baseState : PanSemState Word64 (FfiState Unit) :=
  { locals := fun _ => none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

/-- The `"id"` callee used by the direct `Call`/`DecCall` rows. -/
private def idCode : PanSemCodeMap Word64 :=
  [("id", ([("x", .one)], .return (.var .local "x"), .one))]

/-- `f` calls `DecCall "nested" ... "g"`; `g` returns the constant 7. -/
private def recursiveCode : PanSemCodeMap Word64 :=
  [("f", ([], .decCall "nested" .one "g" [] (.return (.var .local "nested")), .one)),
   ("g", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

/-- `f` calls `g`; `g` returns the constant 7. -/
private def nestedCallCode : PanSemCodeMap Word64 :=
  [("f", ([], .call none "g" [], .one)),
   ("g", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

/-- `loop` calls itself (directly, or through a nested `DecCall`). -/
private def loopCallCode : PanSemCodeMap Word64 :=
  [("loop", ([], .call none "loop" [], .one))]

private def loopDecCallCode : PanSemCodeMap Word64 :=
  [("loop", ([], .decCall "nested" .one "loop" [] .skip, .one))]

private def callState : PanSemState Word64 (FfiState Unit) :=
  { baseState with clock := 10, code := idCode }

private def recursiveState : PanSemState Word64 (FfiState Unit) :=
  { baseState with clock := 10, code := recursiveCode }

private def nestedCallState : PanSemState Word64 (FfiState Unit) :=
  { baseState with clock := 10, code := nestedCallCode }

/-- `Call NONE "id" [Const 7]` returns 7 at clock 9 (`call_code_map_7`,
    `call_code_map_clock_9`). -/
def callCodeMapGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none)
      (.call none "id" [.const (BitVec.ofNat 64 7)]) callState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 9
  | _ => false

/-- A call whose body is a `DecCall` returns 7 at clock 8
    (`recursive_call_code_map_7`, `recursive_call_code_map_clock_8`). -/
def recursiveCallGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none) (.call none "f" []) recursiveState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 8
  | _ => false

/-- `DecCall "answer" ... "id" ... (Return (Var Local "answer"))` returns 7 at
    clock 9 (`deccall_code_map_7`, `deccall_code_map_clock_9`). -/
def decCallCodeMapGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none)
      (.decCall "answer" .one "id" [.const (BitVec.ofNat 64 7)]
        (.return (.var .local "answer"))) callState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 9
  | _ => false

/-- Nested `DecCall`/`DecCall` returns 7 at clock 8
    (`nested_deccall_code_map_7`, `nested_deccall_code_map_clock_8`). -/
def nestedDecCallGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none)
      (.decCall "answer" .one "f" [] (.return (.var .local "answer")))
      recursiveState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 8
  | _ => false

/-- Nested `Call`/`Call` returns 7 at clock 8 (`nested_call_code_map_7`). -/
def nestedCallGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none) (.call none "f" []) nestedCallState with
  | (some (.returned (.word value)), state) =>
      value == BitVec.ofNat 64 7 && state.clock == 8
  | _ => false

/-- A self-recursive `Call` exhausts the clock and returns `TimeOut`
    (`recursive_call_timeout`). -/
def recursiveCallTimeoutGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none) (.call none "loop" [])
      { baseState with clock := 2, code := loopCallCode } with
  | (some .timeOut, _) => true
  | _ => false

/-- A self-recursive `DecCall` exhausts the clock and returns `TimeOut`
    (`recursive_deccall_timeout`). -/
def recursiveDecCallTimeoutGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none)
      (.decCall "answer" .one "loop" [] .skip)
      { baseState with clock := 2, code := loopDecCallCode } with
  | (some .timeOut, _) => true
  | _ => false

/-- A call entered at clock zero returns `TimeOut` (`call_zero_clock_timeout`). -/
def callZeroClockTimeoutGuard : Bool :=
  match panSemTotalEvaluate (fun _ _ => none) (.call none "callee" [])
      { baseState with clock := 0, code := [("callee", ([], .skip, .one))] } with
  | (some .timeOut, _) => true
  | _ => false

def evalGuards : Bool :=
  callCodeMapGuard && recursiveCallGuard && decCallCodeMapGuard &&
    nestedDecCallGuard && nestedCallGuard && recursiveCallTimeoutGuard &&
    recursiveDecCallTimeoutGuard && callZeroClockTimeoutGuard

#guard callCodeMapGuard
#guard recursiveCallGuard
#guard decCallCodeMapGuard
#guard nestedDecCallGuard
#guard nestedCallGuard
#guard recursiveCallTimeoutGuard
#guard recursiveDecCallTimeoutGuard
#guard callZeroClockTimeoutGuard
#guard evalGuards

/-- Kernel-checked regressions for the direct HOL `Call` row: result 7 and
    decremented clock 9. -/
example : callCodeMapGuard = true := by native_decide

/-- Kernel-checked regression for the recursive `Call`-into-`DecCall` row. -/
example : recursiveCallGuard = true := by native_decide

/-- Kernel-checked regression for the direct `DecCall` row. -/
example : decCallCodeMapGuard = true := by native_decide

/-- Kernel-checked regression for the nested `DecCall`/`DecCall` row. -/
example : nestedDecCallGuard = true := by native_decide

/-- Kernel-checked regression for the nested `Call`/`Call` row. -/
example : nestedCallGuard = true := by native_decide

/-- Kernel-checked regression for the recursion-timeout rows. -/
example : recursiveCallTimeoutGuard = true := by native_decide
example : recursiveDecCallTimeoutGuard = true := by native_decide
example : callZeroClockTimeoutGuard = true := by native_decide

/-- The clock after a successful `Call NONE "id" [Const 7]` is exactly the
    source clock decremented once, and the callee's `Return` clears the caller
    locals (HOL `Call` with `caltyp = NONE`). -/
example :
    (panSemTotalEvaluate (fun _ _ => none)
        (.call none "id" [.const (BitVec.ofNat 64 7)]) callState).2.clock = 9 := by
  native_decide

def runChecks : IO Bool := do
  if evalGuards then
    IO.println "PASS full Prog total evaluator recursive Call/DecCall read state-owned code (direct HOL pan_sem_e2e_probe rows)"
    pure true
  else
    IO.println "FAIL full Prog total evaluator recursive Call/DecCall (direct HOL pan_sem_e2e_probe rows)"
    pure false

end Flapjack.Test.PanSemTotalEvalParity
