import Flapjack.Compiler.Backend.Semantics.StackSem.ControlCases
import Flapjack.Compiler.Backend.Semantics.StackSem.LeafTransfers

/-! Test-only recursive Loop evaluator over real leaf bodies. Re-entry runs
again with the decremented clock; no callback fabricates a terminal timeout.
This restricted test evaluator is untagged and does not assemble evaluate_def.
Unsupported bodies are explicit test markers and are excluded by the fixture
coverage certificate. -/
namespace Flapjack.Test.StackSemLoopRecursiveParity
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang
private abbrev State := StackSemStateFiniteExact 8 Unit Unit
private abbrev W := WordLocW 8

private def leafEvaluate (body : HolProg 8) (s : State) :
    Option (StackSemResult 8) × State :=
  (StackSemLeafTransfers.evaluateLeaf body s).getD (some .error, s)

/-- Source Loop equation, with real recursive re-entry and a decreasing clock.
The body uses evaluateLeaf; the fragment equation below checks the factoring. -/
def loopEvaluate (body : HolProg 8) (s : State) :
    Option (StackSemResult 8) × State :=
  let rs := fixClock s (leafEvaluate body s)
  if contLoop rs.1 then
    if _h : rs.2.clock = 0 then (some .timeOut, emptyEnv rs.2)
    else loopEvaluate body (decClock rs.2)
  else (StackSemControl.exitLoop rs.1, rs.2)
termination_by s.clock
decreasing_by
  exact Nat.lt_of_lt_of_le (decClock_clock_lt _ _h) (fixClock_clock_le s _)

/-- Every re-entry is dispatched to the actual recursive function. This
callback recognizes the reached Loop before falling back to real leaf clauses. -/
private def callback (p : HolProg 8) (s : State) :
    Option (StackSemResult 8) × State :=
  match p with
  | .loop body => loopEvaluate body s
  | _ => leafEvaluate p s

/-- Factoring check against the existing reviewed Loop fragment for every
non-Loop body. The fixture coverage below separately rules out unhandled leaves. -/
theorem loopEvaluate_eq_fragment (body : HolProg 8) (s : State)
    (hbody : ∀ b, body ≠ .loop b) :
    loopEvaluate body s = StackSemControlCases.evaluateLoop callback body s := by
  have hc : callback body s = leafEvaluate body s := by
    cases body <;> simp_all [callback]
  rw [loopEvaluate]
  unfold StackSemControlCases.evaluateLoop
  rw [hc]
  rfl

private def s0 : State where
  regs := (((HolFiniteMapExact.empty : HolFiniteMapExact Nat W).updateEq
    (1, .word 3)).updateEq (3, .loc 10 0)).updateEq (4, .loc 4 5)
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := [.word 9]
  stackSpace := 0
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  bitmaps := []
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [], [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  useStack := false
  useStore := false
  useAlloc := false
  clock := 5
  code := .ln
  ffi := { oracle := fun _ _ _ _ => .final .diverged, ffiState := (), ioEvents := [] }
  ffiSaveRegs := fun _ => false
  be := false


private def observe (rs : Option (StackSemResult 8) × State) :
    Option (StackSemResult 8) × Nat × Option W × Nat :=
  (rs.1, rs.2.clock, rs.2.regs.lookup 1, rs.2.stack.length)

private inductive RView where
  | none | timeOut | error | break (n : Nat) | continue (n : Nat)
  | result (a b : Nat) | exception (a b : Nat) | haltWord (n : Nat) | other
  deriving DecidableEq
private def view : Option (StackSemResult 8) → RView
  | none => .none
  | some .timeOut => .timeOut
  | some .error => .error
  | some (.break n) => .break n
  | some (.continue n) => .continue n
  | some (.result (.loc a b)) => .result a b
  | some (.exception (.loc a b)) => .exception a b
  | some (.halt (.word w)) => .haltWord w.toNat
  | _ => .other
private def observed (body : HolProg 8) (clock : Nat) :=
  let rs := loopEvaluate body { s0 with clock := clock }
  (view rs.1, rs.2.clock, rs.2.regs.lookup 1, rs.2.stack.length)

-- continue_three
example : observed (.continue 0) 3 = (.timeOut, 0, none, 0) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.continue 0) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- skip_three
example : observed (.skip) 3 = (.timeOut, 0, none, 0) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.skip) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- tick_three
example : observed (.tick) 3 = (.timeOut, 0, none, 0) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.tick) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- tick_zero
example : observed (.tick) 0 = (.timeOut, 0, none, 0) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.tick) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- break_zero
example : observed (.break 0) 5 = (.none, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.break 0) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- break_two
example : observed (.break 2) 5 = (.break 1, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.break 2) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- continue_two
example : observed (.continue 2) 5 = (.continue 1, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.continue 2) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- return_location
example : observed (.ret 4) 5 = (.result 4 5, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.ret 4) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- return_word_error
example : observed (.ret 1) 5 = (.error, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.ret 1) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- raise_location
example : observed (.raise 4) 5 = (.exception 4 5, 5, some (.word 3), 1) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.raise 4) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]
-- halt_word
example : observed (.halt 1) 5 = (.haltWord 3, 5, none, 0) := by cbv
example (state : State) : (StackSemLeafTransfers.evaluateLeaf (.halt 1) state).isSome = true := by
  simp only [StackSemLeafTransfers.evaluateLeaf]
  repeat' first | split | simp only [Option.isSome_some]

/-- Actual runtime comparisons of every captured original row. -/
def rows : List (String × Bool) :=
  [("continue_three", decide (observed (.continue 0) 3 = (.timeOut, 0, none, 0))),
   ("skip_three", decide (observed (.skip) 3 = (.timeOut, 0, none, 0))),
   ("tick_three", decide (observed (.tick) 3 = (.timeOut, 0, none, 0))),
   ("tick_zero", decide (observed (.tick) 0 = (.timeOut, 0, none, 0))),
   ("break_zero", decide (observed (.break 0) 5 = (.none, 5, some (.word 3), 1))),
   ("break_two", decide (observed (.break 2) 5 = (.break 1, 5, some (.word 3), 1))),
   ("continue_two", decide (observed (.continue 2) 5 = (.continue 1, 5, some (.word 3), 1))),
   ("return_location", decide (observed (.ret 4) 5 = (.result 4 5, 5, some (.word 3), 1))),
   ("return_word_error", decide (observed (.ret 1) 5 = (.error, 5, some (.word 3), 1))),
   ("raise_location", decide (observed (.raise 4) 5 = (.exception 4 5, 5, some (.word 3), 1))),
   ("halt_word", decide (observed (.halt 1) 5 = (.haltWord 3, 5, none, 0)))]

#guard rows.length == 11
#guard rows.all (·.2)

def runChecks : IO Bool := do
  let bad := rows.filter (fun row => !row.2)
  if bad.isEmpty && rows.length == 11 then
    IO.println "PASS recursive StackSem Loop matches all 11 original HOL rows without a timeout stub"
    pure true
  else
    IO.println s!"FAIL recursive StackSem Loop rows: {bad.map (·.1)}"
    pure false
end Flapjack.Test.StackSemLoopRecursiveParity
