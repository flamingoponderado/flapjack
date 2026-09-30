import Flapjack.Compiler.Backend.Semantics.StackSem.Call

/-! Kernel replay of all fourteen original HOL observations in
`scripts/hol-probes/stacksem_call_probe.out`. The concrete `evaluate` stub
reproduces the HOL sub-evaluations for the programs stored in the fixture code
map; the observer records result, clock, register 1 and stack length over an
arbitrary base state with every observed field overridden. -/

namespace Flapjack.Test.StackSemCallParity

open Flapjack.StackSemCall Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang

/-- Concrete sub-evaluator reproducing the HOL `evaluate` results for the
fixture programs `Skip`, `Return`, `Raise`, `Break`, and `Continue`. -/
def evaluateStub {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match prog with
  | .skip => (none, s)
  | .ret n =>
      match getVar n s with
      | some (.loc l1 l2) => (some (.result (.loc l1 l2)), s)
      | _ => (some .error, s)
  | .raise n =>
      match getVar n s with
      | some (.loc l1 l2) => (some (.exception (.loc l1 l2)), s)
      | _ => (some .error, s)
  | .break n => (some (.break n), s)
  | .continue n => (some (.continue n), s)
  | _ => (some .error, s)

private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    StackSemStateFiniteExact 8 C F :=
  { s with
    clock := 5
    regs := ((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (1, .word 3)).updateEq (4, .loc 4 5)).updateEq (5, .loc 6 7)).updateEq (6, .loc 8 9)
    stack := [.word 9]
    code := sptInsert 10 (.ret 4) (sptInsert 12 (.break 2)
      (sptInsert 13 (.continue 2) (sptInsert 14 (.raise 5)
        (sptInsert 15 (.skip : HolProg 8) .ln)))) }

private def observe {C F : Type}
    (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :
    Option (StackSemResult 8) × Nat × Option (WordLocW 8) × Nat :=
  (result.1, result.2.clock, result.2.regs.lookup 1, result.2.stack.length)

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)

-- call_tail_success=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F)) none (.inl 10) none
    (fixture s)) = (some (.result (.loc 4 5)), 4, some (.word 3), 1) := by cbv

-- call_tail_handler_error=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F)) none (.inl 10)
    (some (.skip, 0, 0)) (fixture s)) = (some .error, 5, some (.word 3), 1) := by cbv

-- call_tail_code_missing=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F)) none (.inl 20) none
    (fixture s)) = (some .error, 5, some (.word 3), 1) := by cbv

-- call_tail_timeout=(SOME TimeOut,0,NONE,0)
example : observe (evaluateCall (evaluateStub (C := C) (F := F)) none (.inl 10) none
    { fixture s with clock := 0 }) = (some .timeOut, 0, none, 0) := by cbv

-- call_return_success=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 10) none
    (fixture s)) = (some (.result (.loc 4 5)), 4, some (.word 3), 1) := by cbv

-- call_return_success_handler=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 10) (some (.ret 4, 6, 7))
    (fixture s)) = (some (.result (.loc 4 5)), 4, some (.word 3), 1) := by cbv

-- call_return_wrong_loc=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 6, 7)) (.inl 10) none
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

-- call_return_code_missing=(SOME Error,5,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 20) none
    (fixture s)) = (some .error, 5, some (.word 3), 1) := by cbv

-- call_return_timeout=(SOME TimeOut,0,NONE,0)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 10) none
    { fixture s with clock := 0 }) = (some .timeOut, 0, none, 0) := by cbv

-- call_exception_handled=(SOME (Result (Loc 4 5)),4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 14) (some (.ret 4, 6, 7))
    (fixture s)) = (some (.result (.loc 4 5)), 4, some (.word 3), 1) := by cbv

-- call_exception_unhandled=(SOME (Exception (Loc 6 7)),4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 14) none
    (fixture s)) = (some (.exception (.loc 6 7)), 4, some (.word 3), 1) := by cbv

-- call_exception_wrong_loc=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 14) (some (.ret 4, 8, 9))
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

-- call_return_break=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 12) none
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

-- call_return_continue=(SOME Error,4,SOME (Word 3w),1)
example : observe (evaluateCall (evaluateStub (C := C) (F := F))
    (some (.ret 4, 3, 4, 5)) (.inl 13) none
    (fixture s)) = (some .error, 4, some (.word 3), 1) := by cbv

/-! Closed helper checks: `findCode` handles direct and zero-offset indirect
lookups and misses, `eraseEq` removes the link register, and `bad_fun_return`
classifies `NONE`/`Break`/`Continue`. -/
private def checks : Bool :=
  (Flapjack.StackSemControl.findCode (.inl 10)
      (HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8))
      (sptInsert 10 (.skip : HolProg 8) .ln)).isSome &&
  (Flapjack.StackSemControl.findCode (.inl 11)
      (HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8))
      (sptInsert 10 (.skip : HolProg 8) .ln)).isNone &&
  (Flapjack.StackSemControl.findCode (.inr 4)
      (((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
        (4, .loc 10 0)))
      (sptInsert 10 (.skip : HolProg 8) .ln)).isSome &&
  ((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (3, .loc 1 2)).updateEq (4, .loc 5 6)).eraseEq 3).lookup 3 = none &&
  ((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (3, .loc 1 2)).updateEq (4, .loc 5 6)).eraseEq 3).lookup 4 = some (.loc 5 6) &&
  Flapjack.StackSemControl.badFunReturn (none : Option (StackSemResult 8)) &&
  Flapjack.StackSemControl.badFunReturn (some (.break 2) : Option (StackSemResult 8)) &&
  Flapjack.StackSemControl.badFunReturn (some (.continue 3) : Option (StackSemResult 8)) &&
  !Flapjack.StackSemControl.badFunReturn (some (.result (.loc 4 5)) : Option (StackSemResult 8)) &&
  !Flapjack.StackSemControl.badFunReturn (some (.exception (.loc 6 7)) : Option (StackSemResult 8))

#guard checks

def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact StackSem Call fragment matches original HOL branches"
    pure true
  else
    IO.println "FAIL exact StackSem Call fragment differs from original HOL branches"
    pure false

end Flapjack.Test.StackSemCallParity
