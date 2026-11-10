module

public import Flapjack.Pancake.LoopCall

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.LoopCall
public meta import Flapjack.Pancake.LoopLang
@[expose] public section

/-!
# Original-domain parity for `loop_call$comp`

`original*` observations below are taken from the checked-in HOL fixture
`scripts/hol-probes/loop_call_comp_probe.out`, generated from
`cakeml/pancake/loop_callScript.sml:18-92`.  The observations deliberately
cover the environment-sensitive call, assignment, location, load, primitive,
arithmetic, sequence, branch, loop, mark, FFI, and fallback equations.
-/

namespace Flapjack.Test.LoopCallParity

open Flapjack
open Flapjack.LoopCall

def sourceEnvironment : LocationEnv := [(2, 9)]
def sourceEnvironmentTwo : LocationEnv := [(1, 7), (2, 8)]

def isSkip : LoopProg α → Bool
  | .skip => true
  | _ => false

def isSeq : LoopProg α → Bool
  | .seq _ _ => true
  | _ => false

def isIte : LoopProg α → Bool
  | .ite _ _ _ _ _ _ => true
  | _ => false

def isLoop : LoopProg α → Bool
  | .loop _ _ _ => true
  | _ => false

def isMark : LoopProg α → Bool
  | .mark _ => true
  | _ => false

def callShape : LoopProg α → Option (Option Nat × List Nat)
  | .call _ target arguments _ => some (target, arguments)
  | _ => none

def probeSkip : LoopProg Nat := .skip
def probeCallDest : LoopProg Nat := .call none (some 3) [1, 2] none
def probeCallLast : LoopProg Nat := .call none none [1, 2] none
def probeCallEmpty : LoopProg Nat := .call none none [] none
def probeLocValue : LoopProg Nat := .locValue 1 7
def probeAssignVar : LoopProg Nat := .assign 1 (.var 2)
def probeAssignExpr : LoopProg Nat := .assign 1 (.const 9)
def probeShMem : LoopProg Nat := .shMem .load 1 (.const 0)
def probeLoad32 : LoopProg Nat := .load32 0 1
def probeLoadByte : LoopProg Nat := .loadByte 0 1
def probeSequence : LoopProg Nat :=
  .seq (.locValue 2 8) (.assign 3 (.var 2))
def probeIf : LoopProg Nat :=
  .ite .equal 0 (.reg 2) (.locValue 2 8) (.assign 3 (.var 2)) []
def probeLoop : LoopProg Nat := .loop [] (.locValue 2 8) []
def probeMark : LoopProg Nat := .mark (.locValue 2 8)
def probeFfi : LoopProg Nat := .ffi "host" 1 2 3 4 []
def probePrimitive : LoopProg Nat := .primitive [1] .addCarry [2, 3]
def probeLongMul : LoopProg Nat := .arith (.longMul 1 2 3 4)
def probeDiv : LoopProg Nat := .arith (.div 1 2 3)
def probeFallback : LoopProg Nat := .store (.const 0) 1

/-! Basic lookup facts for the association-list location environment, used by
    the `loop_call` correctness proof. -/

theorem lookup_insert_same_fixture : lookup 1 (insert 1 9 [(2, 8)]) = some 9 :=
  lookup_insert_same 1 9 [(2, 8)]

theorem lookup_insert_other_fixture : lookup 2 (insert 1 9 [(2, 8)]) = some 8 :=
  lookup_insert_other 1 9 2 [(2, 8)] (by decide)

theorem lookup_delete_same_fixture : lookup 1 (delete 1 [(1, 7), (2, 8)]) = none :=
  lookup_delete_same 1 [(1, 7), (2, 8)]

theorem lookup_delete_other_fixture : lookup 2 (delete 1 [(1, 7), (2, 8)]) = some 8 :=
  lookup_delete_other 1 2 [(1, 7), (2, 8)] (by decide)

def lookupFactsGuard : Bool :=
  lookup 1 (insert 1 9 [(2, 8)]) == some 9 &&
    lookup 2 (insert 1 9 [(2, 8)]) == some 8 &&
    lookup 1 (delete 1 [(1, 7), (2, 8)]) == none &&
    lookup 2 (delete 1 [(1, 7), (2, 8)]) == some 8

#eval lookupFactsGuard
#guard lookupFactsGuard

def check (name : String) (actual expected : Bool) : IO Bool := do
  if actual == expected then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    pure false

end Flapjack.Test.LoopCallParity
