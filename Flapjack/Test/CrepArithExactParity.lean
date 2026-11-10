module

public import Flapjack.Pancake.CrepArith
public import Flapjack.Misc.Words.Log2

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.CrepArith
public meta import Flapjack.Pancake.CrepLang.Exp
public meta import Flapjack.Pancake.CrepLang.Prog
public meta import Flapjack.Pancake.Semantics.PanSem
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Exact-carrier parity for the `crep_arith` ports

Replays the direct HOL-EVAL rows of

* `scripts/hol-probes/crep_dest_2exp_probe.out`
* `scripts/hol-probes/crep_mul_const_probe.out`
* `scripts/hol-probes/crep_simp_exp_probe.out`
* `scripts/hol-probes/crep_simp_prog_probe.out`

against the tagged exact-carrier ports `crepDest2ExpHOL`, `crepMulConstHOL`,
`crepSimpExpHOL` and `crepSimpProgHOL` over `CrepExpHOL 8` / `CrepProgHOL 8`.

`dest_2exp`/`mul_const` rows are kernel-checked `example`s; `simp_exp`/
`simp_prog` rows are replayed through `#guard` on the executable definitions
(their well-founded recursion is not reducible by `simp`, so no proof term is
produced and no trusted-evaluator axiom is attached).
-/

set_option linter.unusedSimpArgs false

namespace Flapjack.Test.CrepArithExactParity

open Flapjack

-- Expose the generated recursive equation for concrete multiplication rows.
theorem simpMul {width : Nat} [NeZero width] (left right : CrepExpHOL width) :
    crepSimpExpHOL (.crepOp .mul [left, right]) =
      match crepDestConstHOL (crepSimpExpHOL left), crepDestConstHOL (crepSimpExpHOL right) with
      | some x, some y => .const (x * y)
      | some x, none => crepMulConstHOL (crepSimpExpHOL right) x
      | none, some y => crepMulConstHOL (crepSimpExpHOL left) y
      | none, none => .crepOp .mul [crepSimpExpHOL left, crepSimpExpHOL right] := by
  have h : List.map crepSimpExpHOL [left, right] =
      [crepSimpExpHOL left, crepSimpExpHOL right] := rfl
  rw [crepSimpExpHOL.eq_1 [left, right]
    (crepSimpExpHOL left) (crepSimpExpHOL right) h]
  rfl

private abbrev E := CrepExpHOL 8
private abbrev P := CrepProgHOL 8

private def mul (left right : E) : E := .crepOp .mul [left, right]

private def isConst6 : E → Bool
  | .const 6 => true
  | _ => false

private def isConst24 : E → Bool
  | .const 24 => true
  | _ => false

private def isShiftVar2Const1 : E → Bool
  | .shift .lsl (.var 2) (.const 1) => true
  | _ => false

private def isShiftVar2Const3 : E → Bool
  | .shift .lsl (.var 2) (.const 3) => true
  | _ => false

private def isMulVar2Const3 : E → Bool
  | .crepOp .mul [.var 2, .const 3] => true
  | _ => false

private def isMulVar2Var3 : E → Bool
  | .crepOp .mul [.var 2, .var 3] => true
  | _ => false

private def isLoadShift : E → Bool
  | .load (.shift .lsl (.var 2) (.const 1)) => true
  | _ => false

private def isOpAddShift : E → Bool
  | .op .add [.shift .lsl (.var 2) (.const 1)] => true
  | _ => false

private def isVar7 : E → Bool
  | .var 7 => true
  | _ => false

private def isAssign1Shift : P → Bool
  | .assign 1 (.shift .lsl (.var 2) (.const 1)) => true
  | _ => false

private def isDecReturn : P → Bool
  | .dec 1 (.const 6) (.return [.var 1]) => true
  | _ => false

private def isStoreVar2Shift : P → Bool
  | .store (.var 2) (.shift .lsl (.var 3) (.const 1)) => true
  | _ => false

private def isBreak3 : P → Bool
  | .break 3 => true
  | _ => false

-- `crep_dest_2exp_probe.out` (kernel-checked)
example : crepDest2ExpHOL (width := 8) 0 0 = none := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 1 = some 0 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 2 = some 1 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 4 = some 2 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 8 = some 3 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 3 1 = some 3 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 3 = none := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 6 = none := by simp [crepDest2ExpHOL]

-- Remaining recognizer, shift, and word_log2 bound rows of the HOL probe.
example : crepDest2ExpHOL (width := 8) 4 4 = some 6 := by simp [crepDest2ExpHOL]
example : crepDest2ExpHOL (width := 8) 0 255 = none := by simp [crepDest2ExpHOL]
example : (1 : BitVec 8) <<< 3 = 8 := by decide
example : (1 : BitVec 8) <<< 7 = 128 := by decide
example : crepDest2ExpHOL (width := 8) 3 1 = some 3 →
    3 ≤ 3 + (holWordLog2 (1 : BitVec 8)).toNat := by intro _; decide
example : crepDest2ExpHOL (width := 8) 4 4 = some 6 →
    6 ≤ 4 + (holWordLog2 (4 : BitVec 8)).toNat := by intro _; decide
example : crepDest2ExpHOL (width := 8) 0 8 = some 3 →
    3 ≤ 0 + (holWordLog2 (8 : BitVec 8)).toNat := by intro _; decide

-- `crep_mul_const_probe.out` (kernel-checked)
example : crepMulConstHOL (width := 8) (.var 2) 0 = .const 0 := by
  simp [crepMulConstHOL, crepDest2ExpHOL]
example : crepMulConstHOL (width := 8) (.var 2) 1 = .var 2 := by
  simp [crepMulConstHOL, crepDest2ExpHOL]
example : crepMulConstHOL (width := 8) (.var 2) 2 =
    .shift .lsl (.var 2) (.const 1) := by simp [crepMulConstHOL, crepDest2ExpHOL]
example : crepMulConstHOL (width := 8) (.var 2) 3 = mul (.var 2) (.const 3) := by
  simp [crepMulConstHOL, crepDest2ExpHOL, mul]
example : crepMulConstHOL (width := 8) (.var 2) 4 =
    .shift .lsl (.var 2) (.const 2) := by simp [crepMulConstHOL, crepDest2ExpHOL]
example : crepMulConstHOL (width := 8) (.var 2) 8 =
    .shift .lsl (.var 2) (.const 3) := by simp [crepMulConstHOL, crepDest2ExpHOL]

-- `crep_simp_exp_probe.out`
#guard isConst6 (crepSimpExpHOL (width := 8) (mul (.const 2) (.const 3)))
#guard isShiftVar2Const1 (crepSimpExpHOL (width := 8) (mul (.var 2) (.const 2)))
#guard isShiftVar2Const1 (crepSimpExpHOL (width := 8) (mul (.const 2) (.var 2)))
#guard isMulVar2Const3 (crepSimpExpHOL (width := 8) (mul (.var 2) (.const 3)))
#guard isConst24 (crepSimpExpHOL (width := 8) (mul (.const 4) (mul (.const 2) (.const 3))))
#guard isLoadShift (crepSimpExpHOL (width := 8) (.load (mul (.var 2) (.const 2))))
#guard isOpAddShift (crepSimpExpHOL (width := 8) (.op .add [mul (.var 2) (.const 2)]))
#guard isMulVar2Var3 (crepSimpExpHOL (width := 8) (mul (.var 2) (.var 3)))
#guard isVar7 (crepSimpExpHOL (width := 8) (.var 7))

-- `crep_simp_prog_probe.out`
#guard isAssign1Shift (crepSimpProgHOL (width := 8) (.assign 1 (mul (.var 2) (.const 2))))
#guard isDecReturn (crepSimpProgHOL (width := 8) (.dec 1 (mul (.const 2) (.const 3)) (.return [.var 1])))
#guard isStoreVar2Shift (crepSimpProgHOL (width := 8) (.store (.var 2) (mul (.var 3) (.const 2))))
#guard isBreak3 (crepSimpProgHOL (width := 8) (.break 3))

-- Remaining full program rows in `crep_simp_prog_probe.out`.
#guard match crepSimpProgHOL (width := 8) (.store32 (.var 2) (mul (.var 3) (.const 2))) with
  | .store32 (.var 2) (.shift .lsl (.var 3) (.const 1)) => true | _ => false
#guard match crepSimpProgHOL (width := 8) (.storeByte (.var 2) (mul (.var 3) (.const 2))) with
  | .storeByte (.var 2) (.shift .lsl (.var 3) (.const 1)) => true | _ => false
#guard match crepSimpProgHOL (width := 8) (.storeGlob 4 (mul (.var 3) (.const 2))) with
  | .storeGlob 4 (.shift .lsl (.var 3) (.const 1)) => true | _ => false
#guard match crepSimpProgHOL (width := 8)
    (.seq (.ite (mul (.var 2) (.const 2)) (.assign 1 (.const 4))
      (.while (mul (.var 3) (.const 2)) .skip)) (.return [mul (.var 4) (.const 2)])) with
  | .seq (.ite (.shift .lsl (.var 2) (.const 1)) (.assign 1 (.const 4))
      (.while (.shift .lsl (.var 3) (.const 1)) .skip))
      (.return [.shift .lsl (.var 4) (.const 1)]) => true | _ => false
#guard match crepSimpProgHOL (width := 8)
    (.call none (Flapjack.Basis.Pure.MlString.ofString "f") [mul (.var 2) (.const 2)]) with
  | .call none name [.shift .lsl (.var 2) (.const 1)] =>
      name == Flapjack.Basis.Pure.MlString.ofString "f" | _ => false
#guard match crepSimpProgHOL (width := 8)
    (.call (some ([1], some (7, .assign 2 (mul (.var 3) (.const 2)))))
      (Flapjack.Basis.Pure.MlString.ofString "f") [.var 4]) with
  | .call (some ([1], some (7, .assign 2 (.shift .lsl (.var 3) (.const 1))))) name [.var 4] =>
      name == Flapjack.Basis.Pure.MlString.ofString "f"
  | _ => false
#guard match crepSimpProgHOL (width := 8)
    (.seq (.shMem .load 1 (mul (.var 2) (.const 2))) (.return [mul (.var 3) (.const 2)])) with
  | .seq (.shMem .load 1 (.shift .lsl (.var 2) (.const 1)))
      (.return [.shift .lsl (.var 3) (.const 1)]) => true | _ => false

-- Preserve the earlier constant-folding regression inputs on the executed carrier.
#guard match crepSimpExpHOL (width := 8) (mul (.const 7) (.const 9)) with
  | .const 63 => true | _ => false
#guard match crepSimpProgHOL (width := 8)
    (.seq (.assign 0 (mul (.const 6) (.const 7))) (.return [mul (.const 8) (.const 5)])) with
  | .seq (.assign 0 (.const 42)) (.return [.const 40]) => true | _ => false

-- `crep_dest_2exp_probe` / `crep_mul_const_probe` executable rows
#guard crepDest2ExpHOL (width := 8) 0 8 == some 3
#guard crepDest2ExpHOL (width := 8) 0 3 == none

def runChecks : IO Bool := do
  let ok := crepDest2ExpHOL (width := 8) 0 8 == some 3 &&
    crepDest2ExpHOL (width := 8) 0 3 == none &&
    isShiftVar2Const3 (crepMulConstHOL (width := 8) (.var 2) 8) &&
    isConst6 (crepSimpExpHOL (width := 8) (mul (.const 2) (.const 3))) &&
    isMulVar2Const3 (crepSimpExpHOL (width := 8) (mul (.var 2) (.const 3))) &&
    isLoadShift (crepSimpExpHOL (width := 8) (.load (mul (.var 2) (.const 2)))) &&
    isAssign1Shift (crepSimpProgHOL (width := 8) (.assign 1 (mul (.var 2) (.const 2)))) &&
    isBreak3 (crepSimpProgHOL (width := 8) (.break 3))
  if ok then
    IO.println "PASS crep_arith exact-carrier ports match direct HOL probe rows (dest_2exp / mul_const / simp_exp / simp_prog)"
  else
    IO.println "FAIL crep_arith exact-carrier ports match direct HOL probe rows (dest_2exp / mul_const / simp_exp / simp_prog)"
  return ok

end Flapjack.Test.CrepArithExactParity