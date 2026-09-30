import Flapjack.Compiler.Backend.Semantics.StackSem.IntegerInstructions

/-! Kernel replay of the 33 canonicalized original HOL instruction rows. -/
namespace Flapjack.Test.StackSemIntegerInstParity
open StackSemIntegerInstructions StackSemStateOps StackSemExpressions
private def fixture {C F : Type} (s : StackSemStateFiniteExact 8 C F) :=
  { s with
    clock := 6
    regs := ((((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 8)).updateEq
      (1, .loc 4 5)).updateEq (2, .word 250)).updateEq (3, .word 10)).updateEq
      (4, .word 1)).updateEq (5, .word 0)).updateEq (6, .word 10)
    memory := fun _ => .word 123
    mdomain := fun _ => true
    be := false }
private def encode {width : Nat} [NeZero width] : WordLocW width → Sum Nat (Nat × Nat)
  | .word w => .inl w.toNat
  | .loc a b => .inr (a,b)
private def observe {width : Nat} [NeZero width] {C F : Type} (address : BitVec width) : Option (Option (StackSemStateFiniteExact width C F)) →
    Option (Nat × Option (Sum Nat (Nat × Nat)) × Option (Sum Nat (Nat × Nat)) × Sum Nat (Nat × Nat))
  | some (some s) => some (s.clock, (s.regs.lookup 7).map encode,
      (s.regs.lookup 4).map encode, encode (s.memory address))
  | _ => none
variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
-- skip
example : observe 10 (instInteger (.skip) (fixture s)) = some (6, none, some (.inl 1), (.inl 123)) := by
  cbv
-- const
example : observe 10 (instInteger (.const 7 17) (fixture s)) = some (6, some (.inl 17), some (.inl 1), (.inl 123)) := by
  cbv
-- or_loc
example : observe 10 (instInteger (.arith (.binop .or 7 1 (.reg 1))) (fixture s)) = some (6, some (.inr (4,5)), some (.inl 1), (.inl 123)) := by
  cbv
-- or_missing
example : observe 10 (instInteger (.arith (.binop .or 7 9 (.reg 9))) (fixture s)) = none := by
  cbv
-- or_loc_general
example : observe 10 (instInteger (.arith (.binop .or 7 1 (.reg 2))) (fixture s)) = none := by
  cbv
-- add
example : observe 10 (instInteger (.arith (.binop .add 7 2 (.reg 3))) (fixture s)) = some (6, some (.inl 4), some (.inl 1), (.inl 123)) := by
  cbv
-- shift
example : observe 10 (instInteger (.arith (.shift .lsl 7 3 (.imm 1))) (fixture s)) = some (6, some (.inl 20), some (.inl 1), (.inl 123)) := by
  cbv
-- div
example : observe 10 (instInteger (.arith (.div 7 2 3)) (fixture s)) = some (6, some (.inl 0), some (.inl 1), (.inl 123)) := by
  cbv
-- div_zero
example : observe 10 (instInteger (.arith (.div 7 2 5)) (fixture s)) = none := by
  cbv
-- carry
example : observe 10 (instInteger (.arith (.addCarry 7 2 3 4)) (fixture s)) = some (6, some (.inl 5), some (.inl 1), (.inl 123)) := by
  cbv
-- carry_alias
example : observe 10 (instInteger (.arith (.addCarry 4 2 3 4)) (fixture s)) = some (6, none, some (.inl 1), (.inl 123)) := by
  cbv
-- add_overflow
example : observe 10 (instInteger (.arith (.addOverflow 7 2 3 4)) (fixture s)) = some (6, some (.inl 4), some (.inl 0), (.inl 123)) := by
  cbv
-- sub_overflow
example : observe 10 (instInteger (.arith (.subOverflow 7 2 3 4)) (fixture s)) = some (6, some (.inl 240), some (.inl 0), (.inl 123)) := by
  cbv
-- long_mul
example : observe 10 (instInteger (.arith (.longMul 7 4 2 3)) (fixture s)) = some (6, some (.inl 9), some (.inl 196), (.inl 123)) := by
  cbv
-- long_div
example : observe 10 (instInteger (.arith (.longDiv 7 4 5 2 3)) (fixture s)) = some (6, some (.inl 25), some (.inl 0), (.inl 123)) := by
  cbv
-- long_div_overflow
example : observe 10 (instInteger (.arith (.longDiv 7 4 2 2 3)) (fixture s)) = none := by
  cbv
-- load
example : observe 10 (instInteger (.mem .load 7 (.addr 6 0)) (fixture s)) = some (6, some (.inl 123), some (.inl 1), (.inl 123)) := by
  cbv
-- load8
example : observe 10 (instInteger (.mem .load8 7 (.addr 6 0)) (fixture s)) = some (6, some (.inl 123), some (.inl 1), (.inl 123)) := by
  cbv
-- load16
example : observe 10 (instInteger (.mem .load16 7 (.addr 6 0)) (fixture s)) = none := by
  cbv
-- load32
example : observe 10 (instInteger (.mem .load32 7 (.addr 6 0)) (fixture s)) = none := by
  cbv
-- store_loc
example : observe 10 (instInteger (.mem .store 1 (.addr 6 0)) (fixture s)) = some (6, none, some (.inl 1), (.inr (4,5))) := by
  cbv
-- store8
example : observe 10 (instInteger (.mem .store8 2 (.addr 6 0)) (fixture s)) = some (6, none, some (.inl 1), (.inl 250)) := by
  cbv
-- store16
example : observe 10 (instInteger (.mem .store16 2 (.addr 6 0)) (fixture s)) = none := by
  cbv
-- store32
example : observe 10 (instInteger (.mem .store32 2 (.addr 6 0)) (fixture s)) = none := by
  cbv
-- store8_loc
example : observe 10 (instInteger (.mem .store8 1 (.addr 6 0)) (fixture s)) = none := by
  cbv
private def fixture64 {C F : Type} (s : StackSemStateFiniteExact 64 C F)
    (bigEndian enabled : Bool) :=
  { s with
    clock := 6
    regs := ((((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW 64)).updateEq
      (1, .loc 4 5)).updateEq (2, .word 250)).updateEq (3, .word 10)).updateEq
      (4, .word 1)).updateEq (5, .word 0)).updateEq (6, .word 8)
    memory := fun _ => .word 123
    mdomain := fun _ => enabled
    be := bigEndian }
variable (s64 : StackSemStateFiniteExact 64 C F)
-- load32_64
example : observe 8 (instInteger (.mem .load32 7 (.addr 6 0)) (fixture64 s64 false true)) =
    some (6, some (.inl 123), some (.inl 1), .inl 123) := by cbv
-- store32_64
example : observe 8 (instInteger (.mem .store32 2 (.addr 6 0)) (fixture64 s64 false true)) =
    some (6, none, some (.inl 1), .inl 250) := by cbv
-- load32_64_be
example : observe 8 (instInteger (.mem .load32 7 (.addr 6 0)) (fixture64 s64 true true)) =
    some (6, some (.inl 0), some (.inl 1), .inl 123) := by cbv
-- store32_64_be
example : observe 8 (instInteger (.mem .store32 2 (.addr 6 0)) (fixture64 s64 true true)) =
    some (6, none, some (.inl 1), .inl 1073741824123) := by cbv
-- store8_64_offset
example : observe 8 (instInteger (.mem .store8 2 (.addr 6 1)) (fixture64 s64 false true)) =
    some (6, none, some (.inl 1), .inl 64123) := by cbv
-- store8_64_offset_be
example : observe 8 (instInteger (.mem .store8 2 (.addr 6 1)) (fixture64 s64 true true)) =
    some (6, none, some (.inl 1), .inl 70368744177664123) := by cbv
-- load8_no_domain
example : observe 8 (instInteger (.mem .load8 7 (.addr 6 0)) (fixture64 s64 false false)) =
    none := by cbv
-- store32_no_domain
example : observe 8 (instInteger (.mem .store32 2 (.addr 6 0)) (fixture64 s64 false false)) =
    none := by cbv
end Flapjack.Test.StackSemIntegerInstParity
