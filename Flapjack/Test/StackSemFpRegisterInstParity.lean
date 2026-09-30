import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions

/-! Kernel replay of twenty original HOL FP register/sign observations. -/
namespace Flapjack.Test.StackSemFpRegisterInstParity
open StackSemFpRegisterInstructions
private def fixture {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :=
  { s with
    clock := 6
    regs := (((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).updateEq (1, .word 10)).updateEq
      (2, .word 20)).updateEq (3, .loc 1 2)).updateEq (4, .word 77)).updateEq (5, .loc 4 5)
    fpRegs := ((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (BitVec 64)).updateEq (1, 0xfff0000000000001)).updateEq
      (2, 0x1122334455667788)).updateEq (3, 0x8000000000000000)).updateEq (4, 0) }
private def encode {width : Nat} [NeZero width] : WordLocW width → Sum Nat (Nat × Nat)
  | .word word => .inl word.toNat
  | .loc label offset => .inr (label, offset)
private def observe {width : Nat} [NeZero width] {C F : Type} :
    Option (Option (StackSemStateFiniteExact width C F)) →
    Option (Nat × Option Nat × Option (Sum Nat (Nat × Nat)) × Option (Sum Nat (Nat × Nat)))
  | some (some s) => some (s.clock, (s.fpRegs.lookup 7).map BitVec.toNat,
      (s.regs.lookup 4).map encode, (s.regs.lookup 5).map encode)
  | _ => none

-- Original fpreg_mov_nan.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMov 7 1)) (fixture s)) =
      some (6,some 18442240474082181121,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_mov_missing.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMov 7 9)) (fixture s)) =
      none := by cbv

-- Original fpreg_abs_nan.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpAbs 7 1)) (fixture s)) =
      some (6,some 9218868437227405313,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_abs_zero.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpAbs 7 3)) (fixture s)) =
      some (6,some 0,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_neg_nan.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpNeg 7 1)) (fixture s)) =
      some (6,some 9218868437227405313,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_neg_zero.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpNeg 7 4)) (fixture s)) =
      some (6,some 9223372036854775808,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_abs_missing.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpAbs 7 9)) (fixture s)) =
      none := by cbv

-- Original fpreg_neg_missing.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpNeg 7 9)) (fixture s)) =
      none := by cbv

-- Original fpreg_to64.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMovToReg 4 5 2)) (fixture s)) =
      some (6,none,some (.inl 1234605616436508552),some (.inr (4,5))) := by cbv

-- Original fpreg_to32.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovToReg 4 5 2)) (fixture s)) =
      some (6,none,some (.inl 1432778632),some (.inl 287454020)) := by cbv

-- Original fpreg_to8.
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (instFpRegister (.fp (.fpMovToReg 4 5 2)) (fixture s)) =
      some (6,none,some (.inl 136),some (.inl 68)) := by cbv

-- Original fpreg_to32_alias.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovToReg 4 4 2)) (fixture s)) =
      some (6,none,some (.inl 287454020),some (.inr (4,5))) := by cbv

-- Original fpreg_to_missing.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovToReg 4 5 9)) (fixture s)) =
      none := by cbv

-- Original fpreg_from64_ignore.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 9)) (fixture s)) =
      some (6,some 10,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_from64_loc.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 3 1)) (fixture s)) =
      none := by cbv

-- Original fpreg_from32.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 2)) (fixture s)) =
      some (6,some 85899345930,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_from8.
example {C F : Type} (s : StackSemStateFiniteExact 8 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 2)) (fixture s)) =
      some (6,some 5130,some (.inl 77),some (.inr (4,5))) := by cbv

-- Original fpreg_from32_missing.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 9)) (fixture s)) =
      none := by cbv

-- Original fpreg_from32_loc.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 3)) (fixture s)) =
      none := by cbv

-- Original fpreg_from32_alias.
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpMovFromReg 7 1 1)) (fixture s)) =
      some (6,some 42949672970,some (.inl 77),some (.inr (4,5))) := by cbv

end Flapjack.Test.StackSemFpRegisterInstParity
