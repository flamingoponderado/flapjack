import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions
import Flapjack.Misc.BinaryIeeeArithFp64
import Flapjack.Misc.BinaryIeeeSqrtFp64

/-! Kernel replay of twenty original HOL FP register/sign observations, all
fourteen rows of `stacksem_fp_arith_probe.out` for the FP comparison and
arithmetic cases of `inst_def`, and all eleven rows of
`stacksem_fp_convert_probe.out` for the FPSqrt/FPToInt/FPFromInt cases
(`cakeml/compiler/backend/semantics/stackSemScript.sml:519-542` for
FPLess/FPLessEqual/FPEqual, `:563-587` for FPAdd/FPSub/FPMul/FPDiv/FPFma, and
`:559-562`/`:605-624`/`:625-640` for FPSqrt/FPToInt/FPFromInt).
The fragment is an untagged partial case dispatcher; the whole `inst_def`
assembly is tracked separately. The comparison rows evaluate the computable
HOL comparison renderings directly; the arithmetic and FMA rows replay through
the proven computable-rounding equivalences of
`Flapjack.Misc.BinaryIeeeArithFp64`; the FPSqrt row uses `holFp64Sqrt_rte`
(`Flapjack.Misc.BinaryIeeeSqrtFp64`), the FPFromInt rows use `holIntToFp64_rte`
(`Flapjack.Misc.BinaryIeeeConvert`), and the FPToInt rows use the computable
`holFp64ToInt`. Structural examples below prove the exact returned expression
of every new case, including the `FPFma` addend permutation. -/
namespace Flapjack.Test.StackSemFpRegisterInstParity
open StackSemFpRegisterInstructions StackSemStateOps
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

-- Binary64 values used by the FP comparison and arithmetic probe rows.
private def one   : BitVec 64 := 0x3FF0000000000000
private def two   : BitVec 64 := 0x4000000000000000
private def three : BitVec 64 := 0x4008000000000000
private def six   : BitVec 64 := 0x4018000000000000
private def ten   : BitVec 64 := 0x4024000000000000
private def arithFixture {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :=
  { s with
    clock := 6
    regs := (((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).updateEq (1, .word 10)).updateEq
      (2, .word 20)).updateEq (3, .loc 1 2)).updateEq (4, .word 77)).updateEq (5, .loc 4 5)
    fpRegs := (((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (BitVec 64)).updateEq (1, one)).updateEq
      (2, two)).updateEq (3, three)).updateEq (4, six)).updateEq (7, ten) }

-- Structural kernel checks of the exact returned expression for each new case,
-- given the FP lookups. These do not evaluate the noncomputable arithmetic;
-- they prove the case shape and, for `FPFma`, the argument permutation.
-- HOL stackSemScript.sml:519-542, :563-587.
example {width : Nat} [NeZero width] {C F : Type}
    (r d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = some f2) :
    instFpRegister (.fp (.fpLess r d1 d2)) s =
      some (some (setVar r (.word (if holFp64LessThan f1 f2
        then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)) := by
  simp [instFpRegister, h1, h2]

example {width : Nat} [NeZero width] {C F : Type}
    (r d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = some f2) :
    instFpRegister (.fp (.fpLessEqual r d1 d2)) s =
      some (some (setVar r (.word (if holFp64LessEqual f1 f2
        then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)) := by
  simp [instFpRegister, h1, h2]

example {width : Nat} [NeZero width] {C F : Type}
    (r d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = some f2) :
    instFpRegister (.fp (.fpEqual r d1 d2)) s =
      some (some (setVar r (.word (if holFp64Equal f1 f2
        then BitVec.ofNat width 1 else BitVec.ofNat width 0)) s)) := by
  simp [instFpRegister, h1, h2]

example {width : Nat} [NeZero width] {C F : Type}
    (r d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f1 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = none) :
    instFpRegister (.fp (.fpLess r d1 d2)) s = some none := by
  simp [instFpRegister, h1, h2]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h2 : getFpVar d2 s = some f1) (h3 : getFpVar d3 s = some f2) :
    instFpRegister (.fp (.fpAdd d1 d2 d3)) s =
      some (some (setFpVar d1 (holFp64Add .roundTiesToEven f1 f2) s)) := by
  simp [instFpRegister, h2, h3]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h2 : getFpVar d2 s = some f1) (h3 : getFpVar d3 s = some f2) :
    instFpRegister (.fp (.fpSub d1 d2 d3)) s =
      some (some (setFpVar d1 (holFp64Sub .roundTiesToEven f1 f2) s)) := by
  simp [instFpRegister, h2, h3]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h2 : getFpVar d2 s = some f1) (h3 : getFpVar d3 s = some f2) :
    instFpRegister (.fp (.fpMul d1 d2 d3)) s =
      some (some (setFpVar d1 (holFp64Mul .roundTiesToEven f1 f2) s)) := by
  simp [instFpRegister, h2, h3]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F) (f1 f2 : BitVec 64)
    (h2 : getFpVar d2 s = some f1) (h3 : getFpVar d3 s = some f2) :
    instFpRegister (.fp (.fpDiv d1 d2 d3)) s =
      some (some (setFpVar d1 (holFp64Div .roundTiesToEven f1 f2) s)) := by
  simp [instFpRegister, h2, h3]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F) (f1 : BitVec 64)
    (h2 : getFpVar d2 s = some f1) (h3 : getFpVar d3 s = none) :
    instFpRegister (.fp (.fpAdd d1 d2 d3)) s = some none := by
  simp [instFpRegister, h2, h3]

-- `fpSem$fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`, so the
-- first read (the destination/addend) is permuted to the last argument.
example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F)
    (f1 f2 f3 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = some f2)
    (h3 : getFpVar d3 s = some f3) :
    instFpRegister (.fp (.fpFma d1 d2 d3)) s =
      some (some (setFpVar d1 (holFp64MulAdd .roundTiesToEven f2 f3 f1) s)) := by
  simp [instFpRegister, h1, h2, h3]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 d3 : Nat) (s : StackSemStateFiniteExact width C F)
    (f1 f2 : BitVec 64)
    (h1 : getFpVar d1 s = some f1) (h2 : getFpVar d2 s = some f2)
    (h3 : getFpVar d3 s = none) :
    instFpRegister (.fp (.fpFma d1 d2 d3)) s = some none := by
  simp [instFpRegister, h1, h2, h3]

-- Closed binary64 comparison results, kernel-checked via `decide +kernel`.
private theorem holFp64LessThan_one_two : holFp64LessThan one two = true := by
  decide +kernel
private theorem holFp64LessThan_one_one : holFp64LessThan one one = false := by
  decide +kernel
private theorem holFp64LessThan_two_one : holFp64LessThan two one = false := by
  decide +kernel
private theorem holFp64LessEqual_one_one : holFp64LessEqual one one = true := by
  decide +kernel
private theorem holFp64LessEqual_two_one : holFp64LessEqual two one = false := by
  decide +kernel
private theorem holFp64Equal_one_one : holFp64Equal one one = true := by
  decide +kernel
private theorem holFp64Equal_one_two : holFp64Equal one two = false := by
  decide +kernel

-- Concrete replay of the comparison rows. The case is rewritten away with the
-- structural shape, the closed comparison result selects the branch, and the
-- finite-map update is evaluated. Probe rows
-- fpless_true/fpless_false/fpless_equal/fpless_missing/fplessequal_true/
-- fplessequal_false/fpequal_true/fpequal_false.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLess 4 1 2)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 1),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpLess 4 1 2)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64LessThan one two
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64LessThan_one_two]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLess 4 1 1)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 0),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpLess 4 1 1)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64LessThan one one
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64LessThan_one_one]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLess 4 2 1)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 0),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpLess 4 2 1)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64LessThan two one
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64LessThan_two_one]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLessEqual 4 1 1)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 1),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpLessEqual 4 1 1)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64LessEqual one one
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64LessEqual_one_one]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLessEqual 4 2 1)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 0),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpLessEqual 4 2 1)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64LessEqual two one
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64LessEqual_two_one]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpEqual 4 1 1)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 1),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpEqual 4 1 1)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64Equal one one
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Equal_one_one]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpEqual 4 1 2)) (arithFixture s)) =
      some (6,some 4621819117588971520,some (.inl 0),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpEqual 4 1 2)) (arithFixture s) =
      some (some (setVar 4 (.word (if holFp64Equal one two
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Equal_one_two]
  simp
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpLess 4 1 9)) (arithFixture s)) = none := by
  have h : instFpRegister (.fp (.fpLess 4 1 9)) (arithFixture s) = some none := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h]
  rfl

-- `holFp64MulAdd` has no ready `.2`-projection bridge in
-- `BinaryIeeeArithFp64`; derive the same computable-rounding equality used for
-- the other arithmetic rows.
private theorem holFp64MulAdd_rte (a b c : BitVec 64) :
    holFp64MulAdd .roundTiesToEven a b c =
      holFloatToFp64 (holFloatMulAddRte64 (holFp64ToFloat a) (holFp64ToFloat b)
        (holFp64ToFloat c)) := by
  unfold holFp64MulAdd
  rw [holFloatMulAdd_rte64]

-- Closed binary64 results, each kernel-checked through the computable bridge.
-- The wrong-order FMA value is recorded to show the row distinguishes the
-- `fpfma` permutation: correct `mul_add 2 3 10 = 16.0` versus the
-- wrongly-ordered `mul_add 10 2 3 = 23.0`.
private theorem holFp64Add_one_two :
    holFp64Add .roundTiesToEven one two = three := by
  rw [holFp64Add_rte]; decide +kernel
private theorem holFp64Sub_three_one :
    holFp64Sub .roundTiesToEven three one = two := by
  rw [holFp64Sub_rte]; decide +kernel
private theorem holFp64Mul_two_three :
    holFp64Mul .roundTiesToEven two three = six := by
  rw [holFp64Mul_rte]; decide +kernel
private theorem holFp64Div_six_two :
    holFp64Div .roundTiesToEven six two = three := by
  rw [holFp64Div_rte]; decide +kernel
private theorem holFp64MulAddOrdered :
    holFp64MulAdd .roundTiesToEven two three ten = 0x4030000000000000 := by
  rw [holFp64MulAdd_rte]; decide +kernel
private theorem holFp64MulAddWrongOrder :
    holFp64MulAdd .roundTiesToEven ten two three = 0x4037000000000000 := by
  rw [holFp64MulAdd_rte]; decide +kernel

-- Concrete replay of the arithmetic rows. Each rewrites the exact returned
-- expression through the closed result lemma and evaluates the finite-map
-- update; the probe rows are fpadd_result/fpadd_missing/fpsub_result/
-- fpmul_result/fpdiv_result (fpfma_order below).
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpAdd 7 1 2)) (arithFixture s)) =
      some (6,some 4613937818241073152,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpAdd 7 1 2)) (arithFixture s) =
      some (some (setFpVar 7 (holFp64Add .roundTiesToEven one two) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, setFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Add_one_two]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpAdd 7 1 9)) (arithFixture s)) = none := by
  have h : instFpRegister (.fp (.fpAdd 7 1 9)) (arithFixture s) = some none := by
    simp [instFpRegister, getFpVar, arithFixture, FUPDATE_HOL]
  rw [h]
  rfl
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpSub 7 3 1)) (arithFixture s)) =
      some (6,some 4611686018427387904,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpSub 7 3 1)) (arithFixture s) =
      some (some (setFpVar 7 (holFp64Sub .roundTiesToEven three one) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, setFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Sub_three_one]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpMul 7 2 3)) (arithFixture s)) =
      some (6,some 4618441417868443648,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpMul 7 2 3)) (arithFixture s) =
      some (some (setFpVar 7 (holFp64Mul .roundTiesToEven two three) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, setFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Mul_two_three]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpDiv 7 4 2)) (arithFixture s)) =
      some (6,some 4613937818241073152,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpDiv 7 4 2)) (arithFixture s) =
      some (some (setFpVar 7 (holFp64Div .roundTiesToEven six two) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, setFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64Div_six_two]
  cbv
-- Probe row fpfma_order. The addend is fp7 = 10.0, f2 = fp2 = 2.0 and
-- f3 = fp3 = 3.0, so the correct `mul_add 2 3 10 = 16.0` is observed; the
-- wrongly-ordered `mul_add 10 2 3 = 23.0` is `some 4627167142146473984`.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpFma 7 2 3)) (arithFixture s)) =
      some (6,some 4625196817309499392,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpFma 7 2 3)) (arithFixture s) =
      some (some (setFpVar 7 (holFp64MulAdd .roundTiesToEven two three ten) (arithFixture s))) := by
    simp [instFpRegister, getFpVar, setFpVar, arithFixture, FUPDATE_HOL]
  rw [h, holFp64MulAddOrdered]
  cbv

-- FP real-conversion fixture: clock 6, general registers as in `arithFixture`,
-- and two chosen FP values. The rows read fp7 and may read fp2; the 32-bit
-- FPToInt/FPFromInt rows read fp7 (d1 DIV 2 = 7 or d2 DIV 2 = 7).
private def convFixture {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (f2 f7 : BitVec 64) :=
  { s with
    clock := 6
    regs := (((((HolFiniteMapExact.empty : HolFiniteMapExact Nat (WordLocW width)).updateEq (1, .word 10)).updateEq
      (2, .word 20)).updateEq (3, .loc 1 2)).updateEq (4, .word 77)).updateEq (5, .loc 4 5)
    fpRegs := ((HolFiniteMapExact.empty : HolFiniteMapExact Nat (BitVec 64)).updateEq (2, f2)).updateEq
      (7, f7) }

-- Structural kernel checks of the exact returned expression for each new case,
-- given the FP lookups. HOL stackSemScript.sml:559-562, :605-624, :625-640.
example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f : BitVec 64)
    (h : getFpVar d2 s = some f) :
    instFpRegister (.fp (.fpSqrt d1 d2)) s =
      some (some (setFpVar d1 (holFp64Sqrt .roundTiesToEven f) s)) := by
  simp [instFpRegister, h]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F)
    (h : getFpVar d2 s = none) :
    instFpRegister (.fp (.fpSqrt d1 d2)) s = some none := by
  simp [instFpRegister, h]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F)
    (h : getFpVar d2 s = none) :
    instFpRegister (.fp (.fpToInt d1 d2)) s = some none := by
  simp [instFpRegister, h]

example {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) (f : BitVec 64)
    (h : getFpVar d2 s = some f) (hi : holFp64ToInt .roundTiesToEven f = none) :
    instFpRegister (.fp (.fpToInt d1 d2)) s = some none := by
  simp [instFpRegister, h, hi]

example {C F : Type} (d1 d2 : Nat) (s : StackSemStateFiniteExact 64 C F)
    (f : BitVec 64) (i : Int) (h : getFpVar d2 s = some f)
    (hi : holFp64ToInt .roundTiesToEven f = some i)
    (hw : (BitVec.ofInt 32 i).toInt = i) :
    instFpRegister (.fp (.fpToInt d1 d2)) s =
      some (some (setFpVar d1 ((BitVec.ofInt 32 i).setWidth 64) s)) := by
  simp only [instFpRegister, h]
  rw [hi]
  simp [hw]

example {C F : Type} (d1 d2 : Nat) (s : StackSemStateFiniteExact 64 C F)
    (f : BitVec 64) (h : getFpVar d2 s = some f) :
    instFpRegister (.fp (.fpFromInt d1 d2)) s =
      some (some (setFpVar d1 (holIntToFp64 .roundTiesToEven
        (holWordExtract 31 0 f 32).toInt) s)) := by
  simp [instFpRegister, h]

example {C F : Type} (d1 d2 : Nat) (s : StackSemStateFiniteExact 64 C F)
    (h : getFpVar d2 s = none) :
    instFpRegister (.fp (.fpFromInt d1 d2)) s = some none := by
  simp [instFpRegister, h]

example {width : Nat} [NeZero width] {C F : Type} (d1 d2 : Nat)
    (s : StackSemStateFiniteExact width C F) (hw : width ≠ 64) (v : BitVec 64)
    (h : getFpVar (d2 / 2) s = some v) :
    instFpRegister (.fp (.fpFromInt d1 d2)) s =
      some (some (setFpVar d1 (holIntToFp64 .roundTiesToEven
        (if d2 % 2 = 1 then holWordExtract 63 32 v width
          else holWordExtract 31 0 v width).toInt) s)) := by
  simp [instFpRegister, hw, h]

-- Closed binary64 conversion values, kernel-checked through the computable
-- roundTiesToEven bridges where the source definition is choice-based.
private theorem holFp64Sqrt_four :
    holFp64Sqrt .roundTiesToEven 0x4010000000000000 = 0x4000000000000000 := by
  rw [holFp64Sqrt_rte]; decide +kernel
private theorem holFp64ToInt_two :
    holFp64ToInt .roundTiesToEven (BitVec.ofNat 64 0x4000000000000000) = some (2 : Int) := by
  decide +kernel
private theorem holFp64ToInt_big :
    holFp64ToInt .roundTiesToEven (BitVec.ofNat 64 0x4330000000000000) =
      some (4503599627370496 : Int) := by
  decide +kernel
private theorem holIntToFp64_three :
    holIntToFp64 .roundTiesToEven (3 : Int) = 0x4008000000000000 := by
  rw [holIntToFp64_rte]; decide +kernel
private theorem holIntToFp64_four :
    holIntToFp64 .roundTiesToEven (4 : Int) = 0x4010000000000000 := by
  rw [holIntToFp64_rte]; decide +kernel
private theorem low32_int3 :
    (holWordExtract 31 0 (BitVec.ofNat 64 0x0000000000000003) 32).toInt = 3 := by
  decide +kernel
private theorem low32_halves :
    (holWordExtract 31 0 (BitVec.ofNat 64 0x0000000300000004) 32).toInt = 4 := by
  decide +kernel
private theorem high32_halves :
    (holWordExtract 63 32 (BitVec.ofNat 64 0x0000000300000004) 32).toInt = 3 := by
  decide +kernel

-- Concrete replay of the FPSqrt/FPToInt/FPFromInt rows. Probe rows
-- fpsqrt_result/fpsqrt_missing/fptoint_result/fptoint_out_of_range/
-- fptoint_missing/fptoint32_even/fptoint32_odd/fpfromint_result/
-- fpfromint_missing/fpfromint32_even/fpfromint32_odd. Each row fixes the
-- exact returned expression, rewrites the closed conversion value, and
-- evaluates the finite-map update.
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpSqrt 7 2))
      (convFixture s 0x4010000000000000 0x4024000000000000)) =
      some (6,some 4611686018427387904,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpSqrt 7 2))
      (convFixture s 0x4010000000000000 0x4024000000000000) =
      some (some (setFpVar 7 (holFp64Sqrt .roundTiesToEven 0x4010000000000000)
        (convFixture s 0x4010000000000000 0x4024000000000000))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h, holFp64Sqrt_four]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpSqrt 7 9))
      (convFixture s 0x4010000000000000 0x4024000000000000)) = none := by
  have h : instFpRegister (.fp (.fpSqrt 7 9))
      (convFixture s 0x4010000000000000 0x4024000000000000) = some none := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h]; rfl
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpToInt 7 2))
      (convFixture s 0x4000000000000000 0x4024000000000000)) =
      some (6,some 2,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpToInt 7 2))
      (convFixture s 0x4000000000000000 0x4024000000000000) =
      some (some (setFpVar 7 ((BitVec.ofInt 32 2).setWidth 64)
        (convFixture s 0x4000000000000000 0x4024000000000000))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
    rw [holFp64ToInt_two]
    simp
  rw [h]; cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpToInt 7 2))
      (convFixture s 0x4330000000000000 0x4024000000000000)) = none := by
  have h : instFpRegister (.fp (.fpToInt 7 2))
      (convFixture s 0x4330000000000000 0x4024000000000000) = some none := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
    rw [holFp64ToInt_big]
    simp
  rw [h]; rfl
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpToInt 7 9))
      (convFixture s 0x4000000000000000 0x4024000000000000)) = none := by
  have h : instFpRegister (.fp (.fpToInt 7 9))
      (convFixture s 0x4000000000000000 0x4024000000000000) = some none := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h]; rfl
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpToInt 14 2))
      (convFixture s 0x4000000000000000 0x4024000000000000)) =
      some (6,some 4621819117588971522,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpToInt 14 2))
      (convFixture s 0x4000000000000000 0x4024000000000000) =
      some (some (setFpVar 7 (holBitFieldInsert 31 0 (BitVec.ofInt 32 2)
        (BitVec.ofNat 64 0x4024000000000000))
        (convFixture s 0x4000000000000000 0x4024000000000000))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
    rw [holFp64ToInt_two]
    simp
  rw [h]; cbv
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpToInt 15 2))
      (convFixture s 0x4000000000000000 0x4024000000000000)) =
      some (6,some 8589934592,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpToInt 15 2))
      (convFixture s 0x4000000000000000 0x4024000000000000) =
      some (some (setFpVar 7 (holBitFieldInsert 63 32 (BitVec.ofInt 32 2)
        (BitVec.ofNat 64 0x4024000000000000))
        (convFixture s 0x4000000000000000 0x4024000000000000))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
    rw [holFp64ToInt_two]
    simp
  rw [h]; cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpFromInt 7 2))
      (convFixture s 0x0000000000000003 0x4024000000000000)) =
      some (6,some 4613937818241073152,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpFromInt 7 2))
      (convFixture s 0x0000000000000003 0x4024000000000000) =
      some (some (setFpVar 7 (holIntToFp64 .roundTiesToEven
        (holWordExtract 31 0 (BitVec.ofNat 64 0x0000000000000003) 32).toInt)
        (convFixture s 0x0000000000000003 0x4024000000000000))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h, low32_int3, holIntToFp64_three]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 64 C F) :
    observe (instFpRegister (.fp (.fpFromInt 7 9))
      (convFixture s 0x0000000000000003 0x4024000000000000)) = none := by
  have h : instFpRegister (.fp (.fpFromInt 7 9))
      (convFixture s 0x0000000000000003 0x4024000000000000) = some none := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h]; rfl
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpFromInt 7 14))
      (convFixture s 0x4000000000000000 0x0000000300000004)) =
      some (6,some 4616189618054758400,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpFromInt 7 14))
      (convFixture s 0x4000000000000000 0x0000000300000004) =
      some (some (setFpVar 7 (holIntToFp64 .roundTiesToEven
        (holWordExtract 31 0 (BitVec.ofNat 64 0x0000000300000004) 32).toInt)
        (convFixture s 0x4000000000000000 0x0000000300000004))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h, low32_halves, holIntToFp64_four]
  cbv
example {C F : Type} (s : StackSemStateFiniteExact 32 C F) :
    observe (instFpRegister (.fp (.fpFromInt 7 15))
      (convFixture s 0x4000000000000000 0x0000000300000004)) =
      some (6,some 4613937818241073152,some (.inl 77),some (.inr (4,5))) := by
  have h : instFpRegister (.fp (.fpFromInt 7 15))
      (convFixture s 0x4000000000000000 0x0000000300000004) =
      some (some (setFpVar 7 (holIntToFp64 .roundTiesToEven
        (holWordExtract 63 32 (BitVec.ofNat 64 0x0000000300000004) 32).toInt)
        (convFixture s 0x4000000000000000 0x0000000300000004))) := by
    simp [instFpRegister, getFpVar, convFixture, FUPDATE_HOL]
  rw [h, high32_halves, holIntToFp64_three]
  cbv

end Flapjack.Test.StackSemFpRegisterInstParity
