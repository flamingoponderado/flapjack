import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopInstructions

namespace Flapjack.Test.WordToStackNoShmemopInstructionsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

-- ci_skip
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.skip);
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_const
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.const 999 5);
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_binop_imm
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.binop .add 999 3 (.imm 9)));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_binop_reg
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.binop .xor 999 3 (.reg 5)));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_shift_imm
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.shift .lsl 999 3 (.imm 9)));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_shift_reg
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.shift .lsr 999 3 (.reg 5)));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_div
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.div 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_long_mul
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.longMul 999 7 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_long_div
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.longDiv 999 7 3 5 8));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_carry
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.addCarry 999 7 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_add_overflow
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.addOverflow 999 7 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_sub_overflow
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.arith (.subOverflow 999 7 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_load
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .load 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_load8
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .load8 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_load16
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .load16 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_load32
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .load32 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_store
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .store 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_store8
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .store8 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_store16
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .store16 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_store32
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.mem .store32 999 (.addr 3 9));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpless
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpLess 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fplessequal
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpLessEqual 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpequal
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpEqual 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpabs
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpAbs 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpneg
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpNeg 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpsqrt
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpSqrt 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpadd
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpAdd 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpsub
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpSub 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmul
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpMul 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpdiv
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpDiv 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpfma
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpFma 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmov
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpMov 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovtoreg
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpMovToReg 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovfromreg
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpMovFromReg 999 3 5));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fptoint
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpToInt 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpfromint
example (conf : AsmConfigExact 64) :
    let p : WordLangProgHOL (BitVec 64) := .inst (.fp (.fpFromInt 999 3));
    let bs : AppList (BitVec 64) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovtoreg1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .inst (.fp (.fpMovToReg 999 3 5));
    let bs : AppList (BitVec 1) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovfromreg1
example (conf : AsmConfigExact 1) :
    let p : WordLangProgHOL (BitVec 1) := .inst (.fp (.fpMovFromReg 999 3 5));
    let bs : AppList (BitVec 1) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovtoreg32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .inst (.fp (.fpMovToReg 999 3 5));
    let bs : AppList (BitVec 32) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovfromreg32
example (conf : AsmConfigExact 32) :
    let p : WordLangProgHOL (BitVec 32) := .inst (.fp (.fpMovFromReg 999 3 5));
    let bs : AppList (BitVec 32) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovtoreg80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .inst (.fp (.fpMovToReg 999 3 5));
    let bs : AppList (BitVec 80) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf false p bs (0,0,0)).1 = true ∧
      (compNative conf false p bs (0,0,0)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

-- ci_fpmovfromreg80
example (conf : AsmConfigExact 80) :
    let p : WordLangProgHOL (BitVec 80) := .inst (.fp (.fpMovFromReg 999 3 5));
    let bs : AppList (BitVec 80) × Nat := (.list [4, 7], 17);
    noShareInstSubprogsHOL p = true ∧
      noShmemop (compNative conf true p bs (2,7,9)).1 = true ∧
      (compNative conf true p bs (2,7,9)).2 = bs := by
  simp only [compNative]
  exact ⟨rfl, rfl, True.intro⟩

example {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (i : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.inst i) = true)
    (compiled : compNative conf perf (.inst i) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopInst conf perf i bs frame output residual guard compiled

end Flapjack.Test.WordToStackNoShmemopInstructionsParity
