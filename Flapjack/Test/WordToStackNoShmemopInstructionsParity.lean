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


-- ci_fplessequal


-- ci_fpequal


-- ci_fpabs


-- ci_fpneg


-- ci_fpsqrt


-- ci_fpadd


-- ci_fpsub


-- ci_fpmul


-- ci_fpdiv


-- ci_fpfma


-- ci_fpmov


-- ci_fpmovtoreg


-- ci_fpmovfromreg


-- ci_fptoint


-- ci_fpfromint


-- ci_fpmovtoreg1


-- ci_fpmovfromreg1


-- ci_fpmovtoreg32


-- ci_fpmovfromreg32


-- ci_fpmovtoreg80


-- ci_fpmovfromreg80


example {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (i : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL (.inst i) = true)
    (compiled : compNative conf perf (.inst i) bs frame = (output, residual)) :
    noShmemop output = true :=
  compNoShmemopInst conf perf i bs frame output residual guard compiled

end Flapjack.Test.WordToStackNoShmemopInstructionsParity
