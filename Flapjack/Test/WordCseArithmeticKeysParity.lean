import Flapjack.Compiler.Backend.WordCse.Proofs.ArithmeticKeys
namespace Flapjack.Test.WordCseArithmeticKeysParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordCse WordSemStateFiniteExact
-- ak_0_1
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.reg 5):HolArith 1) = true ∧ arithReads (.binop .add 98 3 (.reg 5):HolArith 1) = arithReads (.binop .add 99 3 (.reg 5):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.reg 5):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.reg 5):HolArith 1)) w s) :=
  arithKeysEq (.binop .add 99 3 (.reg 5):HolArith 1) (.binop .add 98 3 (.reg 5):HolArith 1) ⟨rfl, rfl⟩

-- ak_1_1
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.binop .add 98 3 (.imm 255):HolArith 1) = arithReads (.binop .add 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.binop .add 99 3 (.imm 255):HolArith 1) (.binop .add 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_2_1
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.reg 5):HolArith 1) = true ∧ arithReads (.binop .sub 98 3 (.reg 5):HolArith 1) = arithReads (.binop .sub 99 3 (.reg 5):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.reg 5):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.reg 5):HolArith 1)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.reg 5):HolArith 1) (.binop .sub 98 3 (.reg 5):HolArith 1) ⟨rfl, rfl⟩

-- ak_3_1
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.binop .sub 98 3 (.imm 255):HolArith 1) = arithReads (.binop .sub 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.imm 255):HolArith 1) (.binop .sub 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_4_1
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.reg 5):HolArith 1) = true ∧ arithReads (.binop .and 98 3 (.reg 5):HolArith 1) = arithReads (.binop .and 99 3 (.reg 5):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.reg 5):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.reg 5):HolArith 1)) w s) :=
  arithKeysEq (.binop .and 99 3 (.reg 5):HolArith 1) (.binop .and 98 3 (.reg 5):HolArith 1) ⟨rfl, rfl⟩

-- ak_5_1
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.binop .and 98 3 (.imm 255):HolArith 1) = arithReads (.binop .and 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.binop .and 99 3 (.imm 255):HolArith 1) (.binop .and 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_6_1
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.reg 5):HolArith 1) = true ∧ arithReads (.binop .or 98 3 (.reg 5):HolArith 1) = arithReads (.binop .or 99 3 (.reg 5):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.reg 5):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.reg 5):HolArith 1)) w s) :=
  arithKeysEq (.binop .or 99 3 (.reg 5):HolArith 1) (.binop .or 98 3 (.reg 5):HolArith 1) ⟨rfl, rfl⟩

-- ak_7_1
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.binop .or 98 3 (.imm 255):HolArith 1) = arithReads (.binop .or 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.binop .or 99 3 (.imm 255):HolArith 1) (.binop .or 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_8_1
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.reg 5):HolArith 1) = true ∧ arithReads (.binop .xor 98 3 (.reg 5):HolArith 1) = arithReads (.binop .xor 99 3 (.reg 5):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.reg 5):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.reg 5):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.reg 5):HolArith 1)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.reg 5):HolArith 1) (.binop .xor 98 3 (.reg 5):HolArith 1) ⟨rfl, rfl⟩

-- ak_9_1
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.binop .xor 98 3 (.imm 255):HolArith 1) = arithReads (.binop .xor 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.imm 255):HolArith 1) (.binop .xor 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_10_1
example {C : Type} {F : Type} :
  canMemArith (.shift .lsl 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.shift .lsl 98 3 (.imm 255):HolArith 1) = arithReads (.shift .lsl 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.shift .lsl 99 3 (.imm 255):HolArith 1) (.shift .lsl 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_11_1
example {C : Type} {F : Type} :
  canMemArith (.shift .lsr 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.shift .lsr 98 3 (.imm 255):HolArith 1) = arithReads (.shift .lsr 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.shift .lsr 99 3 (.imm 255):HolArith 1) (.shift .lsr 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_12_1
example {C : Type} {F : Type} :
  canMemArith (.shift .asr 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.shift .asr 98 3 (.imm 255):HolArith 1) = arithReads (.shift .asr 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.shift .asr 99 3 (.imm 255):HolArith 1) (.shift .asr 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_13_1
example {C : Type} {F : Type} :
  canMemArith (.shift .ror 98 3 (.imm 255):HolArith 1) = true ∧ arithReads (.shift .ror 98 3 (.imm 255):HolArith 1) = arithReads (.shift .ror 99 3 (.imm 255):HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 99 3 (.imm 255):HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 98 3 (.imm 255):HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 98 3 (.imm 255):HolArith 1)) w s) :=
  arithKeysEq (.shift .ror 99 3 (.imm 255):HolArith 1) (.shift .ror 98 3 (.imm 255):HolArith 1) ⟨rfl, rfl⟩

-- ak_14_1
example {C : Type} {F : Type} :
  canMemArith (.div 98 3 5:HolArith 1) = true ∧ arithReads (.div 98 3 5:HolArith 1) = arithReads (.div 99 3 5:HolArith 1) ∧
  ∀ (s : WordSemStateFiniteExact 1 C F) (w : WordLocW 1),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.div 99 3 5:HolArith 1)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 98 3 5:HolArith 1)))) s =
      (none, setVar (firstRegOfArith (.div 98 3 5:HolArith 1)) w s) :=
  arithKeysEq (.div 99 3 5:HolArith 1) (.div 98 3 5:HolArith 1) ⟨rfl, rfl⟩

-- ak_0_32
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.reg 5):HolArith 32) = true ∧ arithReads (.binop .add 98 3 (.reg 5):HolArith 32) = arithReads (.binop .add 99 3 (.reg 5):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.reg 5):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.reg 5):HolArith 32)) w s) :=
  arithKeysEq (.binop .add 99 3 (.reg 5):HolArith 32) (.binop .add 98 3 (.reg 5):HolArith 32) ⟨rfl, rfl⟩

-- ak_1_32
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.binop .add 98 3 (.imm 255):HolArith 32) = arithReads (.binop .add 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.binop .add 99 3 (.imm 255):HolArith 32) (.binop .add 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_2_32
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.reg 5):HolArith 32) = true ∧ arithReads (.binop .sub 98 3 (.reg 5):HolArith 32) = arithReads (.binop .sub 99 3 (.reg 5):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.reg 5):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.reg 5):HolArith 32)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.reg 5):HolArith 32) (.binop .sub 98 3 (.reg 5):HolArith 32) ⟨rfl, rfl⟩

-- ak_3_32
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.binop .sub 98 3 (.imm 255):HolArith 32) = arithReads (.binop .sub 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.imm 255):HolArith 32) (.binop .sub 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_4_32
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.reg 5):HolArith 32) = true ∧ arithReads (.binop .and 98 3 (.reg 5):HolArith 32) = arithReads (.binop .and 99 3 (.reg 5):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.reg 5):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.reg 5):HolArith 32)) w s) :=
  arithKeysEq (.binop .and 99 3 (.reg 5):HolArith 32) (.binop .and 98 3 (.reg 5):HolArith 32) ⟨rfl, rfl⟩

-- ak_5_32
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.binop .and 98 3 (.imm 255):HolArith 32) = arithReads (.binop .and 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.binop .and 99 3 (.imm 255):HolArith 32) (.binop .and 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_6_32
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.reg 5):HolArith 32) = true ∧ arithReads (.binop .or 98 3 (.reg 5):HolArith 32) = arithReads (.binop .or 99 3 (.reg 5):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.reg 5):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.reg 5):HolArith 32)) w s) :=
  arithKeysEq (.binop .or 99 3 (.reg 5):HolArith 32) (.binop .or 98 3 (.reg 5):HolArith 32) ⟨rfl, rfl⟩

-- ak_7_32
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.binop .or 98 3 (.imm 255):HolArith 32) = arithReads (.binop .or 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.binop .or 99 3 (.imm 255):HolArith 32) (.binop .or 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_8_32
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.reg 5):HolArith 32) = true ∧ arithReads (.binop .xor 98 3 (.reg 5):HolArith 32) = arithReads (.binop .xor 99 3 (.reg 5):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.reg 5):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.reg 5):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.reg 5):HolArith 32)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.reg 5):HolArith 32) (.binop .xor 98 3 (.reg 5):HolArith 32) ⟨rfl, rfl⟩

-- ak_9_32
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.binop .xor 98 3 (.imm 255):HolArith 32) = arithReads (.binop .xor 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.imm 255):HolArith 32) (.binop .xor 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_10_32
example {C : Type} {F : Type} :
  canMemArith (.shift .lsl 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.shift .lsl 98 3 (.imm 255):HolArith 32) = arithReads (.shift .lsl 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.shift .lsl 99 3 (.imm 255):HolArith 32) (.shift .lsl 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_11_32
example {C : Type} {F : Type} :
  canMemArith (.shift .lsr 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.shift .lsr 98 3 (.imm 255):HolArith 32) = arithReads (.shift .lsr 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.shift .lsr 99 3 (.imm 255):HolArith 32) (.shift .lsr 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_12_32
example {C : Type} {F : Type} :
  canMemArith (.shift .asr 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.shift .asr 98 3 (.imm 255):HolArith 32) = arithReads (.shift .asr 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.shift .asr 99 3 (.imm 255):HolArith 32) (.shift .asr 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_13_32
example {C : Type} {F : Type} :
  canMemArith (.shift .ror 98 3 (.imm 255):HolArith 32) = true ∧ arithReads (.shift .ror 98 3 (.imm 255):HolArith 32) = arithReads (.shift .ror 99 3 (.imm 255):HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 99 3 (.imm 255):HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 98 3 (.imm 255):HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 98 3 (.imm 255):HolArith 32)) w s) :=
  arithKeysEq (.shift .ror 99 3 (.imm 255):HolArith 32) (.shift .ror 98 3 (.imm 255):HolArith 32) ⟨rfl, rfl⟩

-- ak_14_32
example {C : Type} {F : Type} :
  canMemArith (.div 98 3 5:HolArith 32) = true ∧ arithReads (.div 98 3 5:HolArith 32) = arithReads (.div 99 3 5:HolArith 32) ∧
  ∀ (s : WordSemStateFiniteExact 32 C F) (w : WordLocW 32),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.div 99 3 5:HolArith 32)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 98 3 5:HolArith 32)))) s =
      (none, setVar (firstRegOfArith (.div 98 3 5:HolArith 32)) w s) :=
  arithKeysEq (.div 99 3 5:HolArith 32) (.div 98 3 5:HolArith 32) ⟨rfl, rfl⟩

-- ak_0_64
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.reg 5):HolArith 64) = true ∧ arithReads (.binop .add 98 3 (.reg 5):HolArith 64) = arithReads (.binop .add 99 3 (.reg 5):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.reg 5):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.reg 5):HolArith 64)) w s) :=
  arithKeysEq (.binop .add 99 3 (.reg 5):HolArith 64) (.binop .add 98 3 (.reg 5):HolArith 64) ⟨rfl, rfl⟩

-- ak_1_64
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.binop .add 98 3 (.imm 255):HolArith 64) = arithReads (.binop .add 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.binop .add 99 3 (.imm 255):HolArith 64) (.binop .add 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_2_64
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.reg 5):HolArith 64) = true ∧ arithReads (.binop .sub 98 3 (.reg 5):HolArith 64) = arithReads (.binop .sub 99 3 (.reg 5):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.reg 5):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.reg 5):HolArith 64)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.reg 5):HolArith 64) (.binop .sub 98 3 (.reg 5):HolArith 64) ⟨rfl, rfl⟩

-- ak_3_64
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.binop .sub 98 3 (.imm 255):HolArith 64) = arithReads (.binop .sub 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.imm 255):HolArith 64) (.binop .sub 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_4_64
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.reg 5):HolArith 64) = true ∧ arithReads (.binop .and 98 3 (.reg 5):HolArith 64) = arithReads (.binop .and 99 3 (.reg 5):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.reg 5):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.reg 5):HolArith 64)) w s) :=
  arithKeysEq (.binop .and 99 3 (.reg 5):HolArith 64) (.binop .and 98 3 (.reg 5):HolArith 64) ⟨rfl, rfl⟩

-- ak_5_64
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.binop .and 98 3 (.imm 255):HolArith 64) = arithReads (.binop .and 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.binop .and 99 3 (.imm 255):HolArith 64) (.binop .and 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_6_64
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.reg 5):HolArith 64) = true ∧ arithReads (.binop .or 98 3 (.reg 5):HolArith 64) = arithReads (.binop .or 99 3 (.reg 5):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.reg 5):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.reg 5):HolArith 64)) w s) :=
  arithKeysEq (.binop .or 99 3 (.reg 5):HolArith 64) (.binop .or 98 3 (.reg 5):HolArith 64) ⟨rfl, rfl⟩

-- ak_7_64
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.binop .or 98 3 (.imm 255):HolArith 64) = arithReads (.binop .or 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.binop .or 99 3 (.imm 255):HolArith 64) (.binop .or 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_8_64
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.reg 5):HolArith 64) = true ∧ arithReads (.binop .xor 98 3 (.reg 5):HolArith 64) = arithReads (.binop .xor 99 3 (.reg 5):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.reg 5):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.reg 5):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.reg 5):HolArith 64)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.reg 5):HolArith 64) (.binop .xor 98 3 (.reg 5):HolArith 64) ⟨rfl, rfl⟩

-- ak_9_64
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.binop .xor 98 3 (.imm 255):HolArith 64) = arithReads (.binop .xor 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.imm 255):HolArith 64) (.binop .xor 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_10_64
example {C : Type} {F : Type} :
  canMemArith (.shift .lsl 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.shift .lsl 98 3 (.imm 255):HolArith 64) = arithReads (.shift .lsl 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.shift .lsl 99 3 (.imm 255):HolArith 64) (.shift .lsl 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_11_64
example {C : Type} {F : Type} :
  canMemArith (.shift .lsr 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.shift .lsr 98 3 (.imm 255):HolArith 64) = arithReads (.shift .lsr 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.shift .lsr 99 3 (.imm 255):HolArith 64) (.shift .lsr 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_12_64
example {C : Type} {F : Type} :
  canMemArith (.shift .asr 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.shift .asr 98 3 (.imm 255):HolArith 64) = arithReads (.shift .asr 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.shift .asr 99 3 (.imm 255):HolArith 64) (.shift .asr 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_13_64
example {C : Type} {F : Type} :
  canMemArith (.shift .ror 98 3 (.imm 255):HolArith 64) = true ∧ arithReads (.shift .ror 98 3 (.imm 255):HolArith 64) = arithReads (.shift .ror 99 3 (.imm 255):HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 99 3 (.imm 255):HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 98 3 (.imm 255):HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 98 3 (.imm 255):HolArith 64)) w s) :=
  arithKeysEq (.shift .ror 99 3 (.imm 255):HolArith 64) (.shift .ror 98 3 (.imm 255):HolArith 64) ⟨rfl, rfl⟩

-- ak_14_64
example {C : Type} {F : Type} :
  canMemArith (.div 98 3 5:HolArith 64) = true ∧ arithReads (.div 98 3 5:HolArith 64) = arithReads (.div 99 3 5:HolArith 64) ∧
  ∀ (s : WordSemStateFiniteExact 64 C F) (w : WordLocW 64),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.div 99 3 5:HolArith 64)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 98 3 5:HolArith 64)))) s =
      (none, setVar (firstRegOfArith (.div 98 3 5:HolArith 64)) w s) :=
  arithKeysEq (.div 99 3 5:HolArith 64) (.div 98 3 5:HolArith 64) ⟨rfl, rfl⟩

-- ak_0_80
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.reg 5):HolArith 80) = true ∧ arithReads (.binop .add 98 3 (.reg 5):HolArith 80) = arithReads (.binop .add 99 3 (.reg 5):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.reg 5):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.reg 5):HolArith 80)) w s) :=
  arithKeysEq (.binop .add 99 3 (.reg 5):HolArith 80) (.binop .add 98 3 (.reg 5):HolArith 80) ⟨rfl, rfl⟩

-- ak_1_80
example {C : Type} {F : Type} :
  canMemArith (.binop .add 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.binop .add 98 3 (.imm 255):HolArith 80) = arithReads (.binop .add 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .add 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .add 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.binop .add 99 3 (.imm 255):HolArith 80) (.binop .add 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_2_80
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.reg 5):HolArith 80) = true ∧ arithReads (.binop .sub 98 3 (.reg 5):HolArith 80) = arithReads (.binop .sub 99 3 (.reg 5):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.reg 5):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.reg 5):HolArith 80)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.reg 5):HolArith 80) (.binop .sub 98 3 (.reg 5):HolArith 80) ⟨rfl, rfl⟩

-- ak_3_80
example {C : Type} {F : Type} :
  canMemArith (.binop .sub 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.binop .sub 98 3 (.imm 255):HolArith 80) = arithReads (.binop .sub 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .sub 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.binop .sub 99 3 (.imm 255):HolArith 80) (.binop .sub 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_4_80
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.reg 5):HolArith 80) = true ∧ arithReads (.binop .and 98 3 (.reg 5):HolArith 80) = arithReads (.binop .and 99 3 (.reg 5):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.reg 5):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.reg 5):HolArith 80)) w s) :=
  arithKeysEq (.binop .and 99 3 (.reg 5):HolArith 80) (.binop .and 98 3 (.reg 5):HolArith 80) ⟨rfl, rfl⟩

-- ak_5_80
example {C : Type} {F : Type} :
  canMemArith (.binop .and 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.binop .and 98 3 (.imm 255):HolArith 80) = arithReads (.binop .and 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .and 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .and 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.binop .and 99 3 (.imm 255):HolArith 80) (.binop .and 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_6_80
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.reg 5):HolArith 80) = true ∧ arithReads (.binop .or 98 3 (.reg 5):HolArith 80) = arithReads (.binop .or 99 3 (.reg 5):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.reg 5):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.reg 5):HolArith 80)) w s) :=
  arithKeysEq (.binop .or 99 3 (.reg 5):HolArith 80) (.binop .or 98 3 (.reg 5):HolArith 80) ⟨rfl, rfl⟩

-- ak_7_80
example {C : Type} {F : Type} :
  canMemArith (.binop .or 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.binop .or 98 3 (.imm 255):HolArith 80) = arithReads (.binop .or 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .or 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .or 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.binop .or 99 3 (.imm 255):HolArith 80) (.binop .or 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_8_80
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.reg 5):HolArith 80) = true ∧ arithReads (.binop .xor 98 3 (.reg 5):HolArith 80) = arithReads (.binop .xor 99 3 (.reg 5):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.reg 5):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.reg 5):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.reg 5):HolArith 80)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.reg 5):HolArith 80) (.binop .xor 98 3 (.reg 5):HolArith 80) ⟨rfl, rfl⟩

-- ak_9_80
example {C : Type} {F : Type} :
  canMemArith (.binop .xor 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.binop .xor 98 3 (.imm 255):HolArith 80) = arithReads (.binop .xor 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.binop .xor 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.binop .xor 99 3 (.imm 255):HolArith 80) (.binop .xor 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_10_80
example {C : Type} {F : Type} :
  canMemArith (.shift .lsl 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.shift .lsl 98 3 (.imm 255):HolArith 80) = arithReads (.shift .lsl 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .lsl 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.shift .lsl 99 3 (.imm 255):HolArith 80) (.shift .lsl 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_11_80
example {C : Type} {F : Type} :
  canMemArith (.shift .lsr 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.shift .lsr 98 3 (.imm 255):HolArith 80) = arithReads (.shift .lsr 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .lsr 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.shift .lsr 99 3 (.imm 255):HolArith 80) (.shift .lsr 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_12_80
example {C : Type} {F : Type} :
  canMemArith (.shift .asr 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.shift .asr 98 3 (.imm 255):HolArith 80) = arithReads (.shift .asr 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .asr 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.shift .asr 99 3 (.imm 255):HolArith 80) (.shift .asr 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_13_80
example {C : Type} {F : Type} :
  canMemArith (.shift .ror 98 3 (.imm 255):HolArith 80) = true ∧ arithReads (.shift .ror 98 3 (.imm 255):HolArith 80) = arithReads (.shift .ror 99 3 (.imm 255):HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 99 3 (.imm 255):HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 98 3 (.imm 255):HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.shift .ror 98 3 (.imm 255):HolArith 80)) w s) :=
  arithKeysEq (.shift .ror 99 3 (.imm 255):HolArith 80) (.shift .ror 98 3 (.imm 255):HolArith 80) ⟨rfl, rfl⟩

-- ak_14_80
example {C : Type} {F : Type} :
  canMemArith (.div 98 3 5:HolArith 80) = true ∧ arithReads (.div 98 3 5:HolArith 80) = arithReads (.div 99 3 5:HolArith 80) ∧
  ∀ (s : WordSemStateFiniteExact 80 C F) (w : WordLocW 80),
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.div 99 3 5:HolArith 80)) w s) →
    evaluate (.inst (.arith (HolArith.toWordLangArith (.div 98 3 5:HolArith 80)))) s =
      (none, setVar (firstRegOfArith (.div 98 3 5:HolArith 80)) w s) :=
  arithKeysEq (.div 99 3 5:HolArith 80) (.div 98 3 5:HolArith 80) ⟨rfl, rfl⟩

example {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a b : HolArith width) (h : canMemArith a = true ∧ arithToNumList a = arithToNumList b)
    (s : WordSemStateFiniteExact width C F) (w : WordLocW width)
    (heval : evaluate (.inst (.arith (HolArith.toWordLangArith a))) s =
      (none, setVar (firstRegOfArith a) w s)) :
    evaluate (.inst (.arith (HolArith.toWordLangArith b))) s =
      (none, setVar (firstRegOfArith b) w s) := (arithKeysEq a b h).2.2 s w heval
end Flapjack.Test.WordCseArithmeticKeysParity
