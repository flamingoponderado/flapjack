import Flapjack.Compiler.Backend.WordCse.Proofs.DeletionFrames
open Flapjack Compiler.Encoders.Asm Compiler.Backend.WordCse WordSemStateFiniteExact

-- del_arith_0_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_1_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_1_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_2_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_2_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_3_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_3_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_4_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_4_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_5_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_5_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_6_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_6_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_7_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_7_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_8_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_8_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_9_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_9_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_10_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_10_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_11_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_11_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_12_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_12_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_13_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_13_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_14_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 1) 99 w s ⟨rfl, by decide⟩

-- del_arith_14_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 1) 77 w s ⟨rfl, by decide⟩

-- del_arith_0_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_0_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_1_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_1_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_2_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_2_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_3_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_3_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_4_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_4_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_5_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_5_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_6_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_6_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_7_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_7_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_8_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_8_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_9_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_9_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_10_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_10_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_11_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_11_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_12_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_12_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_13_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_13_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_14_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 32) 99 w s ⟨rfl, by decide⟩

-- del_arith_14_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 32) 77 w s ⟨rfl, by decide⟩

-- del_arith_0_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_0_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_1_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_1_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_2_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_2_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_3_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_3_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_4_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_4_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_5_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_5_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_6_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_6_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_7_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_7_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_8_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_8_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_9_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_9_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_10_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_10_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_11_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_11_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_12_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_12_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_13_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_13_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_14_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 64) 99 w s ⟨rfl, by decide⟩

-- del_arith_14_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 64) 77 w s ⟨rfl, by decide⟩

-- del_arith_0_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_0_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.reg 5):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_1_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_1_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .add 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_2_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_2_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.reg 5):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_3_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_3_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .sub 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_4_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_4_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.reg 5):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_5_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_5_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .and 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_6_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_6_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.reg 5):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_7_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_7_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .or 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_8_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_8_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.reg 5):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_9_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_9_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.binop .xor 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_10_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_10_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsl 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_11_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_11_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .lsr 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_12_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_12_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .asr 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_13_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_13_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.shift .ror 99 3 (.imm 255):HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_arith_14_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 80) 99 w s ⟨rfl, by decide⟩

-- del_arith_14_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithUnsetVar (.div 99 3 5:HolArith 80) 77 w s ⟨rfl, by decide⟩

-- del_load_load_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load8_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load8_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load16_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load16_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load32_99_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 1)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load32_77_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 1)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load8_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load8_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load16_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load16_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load32_99_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 32)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load32_77_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 32)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load8_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load8_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load16_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load16_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load32_99_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 64)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load32_77_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 64)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load8_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load8_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load8 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load8 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load16_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load16_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load16 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load16 99 3 255 77 w s ⟨rfl, by decide⟩

-- del_load_load32_99_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 80)))) (unsetVar 99 s) = (none, setVar 99 w (unsetVar 99 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 99 w s ⟨rfl, by decide⟩

-- del_load_load32_77_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 80)))) (unsetVar 77 s) = (none, setVar 99 w (unsetVar 77 s))) ↔
  evaluate (.inst (.mem .load32 99 (.addr 3 (255:BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadUnsetVar .load32 99 3 255 77 w s ⟨rfl, by decide⟩

