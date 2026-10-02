import Flapjack.Compiler.Backend.WordCse.Proofs.EvaluationFrames
namespace Flapjack.Test.WordCseEvaluationFramesParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordCse WordSemStateFiniteExact
-- fr_write_0_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_0_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_0_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.reg 5):HolArith 1) w s m rfl

-- fr_arith_agree_0_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.reg 5):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_1_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_1_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_1_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_1_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_2_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_2_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_2_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.reg 5):HolArith 1) w s m rfl

-- fr_arith_agree_2_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.reg 5):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_3_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_3_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_4_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_4_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_4_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.reg 5):HolArith 1) w s m rfl

-- fr_arith_agree_4_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.reg 5):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_5_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_5_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_5_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_5_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_6_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_6_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_6_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.reg 5):HolArith 1) w s m rfl

-- fr_arith_agree_6_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.reg 5):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_7_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_7_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_7_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_7_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_8_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_8_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_8_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.reg 5):HolArith 1) w s m rfl

-- fr_arith_agree_8_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.reg 5):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_9_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_9_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_9_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_9_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_10_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_10_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_10_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsl 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_10_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsl 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_11_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_11_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_11_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsr 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_11_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsr 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_12_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_12_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_12_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .asr 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_12_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .asr 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_13_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_13_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_13_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .ror 99 3 (.imm 255):HolArith 1) w s m rfl

-- fr_arith_agree_13_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .ror 99 3 (.imm 255):HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_14_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 1) 99 u w s ⟨rfl, by decide⟩

-- fr_write_14_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 1) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_14_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) (m : BitVec 1 → WordLocW 1) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.div 99 3 5:HolArith 1) w s m rfl

-- fr_arith_agree_14_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.div 99 3 5:HolArith 1) w s1 s2 ⟨he, rfl, hl⟩

-- fr_load_agree_load_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load 99 3 (-1 : BitVec 1) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load8_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load8 99 3 (-1 : BitVec 1) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load16_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load16 99 3 (-1 : BitVec 1) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load32_1
example {C : Type} {F : Type} (w : WordLocW 1) (s1 s2 : WordSemStateFiniteExact 1 C F)
  (he : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load32 99 3 (-1 : BitVec 1) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_write_0_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_0_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_0_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.reg 5):HolArith 32) w s m rfl

-- fr_arith_agree_0_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.reg 5):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_1_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_1_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_1_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_1_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_2_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_2_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_2_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.reg 5):HolArith 32) w s m rfl

-- fr_arith_agree_2_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.reg 5):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_3_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_3_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_4_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_4_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_4_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.reg 5):HolArith 32) w s m rfl

-- fr_arith_agree_4_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.reg 5):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_5_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_5_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_5_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_5_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_6_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_6_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_6_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.reg 5):HolArith 32) w s m rfl

-- fr_arith_agree_6_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.reg 5):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_7_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_7_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_7_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_7_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_8_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_8_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_8_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.reg 5):HolArith 32) w s m rfl

-- fr_arith_agree_8_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.reg 5):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_9_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_9_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_9_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_9_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_10_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_10_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_10_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsl 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_10_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsl 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_11_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_11_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_11_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsr 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_11_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsr 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_12_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_12_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_12_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .asr 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_12_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .asr 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_13_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_13_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_13_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .ror 99 3 (.imm 255):HolArith 32) w s m rfl

-- fr_arith_agree_13_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .ror 99 3 (.imm 255):HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_14_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 32) 99 u w s ⟨rfl, by decide⟩

-- fr_write_14_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 32) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_14_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) (m : BitVec 32 → WordLocW 32) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.div 99 3 5:HolArith 32) w s m rfl

-- fr_arith_agree_14_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.div 99 3 5:HolArith 32) w s1 s2 ⟨he, rfl, hl⟩

-- fr_load_agree_load_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load 99 3 (-1 : BitVec 32) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load8_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load8 99 3 (-1 : BitVec 32) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load16_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load16 99 3 (-1 : BitVec 32) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load32_32
example {C : Type} {F : Type} (w : WordLocW 32) (s1 s2 : WordSemStateFiniteExact 32 C F)
  (he : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load32 99 3 (-1 : BitVec 32) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_write_0_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_0_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_0_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.reg 5):HolArith 64) w s m rfl

-- fr_arith_agree_0_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.reg 5):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_1_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_1_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_1_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_1_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_2_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_2_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_2_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.reg 5):HolArith 64) w s m rfl

-- fr_arith_agree_2_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.reg 5):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_3_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_3_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_4_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_4_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_4_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.reg 5):HolArith 64) w s m rfl

-- fr_arith_agree_4_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.reg 5):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_5_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_5_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_5_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_5_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_6_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_6_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_6_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.reg 5):HolArith 64) w s m rfl

-- fr_arith_agree_6_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.reg 5):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_7_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_7_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_7_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_7_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_8_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_8_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_8_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.reg 5):HolArith 64) w s m rfl

-- fr_arith_agree_8_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.reg 5):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_9_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_9_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_9_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_9_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_10_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_10_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_10_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsl 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_10_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsl 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_11_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_11_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_11_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsr 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_11_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsr 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_12_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_12_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_12_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .asr 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_12_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .asr 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_13_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_13_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_13_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .ror 99 3 (.imm 255):HolArith 64) w s m rfl

-- fr_arith_agree_13_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .ror 99 3 (.imm 255):HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_14_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 64) 99 u w s ⟨rfl, by decide⟩

-- fr_write_14_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 64) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_14_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) (m : BitVec 64 → WordLocW 64) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.div 99 3 5:HolArith 64) w s m rfl

-- fr_arith_agree_14_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.div 99 3 5:HolArith 64) w s1 s2 ⟨he, rfl, hl⟩

-- fr_load_agree_load_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load 99 3 (-1 : BitVec 64) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load8_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load8 99 3 (-1 : BitVec 64) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load16_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load16 99 3 (-1 : BitVec 64) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load32_64
example {C : Type} {F : Type} (w : WordLocW 64) (s1 s2 : WordSemStateFiniteExact 64 C F)
  (he : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load32 99 3 (-1 : BitVec 64) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_write_0_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_0_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.reg 5):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_0_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.reg 5):HolArith 80) w s m rfl

-- fr_arith_agree_0_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.reg 5):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.reg 5):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_1_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_1_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .add 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_1_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .add 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_1_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .add 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .add 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_2_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_2_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.reg 5):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_2_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.reg 5):HolArith 80) w s m rfl

-- fr_arith_agree_2_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.reg 5):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.reg 5):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_3_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_3_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .sub 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .sub 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .sub 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .sub 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_4_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_4_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.reg 5):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_4_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.reg 5):HolArith 80) w s m rfl

-- fr_arith_agree_4_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.reg 5):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.reg 5):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_5_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_5_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .and 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_5_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .and 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_5_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .and 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .and 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_6_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_6_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.reg 5):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_6_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.reg 5):HolArith 80) w s m rfl

-- fr_arith_agree_6_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.reg 5):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.reg 5):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_7_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_7_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .or 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_7_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .or 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_7_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .or 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .or 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_8_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_8_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.reg 5):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_8_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.reg 5):HolArith 80) w s m rfl

-- fr_arith_agree_8_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.reg 5):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.reg 5):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_9_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_9_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.binop .xor 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_9_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.binop .xor 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_9_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.binop .xor 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.binop .xor 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_10_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_10_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsl 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_10_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsl 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_10_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsl 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsl 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_11_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_11_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .lsr 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_11_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .lsr 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_11_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .lsr 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .lsr 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_12_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_12_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .asr 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_12_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .asr 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_12_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .asr 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .asr 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_13_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_13_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.shift .ror 99 3 (.imm 255):HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_13_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.shift .ror 99 3 (.imm 255):HolArith 80) w s m rfl

-- fr_arith_agree_13_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.shift .ror 99 3 (.imm 255):HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.shift .ror 99 3 (.imm 255):HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_write_14_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) (setVar 99 u s) = (none, setVar 99 w (setVar 99 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 80) 99 u w s ⟨rfl, by decide⟩

-- fr_write_14_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) (setVar 77 u s) = (none, setVar 99 w (setVar 77 u s))) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithSetVar (.div 99 3 5:HolArith 80) 77 u w s ⟨rfl, by decide⟩

-- fr_memory_14_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) (m : BitVec 80 → WordLocW 80) :
  (evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) {s with memory := m} = (none, {setVar 99 w s with memory := m})) ↔
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s = (none, setVar 99 w s) :=
  evaluateArithMemory (.div 99 3 5:HolArith 80) w s m rfl

-- fr_arith_agree_14_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s1 = (none, setVar 99 w s1)) (hl : s2.locals = s1.locals) :
  evaluate (.inst (.arith (HolArith.toWordLangArith (.div 99 3 5:HolArith 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateArithAgree (.div 99 3 5:HolArith 80) w s1 s2 ⟨he, rfl, hl⟩

-- fr_load_agree_load_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load 99 3 (-1 : BitVec 80) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load8_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load8 99 3 (-1 : BitVec 80) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load16_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load16 99 3 (-1 : BitVec 80) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

-- fr_load_agree_load32_80
example {C : Type} {F : Type} (w : WordLocW 80) (s1 s2 : WordSemStateFiniteExact 80 C F)
  (he : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s1 = (none, setVar 99 w s1))
  (hl : s2.locals = s1.locals) (hm : s2.memory = s1.memory)
  (hd : s2.mdomain = s1.mdomain) (hb : s2.be = s1.be) :
  evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s2 = (none, setVar 99 w s2) :=
  evaluateLoadAgree .load32 99 3 (-1 : BitVec 80) w s1 s2 ⟨he, rfl, hl, hm, hd, hb⟩

end Flapjack.Test.WordCseEvaluationFramesParity
