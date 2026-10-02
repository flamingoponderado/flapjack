import Flapjack.Compiler.Backend.WordCse.Proofs.LoadEvaluation
namespace Flapjack.Test.WordCseLoadEvaluationParity
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordCse WordSemStateFiniteExact
-- ld_any_load_98_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 98 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 1) w s 98 ⟨rfl, h⟩

-- ld_any_load_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 3 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 1) w s 3 ⟨rfl, h⟩

-- ld_write_load_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 1) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 1) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 99 (.addr 5 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load 99 3 5 (-1 : BitVec 1) w s ⟨rfl, hl, h⟩

-- ld_any_load8_98_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 98 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 1) w s 98 ⟨rfl, h⟩

-- ld_any_load8_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 3 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 1) w s 3 ⟨rfl, h⟩

-- ld_write_load8_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 1) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load8_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 1) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load8_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 99 (.addr 5 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load8 99 3 5 (-1 : BitVec 1) w s ⟨rfl, hl, h⟩

-- ld_any_load16_98_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 98 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 1) w s 98 ⟨rfl, h⟩

-- ld_any_load16_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 3 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 1) w s 3 ⟨rfl, h⟩

-- ld_write_load16_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 1) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load16_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 1) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load16_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 99 (.addr 5 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load16 99 3 5 (-1 : BitVec 1) w s ⟨rfl, hl, h⟩

-- ld_any_load32_98_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 98 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 1) w s 98 ⟨rfl, h⟩

-- ld_any_load32_3_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 3 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 1) w s 3 ⟨rfl, h⟩

-- ld_write_load32_99_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 1) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load32_77_1
example {C : Type} {F : Type} (u w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 1) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load32_1
example {C : Type} {F : Type} (w : WordLocW 1) (s : WordSemStateFiniteExact 1 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 1)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 99 (.addr 5 (-1 : BitVec 1)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load32 99 3 5 (-1 : BitVec 1) w s ⟨rfl, hl, h⟩

-- ld_any_load_98_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 98 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 32) w s 98 ⟨rfl, h⟩

-- ld_any_load_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 3 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 32) w s 3 ⟨rfl, h⟩

-- ld_write_load_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 32) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 32) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 99 (.addr 5 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load 99 3 5 (-1 : BitVec 32) w s ⟨rfl, hl, h⟩

-- ld_any_load8_98_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 98 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 32) w s 98 ⟨rfl, h⟩

-- ld_any_load8_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 3 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 32) w s 3 ⟨rfl, h⟩

-- ld_write_load8_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 32) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load8_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 32) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load8_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 99 (.addr 5 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load8 99 3 5 (-1 : BitVec 32) w s ⟨rfl, hl, h⟩

-- ld_any_load16_98_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 98 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 32) w s 98 ⟨rfl, h⟩

-- ld_any_load16_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 3 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 32) w s 3 ⟨rfl, h⟩

-- ld_write_load16_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 32) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load16_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 32) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load16_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 99 (.addr 5 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load16 99 3 5 (-1 : BitVec 32) w s ⟨rfl, hl, h⟩

-- ld_any_load32_98_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 98 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 32) w s 98 ⟨rfl, h⟩

-- ld_any_load32_3_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 3 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 32) w s 3 ⟨rfl, h⟩

-- ld_write_load32_99_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 32) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load32_77_32
example {C : Type} {F : Type} (u w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 32) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load32_32
example {C : Type} {F : Type} (w : WordLocW 32) (s : WordSemStateFiniteExact 32 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 32)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 99 (.addr 5 (-1 : BitVec 32)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load32 99 3 5 (-1 : BitVec 32) w s ⟨rfl, hl, h⟩

-- ld_any_load_98_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 98 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 64) w s 98 ⟨rfl, h⟩

-- ld_any_load_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 3 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 64) w s 3 ⟨rfl, h⟩

-- ld_write_load_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 64) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 64) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 99 (.addr 5 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load 99 3 5 (-1 : BitVec 64) w s ⟨rfl, hl, h⟩

-- ld_any_load8_98_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 98 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 64) w s 98 ⟨rfl, h⟩

-- ld_any_load8_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 3 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 64) w s 3 ⟨rfl, h⟩

-- ld_write_load8_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 64) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load8_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 64) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load8_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 99 (.addr 5 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load8 99 3 5 (-1 : BitVec 64) w s ⟨rfl, hl, h⟩

-- ld_any_load16_98_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 98 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 64) w s 98 ⟨rfl, h⟩

-- ld_any_load16_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 3 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 64) w s 3 ⟨rfl, h⟩

-- ld_write_load16_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 64) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load16_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 64) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load16_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 99 (.addr 5 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load16 99 3 5 (-1 : BitVec 64) w s ⟨rfl, hl, h⟩

-- ld_any_load32_98_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 98 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 64) w s 98 ⟨rfl, h⟩

-- ld_any_load32_3_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 3 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 64) w s 3 ⟨rfl, h⟩

-- ld_write_load32_99_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 64) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load32_77_64
example {C : Type} {F : Type} (u w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 64) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load32_64
example {C : Type} {F : Type} (w : WordLocW 64) (s : WordSemStateFiniteExact 64 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 64)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 99 (.addr 5 (-1 : BitVec 64)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load32 99 3 5 (-1 : BitVec 64) w s ⟨rfl, hl, h⟩

-- ld_any_load_98_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 98 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 80) w s 98 ⟨rfl, h⟩

-- ld_any_load_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 3 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load 99 3 (-1 : BitVec 80) w s 3 ⟨rfl, h⟩

-- ld_write_load_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 80) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load 99 3 (-1 : BitVec 80) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load 99 (.addr 5 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load 99 3 5 (-1 : BitVec 80) w s ⟨rfl, hl, h⟩

-- ld_any_load8_98_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 98 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 80) w s 98 ⟨rfl, h⟩

-- ld_any_load8_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 3 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load8 99 3 (-1 : BitVec 80) w s 3 ⟨rfl, h⟩

-- ld_write_load8_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 80) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load8_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load8 99 3 (-1 : BitVec 80) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load8_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load8 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load8 99 (.addr 5 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load8 99 3 5 (-1 : BitVec 80) w s ⟨rfl, hl, h⟩

-- ld_any_load16_98_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 98 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 80) w s 98 ⟨rfl, h⟩

-- ld_any_load16_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 3 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load16 99 3 (-1 : BitVec 80) w s 3 ⟨rfl, h⟩

-- ld_write_load16_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 80) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load16_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load16 99 3 (-1 : BitVec 80) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load16_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load16 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load16 99 (.addr 5 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load16 99 3 5 (-1 : BitVec 80) w s ⟨rfl, hl, h⟩

-- ld_any_load32_98_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 98 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 98 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 80) w s 98 ⟨rfl, h⟩

-- ld_any_load32_3_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 3 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 3 w s) :=
  evaluateLoadAnyDest .load32 99 3 (-1 : BitVec 80) w s 3 ⟨rfl, h⟩

-- ld_write_load32_99_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) (setVar 99 u s) =
      (none, setVar 99 w (setVar 99 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 80) 99 u w s ⟨rfl, by decide⟩

-- ld_write_load32_77_80
example {C : Type} {F : Type} (u w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F) :
    (evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) (setVar 77 u s) =
      (none, setVar 99 w (setVar 77 u s))) ↔
    evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadSetVar .load32 99 3 (-1 : BitVec 80) 77 u w s ⟨rfl, by decide⟩

-- ld_addr_load32_80
example {C : Type} {F : Type} (w : WordLocW 80) (s : WordSemStateFiniteExact 80 C F)
    (hl : sptLookup 5 s.locals = sptLookup 3 s.locals)
    (h : evaluate (.inst (.mem .load32 99 (.addr 3 (-1 : BitVec 80)))) s = (none, setVar 99 w s)) :
    evaluate (.inst (.mem .load32 99 (.addr 5 (-1 : BitVec 80)))) s = (none, setVar 99 w s) :=
  evaluateLoadChangeAddr .load32 99 3 5 (-1 : BitVec 80) w s ⟨rfl, hl, h⟩

end Flapjack.Test.WordCseLoadEvaluationParity
