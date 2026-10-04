import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveData

/-! Kernel replay of seven determinate original HOL partial-data collector rows.
No concrete nonword-header output is claimed: HOL's `theWord (Loc ...)` is
unspecified. The general simulation theorem covers successful collector calls.
-/
namespace Flapjack.Test.GenPartialMoveDataParity
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

-- Original partial_data_empty.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 0
      ((100 : BitVec 64), 7, 100, 1000, (fun _ => .word 4), (fun _ => true), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 100, .word 4, .word 4, .word 4, true) := by
  simp [wordGenGcPartialMoveData]

-- Original partial_data_fuel_zero.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 0
      ((100 : BitVec 64), 7, 108, 1000, (fun _ => .word 4), (fun _ => true), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 108, .word 4, .word 4, .word 4, false) := by
  simp [wordGenGcPartialMoveData]

-- Original partial_data_skip_zero_length.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 1
      ((100 : BitVec 64), 7, 108, 1000, (fun _ => .word 4), (fun _ => true), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 108, .word 4, .word 4, .word 4, true) := by
  have h : (100 : BitVec 64) ≠ 108 := by decide
  have hb : (4 : BitVec 64).getLsbD 2 = true := by decide
  have hd : decodeLength conf (4 : BitVec 64) = 0 := by rfl
  have ha : (100 : BitVec 64) + (0 + 1) * wordSemBytesInWord = 108 := by rfl
  rw [wordGenGcPartialMoveData]
  simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc,
    hb, if_true, hd, ha]
  rw [wordGenGcPartialMoveData]
  simp

-- Original partial_data_skip_one_length.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 1
      ((100 : BitVec 64), 7, 116, 1000, (fun _ => .word 0x1000000000004), (fun _ => true), 8, 32)
     (i, pa, m 100, m 116, m 116, c)) =
      (7, 116, .word 0x1000000000004, .word 0x1000000000004, .word 0x1000000000004, true) := by
  have h : (100 : BitVec 64) ≠ 116 := by decide
  have hb : (0x1000000000004 : BitVec 64).getLsbD 2 = true := by decide
  have hd : decodeLength conf (0x1000000000004 : BitVec 64) = 1 := by rfl
  have ha : (100 : BitVec 64) + (1 + 1) * wordSemBytesInWord = 116 := by rfl
  rw [wordGenGcPartialMoveData]
  simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc,
    hb, if_true, hd, ha]
  rw [wordGenGcPartialMoveData]
  simp

-- Original partial_data_missing_domain.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 1
      ((100 : BitVec 64), 7, 108, 1000, (fun _ => .word 4), (fun _ => false), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 108, .word 4, .word 4, .word 4, false) := by
  have h : (100 : BitVec 64) ≠ 108 := by decide
  have hb : (4 : BitVec 64).getLsbD 2 = true := by decide
  have hd : decodeLength conf (4 : BitVec 64) = 0 := by rfl
  have ha : (100 : BitVec 64) + (0 + 1) * wordSemBytesInWord = 108 := by rfl
  rw [wordGenGcPartialMoveData]
  simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc,
    hb, if_true, hd, ha]
  rw [wordGenGcPartialMoveData]
  simp

-- Original partial_data_pointer_zero_length.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 1
      ((100 : BitVec 64), 7, 108, 1000, (fun _ => .word 0), (fun _ => true), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 108, .word 0, .word 0, .word 0, true) := by
  have h : (100 : BitVec 64) ≠ 108 := by decide
  have hb : (0 : BitVec 64).getLsbD 2 = false := by decide
  have hd : decodeLength conf (0 : BitVec 64) = 0 := by rfl
  have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
  rw [wordGenGcPartialMoveData]
  simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc,
    hb, Bool.false_eq_true, hd, ha, wordGenGcPartialMoveList_zero]
  rw [wordGenGcPartialMoveData]
  simp

-- Original partial_data_pointer_small_field.
example :
    (let (i, pa, m, c) := wordGenGcPartialMoveData conf 1
      ((100 : BitVec 64), 7, 116, 1000,
        (fun a => .word (if a = 100 then 0x1000000000000 else 4)), (fun _ => true), 8, 32)
     (i, pa, m 100, m 108, m 116, c)) =
      (7, 116, .word 0x1000000000000, .word 4, .word 4, true) := by
  have h : (100 : BitVec 64) ≠ 116 := by decide
  have hb : (0x1000000000000 : BitVec 64).getLsbD 2 = false := by decide
  have hd : decodeLength conf (0x1000000000000 : BitVec 64) = 1 := by rfl
  have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
  have hn : (108 : BitVec 64) ≠ 100 := by decide
  have hm : (116 : BitVec 64) ≠ 100 := by decide
  have hadd : (108 : BitVec 64) + wordSemBytesInWord = 116 := by rfl
  rw [wordGenGcPartialMoveData]
  simp only [h, if_false, Nat.one_ne_zero, if_true, wordSemTheWord, wordSemIsWordLoc,
    hb, Bool.false_eq_true, hd, ha]
  rw [wordGenGcPartialMoveList]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide, if_false, hn,
    wordSemBytesInWord, wordGenGcPartialMove]
  simp only [wordSemIsWordLoc, wordSemTheWord]
  have hz : (1 : BitVec 64) - 1 = 0 := by decide
  simp only [conf, hz, wordGenGcPartialMoveList_zero]
  rw [wordGenGcPartialMoveData]
  simp [gcUpdate]

end Flapjack.Test.GenPartialMoveDataParity
