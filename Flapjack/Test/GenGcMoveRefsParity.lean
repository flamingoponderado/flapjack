import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveRefs

/-! Kernel replay of five original HOL generational reference-block rows from
`stack_alloc_gen_refs_statement_probe.out`. Observations include collector
pointers, counters, three memory addresses, and the full success Boolean. -/
namespace Flapjack.Test.GenGcMoveRefsParity
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, hasFpOps := false, hasFpTern := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

/-- Fixture infrastructure: the native zero-payload equation. -/
private theorem genListZero (a i pa ib pb old : BitVec 64)
    (m : BitVec 64 → WordLocW 64) (dm : BitVec 64 → Bool) :
    wordGenGcMoveList conf (a, 0, i, pa, ib, pb, old, m, dm) =
      (a, i, pa, ib, pb, m, true) := by
  rw [wordGenGcMoveList]
  simp

-- Original gen_refs_empty.
example :
    (let (re,i,pa,ib,pb,m,c) := wordGenGcMoveRefs conf 0
      ((100 : BitVec 64), 100, 7, 2000, 50, 3000, 1000, (fun _ => .word 4), (fun _ => true))
     (re,i,pa,ib,pb,m 100,m 108,m 116,c)) =
      (100,7,2000,50,3000,.word 4,.word 4,.word 4,true) := by
  simp [wordGenGcMoveRefs]

-- Original gen_refs_fuel_zero.
example :
    (let (re,i,pa,ib,pb,m,c) := wordGenGcMoveRefs conf 0
      ((100 : BitVec 64), 108, 7, 2000, 50, 3000, 1000, (fun _ => .word 4), (fun _ => true))
     (re,i,pa,ib,pb,m 100,m 108,m 116,c)) =
      (100,7,2000,50,3000,.word 4,.word 4,.word 4,false) := by
  simp [wordGenGcMoveRefs]

-- Original gen_refs_zero_payload.
example :
    (let (re,i,pa,ib,pb,m,c) := wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 108, 7, 2000, 50, 3000, 1000, (fun _ => .word 0), (fun _ => true))
     (re,i,pa,ib,pb,m 100,m 108,m 116,c)) =
      (108,7,2000,50,3000,.word 0,.word 0,.word 0,true) := by
  have hr : wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 108, 7, 2000, 50, 3000, 1000, (fun _ => .word 0), (fun _ => true)) =
      (108,7,2000,50,3000,(fun _ => .word 0),true) := by
    have h : (100 : BitVec 64) ≠ 108 := by decide
    have hd : decodeLength conf (0 : BitVec 64) = 0 := by rfl
    have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
    rw [wordGenGcMoveRefs]
    simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc, hd, ha]
    rw [genListZero]
    rw [wordGenGcMoveRefs]
    simp
  rw [hr]

-- Original gen_refs_small_field.
example :
    (let (re,i,pa,ib,pb,m,c) := wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 116, 7, 2000, 50, 3000, 1000, (fun a => .word (if a = 100 then 0x1000000000000 else 4)), (fun _ => true))
     (re,i,pa,ib,pb,m 100,m 108,m 116,c)) =
      (116,7,2000,50,3000,.word 0x1000000000000,.word 4,.word 4,true) := by
  have hr : wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 116, 7, 2000, 50, 3000, 1000, (fun a => .word (if a = 100 then 0x1000000000000 else 4)), (fun _ => true)) =
      (116,7,2000,50,3000,gcUpdate (108 : BitVec 64) (.word 4) (fun a => .word (if a = 100 then 0x1000000000000 else 4)),true) := by
    have h : (100 : BitVec 64) ≠ 116 := by decide
    have hd : decodeLength conf (0x1000000000000 : BitVec 64) = 1 := by rfl
    have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
    rw [wordGenGcMoveRefs]
    simp only [h, if_false, Nat.one_ne_zero, if_true, wordSemTheWord, wordSemIsWordLoc, hd, ha]
    have hn : (108 : BitVec 64) ≠ 100 := by decide
    have hz : (1 : BitVec 64) - 1 = 0 := by decide
    have hb : (108 : BitVec 64) + wordSemBytesInWord = 116 := by rfl
    rw [wordGenGcMoveList]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide, if_false, hn, wordGenGcMove]
    simp only [show (1 : BitVec 64) &&& 4 = 0 from by decide, if_true, hz, hb]
    rw [genListZero]
    rw [wordGenGcMoveRefs]
    simp
  rw [hr]
  simp [gcUpdate]

-- Original gen_refs_missing_domain.
example :
    (let (re,i,pa,ib,pb,m,c) := wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 108, 7, 2000, 50, 3000, 1000, (fun _ => .word 0), (fun _ => false))
     (re,i,pa,ib,pb,m 100,m 108,m 116,c)) =
      (108,7,2000,50,3000,.word 0,.word 0,.word 0,false) := by
  have hr : wordGenGcMoveRefs conf 1
      ((100 : BitVec 64), 108, 7, 2000, 50, 3000, 1000, (fun _ => .word 0), (fun _ => false)) =
      (108,7,2000,50,3000,(fun _ => .word 0),false) := by
    have h : (100 : BitVec 64) ≠ 108 := by decide
    have hd : decodeLength conf (0 : BitVec 64) = 0 := by rfl
    have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
    rw [wordGenGcMoveRefs]
    simp only [h, if_false, Nat.one_ne_zero, wordSemTheWord, wordSemIsWordLoc, hd, ha]
    rw [genListZero]
    rw [wordGenGcMoveRefs]
    simp
  rw [hr]

end Flapjack.Test.GenGcMoveRefsParity
