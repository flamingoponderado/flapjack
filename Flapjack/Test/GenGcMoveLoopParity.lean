import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveLoop

/-! Kernel replay of the five original HOL collector observations captured in
`stack_alloc_gen_loop_statement_probe.out`; no native-decide oracle. -/
namespace Flapjack.Test.GenGcMoveLoopParity
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, be := false,
    callEmptyFfi := false, gcKind := .simple }
private theorem dataRun (k : Nat) (hk : k ≠ 0) :
    wordGenGcMoveData conf k
      ((100 : BitVec 64), 7, 108, 50, 3000, 1000, (fun _ => .word 4), (fun _ => true)) =
      (7,108,50,3000,(fun _ => .word 4),true) := by
  have h : (100 : BitVec 64) ≠ 108 := by decide
  have hb : (4 : BitVec 64).getLsbD 2 = true := by decide
  have hd : decodeLength conf (4 : BitVec 64) = 0 := by rfl
  have ha : (100 : BitVec 64) + (0 + 1) * wordSemBytesInWord = 108 := by rfl
  rw [wordGenGcMoveData]
  simp only [h, if_false, hk, wordSemTheWord, wordSemIsWordLoc, hb, if_true, hd, ha]
  rw [wordGenGcMoveData]
  simp
private theorem genListZero (a i pa ib pb old : BitVec 64)
    (m : BitVec 64 → WordLocW 64) (dm : BitVec 64 → Bool) :
    wordGenGcMoveList conf (a, 0, i, pa, ib, pb, old, m, dm) =
      (a, i, pa, ib, pb, m, true) := by
  rw [wordGenGcMoveList]
  simp
private theorem refsRun (k : Nat) (hk : k ≠ 0) :
    wordGenGcMoveRefs conf k
      ((100 : BitVec 64),108,7,2000,50,100,1000,(fun _ => .word 0),(fun _ => true)) =
      (108,7,2000,50,100,(fun _ => .word 0),true) := by
  have h : (100 : BitVec 64) ≠ 108 := by decide
  have hd : decodeLength conf (0 : BitVec 64) = 0 := by rfl
  have ha : (100 : BitVec 64) + wordSemBytesInWord = 108 := by rfl
  rw [wordGenGcMoveRefs]
  simp only [h, if_false, hk, wordSemTheWord, wordSemIsWordLoc, hd, ha]
  rw [genListZero]
  rw [wordGenGcMoveRefs]
  simp

-- Original gen_loop_stop.
example :
    (let (i,pa,ib,pb,m,c) := wordGenGcMoveLoop conf 0
      ((2000 : BitVec 64),7,2000,50,100,100,1000,(fun _ => .word 4),(fun _ => true))
     (i,pa,ib,pb,m 100,m 108,c)) =
      (7,2000,50,100,.word 4,.word 4,true) := by
  rw [wordGenGcMoveLoop]
  simp

-- Original gen_loop_data_fuel_zero.
example :
    (let (i,pa,ib,pb,m,c) := wordGenGcMoveLoop conf 0
      ((100 : BitVec 64),7,108,50,3000,3000,1000,(fun _ => .word 4),(fun _ => true))
     (i,pa,ib,pb,m 100,m 108,c)) =
      (7,108,50,3000,.word 4,.word 4,false) := by
  rw [wordGenGcMoveLoop]
  simp only [if_true, show (100 : BitVec 64) ≠ 108 by decide, if_false]
  rw [dataRun (2 ^ 64) (by decide)]

-- Original gen_loop_data_one.
example :
    (let (i,pa,ib,pb,m,c) := wordGenGcMoveLoop conf 1
      ((100 : BitVec 64),7,108,50,3000,3000,1000,(fun _ => .word 4),(fun _ => true))
     (i,pa,ib,pb,m 100,m 108,c)) =
      (7,108,50,3000,.word 4,.word 4,true) := by
  rw [wordGenGcMoveLoop]
  simp only [if_true, show (100 : BitVec 64) ≠ 108 by decide, if_false]
  rw [dataRun (2 ^ 64) (by decide)]
  simp only [Nat.one_ne_zero, if_false]
  rw [wordGenGcMoveLoop]
  simp

-- Original gen_loop_refs_fuel_zero.
example :
    (let (i,pa,ib,pb,m,c) := wordGenGcMoveLoop conf 0
      ((2000 : BitVec 64),7,2000,50,100,108,1000,(fun _ => .word 0),(fun _ => true))
     (i,pa,ib,pb,m 100,m 108,c)) =
      (7,2000,50,100,.word 0,.word 0,false) := by
  rw [wordGenGcMoveLoop]
  simp only [show (108 : BitVec 64) ≠ 100 by decide, if_false]
  rw [refsRun (2 ^ 64) (by decide)]
  simp

-- Original gen_loop_refs_one.
example :
    (let (i,pa,ib,pb,m,c) := wordGenGcMoveLoop conf 1
      ((2000 : BitVec 64),7,2000,50,100,108,1000,(fun _ => .word 0),(fun _ => true))
     (i,pa,ib,pb,m 100,m 108,c)) =
      (7,2000,50,100,.word 0,.word 0,true) := by
  rw [wordGenGcMoveLoop]
  simp only [show (108 : BitVec 64) ≠ 100 by decide, if_false]
  rw [refsRun (2 ^ 64) (by decide)]
  simp only [Nat.one_ne_zero, if_false]
  rw [wordGenGcMoveLoop]
  simp

end Flapjack.Test.GenGcMoveLoopParity
