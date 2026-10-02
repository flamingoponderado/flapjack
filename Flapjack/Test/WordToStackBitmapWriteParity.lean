import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWrite
open Flapjack Flapjack.Compiler.Backend.WordToStack
set_option maxRecDepth 8192

private theorem fixtureEnumeration0 : sptToAList (sptFromAList [] : Spt Nat) = [] := by
  rfl

private theorem fixtureEnumeration1 : sptToAList (sptFromAList [(0,0)] : Spt Nat) = [(0,0)] := by
  simp +decide [sptFromAList, sptInsert, sptToAList, sptFoldi] <;> decide +kernel

private theorem fixtureEnumeration2 : sptToAList (sptFromAList [(2,7),(4,9)] : Spt Nat) = [(4,9),(2,7)] := by
  simp +decide [sptFromAList, sptInsert, sptToAList, sptFoldi, lrNext] <;> decide +kernel

private theorem fixtureEnumeration3 : sptToAList (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) = [(1,10),(2,11),(130,12)] := by
  simp +decide [sptFromAList, sptInsert, sptToAList, sptFoldi, lrNext] <;> decide +kernel

private theorem fixtureEnumeration4 : sptToAList (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) = [(0,1),(2,3)] := by
  simp +decide [sptFromAList, sptInsert, sptToAList, sptFoldi, lrNext] <;> decide +kernel

private theorem fixtureEnumeration5 : sptToAList (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) = [(1208925819614629174706176,5),(1208925819614629174706178,8)] := by
  simp +decide [sptFromAList, sptInsert, sptToAList, sptFoldi, lrNext] <;> decide +kernel

-- bw_decode_0_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 0 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 2 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 1208925819614629174706176 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 0 7) = some [false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 2 7) = some [false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 0 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 2 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_1_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 0 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 2 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 0 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 2 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_2_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 7) = some [false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_3_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 7) = some [true,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 7) = some [true,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 17) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 17) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_4_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 7) = some [false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_5_0_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 7) = some [true,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 7) = some [true,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 7) = some [false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_0_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 17) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_1_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 17) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_2_8
example : StackSem.readBitmap (writeBitmapExact (width := 8) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 17) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_0_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 0 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 2 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 1208925819614629174706176 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 0 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 2 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 0 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 2 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_1_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 0 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 2 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 0 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 2 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_2_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_3_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 63) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 63) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_4_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_5_0_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 63) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 63) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 63) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_0_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 129) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_1_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 129) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_2_64
example : StackSem.readBitmap (writeBitmapExact (width := 64) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 129) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_0_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 0 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 2 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 1208925819614629174706176 1) = some [false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 0 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 2 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 0 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 2 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_0_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration0]
  decide

-- bw_decode_1_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 0 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 2 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 0 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 2 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_1_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,0)] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration1]
  decide

-- bw_decode_2_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 0 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 2 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_2_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(2,7),(4,9)] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration2]
  decide

-- bw_decode_3_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 0 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 2 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_3_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1,10),(2,11),(130,12)] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration3]
  decide

-- bw_decode_4_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 0 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 2 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_4_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(0,1),(0,99),(2,3)] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration4]
  decide

-- bw_decode_5_0_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_0_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 0) = some [] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_1_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 1) = some [true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 79) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 79) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_2_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 79) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_0_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 0 161) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_1_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 2 161) = some [true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

-- bw_decode_5_3_2_80
example : StackSem.readBitmap (writeBitmapExact (width := 80) (sptFromAList [(1208925819614629174706176,5),(1208925819614629174706178,8)] : Spt Nat) 1208925819614629174706176 161) = some [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] := by
  rw [readBitmapWriteBitmap _ _ _ (by decide)]
  rw [fixtureEnumeration5]
  decide

example {width : Nat} [NeZero width] {α : Type} (names : Spt α) (k f : Nat) (h : 8 ≤ width) := readBitmapWriteBitmap names k f h
