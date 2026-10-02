import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapInsert
open Flapjack Flapjack.Compiler.Backend.WordToStack

-- bi_decode_0_0_0_1
example : StackSem.readBitmap (width := 1) (([] ++ appListAppend (.append (.nil : AppList (BitVec 1)) (.list [0]))).drop (0 % 2^1)) = StackSem.readBitmap (width := 1) [0] := by
  apply readBitmapInsertBitmap (width := 1) [0] (.nil) 0 _ (0+1) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_1_1
example : StackSem.readBitmap (width := 1) (([] ++ appListAppend (.append (.nil : AppList (BitVec 1)) (.list [1,0]))).drop (0 % 2^1)) = StackSem.readBitmap (width := 1) [1,0] := by
  apply readBitmapInsertBitmap (width := 1) [1,0] (.nil) 0 _ (0+2) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_0_1
example : StackSem.readBitmap (width := 1) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 1)) (.list [0]))).drop (1 % 2^1)) = StackSem.readBitmap (width := 1) [0] := by
  apply readBitmapInsertBitmap (width := 1) [0] (.nil) 1 _ (1+1) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_1_1
example : StackSem.readBitmap (width := 1) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 1)) (.list [1,0]))).drop (1 % 2^1)) = StackSem.readBitmap (width := 1) [1,0] := by
  apply readBitmapInsertBitmap (width := 1) [1,0] (.nil) 1 _ (1+2) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_0_1
example : StackSem.readBitmap (width := 1) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 1)) (.list [0]))).drop (1 % 2^1)) = StackSem.readBitmap (width := 1) [0] := by
  apply readBitmapInsertBitmap (width := 1) [0] (.list [0]) 1 _ (1+1) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_1_1
example : StackSem.readBitmap (width := 1) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 1)) (.list [1,0]))).drop (1 % 2^1)) = StackSem.readBitmap (width := 1) [1,0] := by
  apply readBitmapInsertBitmap (width := 1) [1,0] (.list [0]) 1 _ (1+2) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_0_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [0]))).drop (0 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.nil) 0 _ (0+1) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_1_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [2,0]))).drop (0 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.nil) 0 _ (0+2) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_0_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [0]))).drop (1 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.nil) 1 _ (1+1) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_1_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [2,0]))).drop (1 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.nil) 1 _ (1+2) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_0_2
example : StackSem.readBitmap (width := 2) (([3,0] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.nil) 2 _ (2+1) 2 [3,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_1_2
example : StackSem.readBitmap (width := 2) (([3,0] ++ appListAppend (.append (.nil : AppList (BitVec 2)) (.list [2,0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.nil) 2 _ (2+2) 2 [3,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_0_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [0]))).drop (1 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.list [0]) 1 _ (1+1) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_1_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [2,0]))).drop (1 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.list [0]) 1 _ (1+2) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_0_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.list [0]) 2 _ (2+1) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_1_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [2,0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.list [0]) 2 _ (2+2) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_0_2
example : StackSem.readBitmap (width := 2) (([3,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.list [0]) 3 _ (3+1) 3 [3,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_1_2
example : StackSem.readBitmap (width := 2) (([3,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 2)) (.list [2,0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.list [0]) 3 _ (3+2) 3 [3,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_0_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 2)) (.list [0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.append (.list [0]) (.list [1])) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_1_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 2)) (.list [2,0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.append (.list [0]) (.list [1])) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_0_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 2)) (.list [0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.append (.list [0]) (.list [1])) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_1_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 2)) (.list [2,0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.append (.list [0]) (.list [1])) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_0_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 2)) (.list [0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_1_2
example : StackSem.readBitmap (width := 2) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 2)) (.list [2,0]))).drop (2 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_0_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 2)) (.list [0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [0] := by
  apply readBitmapInsertBitmap (width := 2) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_1_2
example : StackSem.readBitmap (width := 2) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 2)) (.list [2,0]))).drop (3 % 2^2)) = StackSem.readBitmap (width := 2) [2,0] := by
  apply readBitmapInsertBitmap (width := 2) [2,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_0_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [0]))).drop (0 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.nil) 0 _ (0+1) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_1_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [128,0]))).drop (0 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.nil) 0 _ (0+2) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_0_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [0]))).drop (1 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.nil) 1 _ (1+1) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_1_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [128,0]))).drop (1 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.nil) 1 _ (1+2) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_0_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.nil) 2 _ (2+1) 2 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_1_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.nil : AppList (BitVec 8)) (.list [128,0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.nil) 2 _ (2+2) 2 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_0_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [0]))).drop (1 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.list [0]) 1 _ (1+1) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_1_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [128,0]))).drop (1 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.list [0]) 1 _ (1+2) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_0_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.list [0]) 2 _ (2+1) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_1_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [128,0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.list [0]) 2 _ (2+2) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_0_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.list [0]) 3 _ (3+1) 3 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_1_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 8)) (.list [128,0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.list [0]) 3 _ (3+2) 3 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_0_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.list [0]) (.list [1])) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_1_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [128,0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.list [0]) (.list [1])) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_0_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.list [0]) (.list [1])) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_1_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [128,0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.list [0]) (.list [1])) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_0_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [0]))).drop (4 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.list [0]) (.list [1])) 4 _ (4+1) 4 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_1_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 8)) (.list [128,0]))).drop (4 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.list [0]) (.list [1])) 4 _ (4+2) 4 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_0_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_1_8
example : StackSem.readBitmap (width := 8) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [128,0]))).drop (2 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_0_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_1_8
example : StackSem.readBitmap (width := 8) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [128,0]))).drop (3 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_0_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [0]))).drop (4 % 2^8)) = StackSem.readBitmap (width := 8) [0] := by
  apply readBitmapInsertBitmap (width := 8) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+1) 4 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_1_8
example : StackSem.readBitmap (width := 8) (([255,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 8)) (.list [128,0]))).drop (4 % 2^8)) = StackSem.readBitmap (width := 8) [128,0] := by
  apply readBitmapInsertBitmap (width := 8) [128,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+2) 4 [255,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_0_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [0]))).drop (0 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.nil) 0 _ (0+1) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_1_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (0 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.nil) 0 _ (0+2) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_0_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [0]))).drop (1 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.nil) 1 _ (1+1) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_1_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (1 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.nil) 1 _ (1+2) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_0_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.nil) 2 _ (2+1) 2 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_1_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.nil : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.nil) 2 _ (2+2) 2 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_0_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [0]))).drop (1 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.list [0]) 1 _ (1+1) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_1_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (1 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.list [0]) 1 _ (1+2) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_0_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.list [0]) 2 _ (2+1) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_1_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.list [0]) 2 _ (2+2) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_0_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.list [0]) 3 _ (3+1) 3 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_1_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.list [0]) 3 _ (3+2) 3 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_0_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.list [0]) (.list [1])) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_1_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.list [0]) (.list [1])) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_0_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.list [0]) (.list [1])) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_1_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.list [0]) (.list [1])) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_0_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [0]))).drop (4 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.list [0]) (.list [1])) 4 _ (4+1) 4 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_1_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (4 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.list [0]) (.list [1])) 4 _ (4+2) 4 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_0_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_1_64
example : StackSem.readBitmap (width := 64) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (2 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_0_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_1_64
example : StackSem.readBitmap (width := 64) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (3 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_0_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [0]))).drop (4 % 2^64)) = StackSem.readBitmap (width := 64) [0] := by
  apply readBitmapInsertBitmap (width := 64) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+1) 4 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_1_64
example : StackSem.readBitmap (width := 64) (([18446744073709551615,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 64)) (.list [9223372036854775808,0]))).drop (4 % 2^64)) = StackSem.readBitmap (width := 64) [9223372036854775808,0] := by
  apply readBitmapInsertBitmap (width := 64) [9223372036854775808,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+2) 4 [18446744073709551615,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_0_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [0]))).drop (0 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.nil) 0 _ (0+1) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_0_1_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (0 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.nil) 0 _ (0+2) 0 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_0_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [0]))).drop (1 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.nil) 1 _ (1+1) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_1_1_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (1 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.nil) 1 _ (1+2) 1 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_0_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.nil) 2 _ (2+1) 2 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_0_2_1_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.nil : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.nil) 2 _ (2+2) 2 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_0_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [0]))).drop (1 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.list [0]) 1 _ (1+1) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_0_1_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (1 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.list [0]) 1 _ (1+2) 1 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_0_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.list [0]) 2 _ (2+1) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_1_1_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.list [0]) 2 _ (2+2) 2 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_0_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.list [0]) 3 _ (3+1) 3 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_1_2_1_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.list [0] : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.list [0]) 3 _ (3+2) 3 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_0_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.list [0]) (.list [1])) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_0_1_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.list [0]) (.list [1])) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_0_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.list [0]) (.list [1])) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_1_1_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.list [0]) (.list [1])) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_0_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [0]))).drop (4 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.list [0]) (.list [1])) 4 _ (4+1) 4 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_2_2_1_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.append (.list [0]) (.list [1]) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (4 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.list [0]) (.list [1])) 4 _ (4+2) 4 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_0_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+1) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_0_1_80
example : StackSem.readBitmap (width := 80) (([] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (2 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 2 _ (2+2) 2 []
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_0_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+1) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_1_1_80
example : StackSem.readBitmap (width := 80) (([0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (3 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 3 _ (3+2) 3 [0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_0_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [0]))).drop (4 % 2^80)) = StackSem.readBitmap (width := 80) [0] := by
  apply readBitmapInsertBitmap (width := 80) [0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+1) 4 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

-- bi_decode_3_2_1_80
example : StackSem.readBitmap (width := 80) (([1208925819614629174706175,0] ++ appListAppend (.append (.append (.append .nil (.list [1])) (.append (.list [0]) .nil) : AppList (BitVec 80)) (.list [604462909807314587353088,0]))).drop (4 % 2^80)) = StackSem.readBitmap (width := 80) [604462909807314587353088,0] := by
  apply readBitmapInsertBitmap (width := 80) [604462909807314587353088,0] (.append (.append .nil (.list [1])) (.append (.list [0]) .nil)) 4 _ (4+2) 4 [1208925819614629174706175,0]
  · decide
  · simp +decide <;> decide +kernel
  · rfl
  · rfl

example {width : Nat} [NeZero width] (bm : List (BitVec width)) (old new : AppList (BitVec width)) (n next i : Nat) (cur : List (BitVec width)) (hi : i < 2^width) (hb : (StackSem.readBitmap bm).isSome = true) (hn : n = cur.length+(appListAppend old).length) (hout : insertBitmap bm (old,n) = ((new,next),i)) := readBitmapInsertBitmap bm old n new next i cur hi hb hn hout
