import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapBitStructure
open Flapjack.Compiler.Backend.WordToStack
set_option maxRecDepth 4096

-- bs_snoc_0_0_1
example : bitsToWordW ([] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 0) ||| (bitsToWordW []:BitVec 1) := bitsToWordSnoc [] false

-- bs_value_0_0_1
example : (bitsToWordW ([] ++ [false]) : BitVec 1).toNat = 0 := by decide

-- bs_snoc_0_1_1
example : bitsToWordW ([] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 0) ||| (bitsToWordW []:BitVec 1) := bitsToWordSnoc [] true

-- bs_value_0_1_1
example : (bitsToWordW ([] ++ [true]) : BitVec 1).toNat = 1 := by decide

-- bs_miss_0_0_1
example : (bitsToWordW []:BitVec 1).getLsbD 0 = false := bitsToWordMiss [] 0 ⟨by decide,by decide⟩

-- bs_snoc_1_0_1
example : bitsToWordW ([false] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 1) := bitsToWordSnoc [false] false

-- bs_value_1_0_1
example : (bitsToWordW ([false] ++ [false]) : BitVec 1).toNat = 0 := by decide

-- bs_snoc_1_1_1
example : bitsToWordW ([false] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 1) := bitsToWordSnoc [false] true

-- bs_value_1_1_1
example : (bitsToWordW ([false] ++ [true]) : BitVec 1).toNat = 0 := by decide

-- bs_snoc_2_0_1
example : bitsToWordW ([true] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 1) := bitsToWordSnoc [true] false

-- bs_value_2_0_1
example : (bitsToWordW ([true] ++ [false]) : BitVec 1).toNat = 1 := by decide

-- bs_snoc_2_1_1
example : bitsToWordW ([true] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 1) := bitsToWordSnoc [true] true

-- bs_value_2_1_1
example : (bitsToWordW ([true] ++ [true]) : BitVec 1).toNat = 1 := by decide

-- bs_snoc_3_0_1
example : bitsToWordW ([true,false,true] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 1) := bitsToWordSnoc [true,false,true] false

-- bs_value_3_0_1
example : (bitsToWordW ([true,false,true] ++ [false]) : BitVec 1).toNat = 1 := by decide

-- bs_snoc_3_1_1
example : bitsToWordW ([true,false,true] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 1) := bitsToWordSnoc [true,false,true] true

-- bs_value_3_1_1
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 1).toNat = 1 := by decide

-- bs_snoc_4_0_1
example : bitsToWordW ([false,true,false,true] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 1) := bitsToWordSnoc [false,true,false,true] false

-- bs_value_4_0_1
example : (bitsToWordW ([false,true,false,true] ++ [false]) : BitVec 1).toNat = 0 := by decide

-- bs_snoc_4_1_1
example : bitsToWordW ([false,true,false,true] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 1) := bitsToWordSnoc [false,true,false,true] true

-- bs_value_4_1_1
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 1).toNat = 0 := by decide

-- bs_snoc_5_0_1
example : bitsToWordW ([true,true,true] ++ [false]) = ((if false then (1:BitVec 1) else 0) <<< 3) ||| (bitsToWordW [true,true,true]:BitVec 1) := bitsToWordSnoc [true,true,true] false

-- bs_value_5_0_1
example : (bitsToWordW ([true,true,true] ++ [false]) : BitVec 1).toNat = 1 := by decide

-- bs_snoc_5_1_1
example : bitsToWordW ([true,true,true] ++ [true]) = ((if true then (1:BitVec 1) else 0) <<< 3) ||| (bitsToWordW [true,true,true]:BitVec 1) := bitsToWordSnoc [true,true,true] true

-- bs_value_5_1_1
example : (bitsToWordW ([true,true,true] ++ [true]) : BitVec 1).toNat = 1 := by decide

-- bs_prefix_0_1
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ []):BitVec 1).getLsbD i) = [] := genlistBitsToWordAlt [] [] (by decide)

-- bs_prefix_1_1
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]):BitVec 1).getLsbD i) = [] := genlistBitsToWordAlt [] [true] (by decide)

-- bs_prefix_2_1
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 1).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_prefix_3_1
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ []):BitVec 1).getLsbD i) = [false] := genlistBitsToWordAlt [false] [] (by decide)

-- bs_prefix_6_1
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 1).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_snoc_0_0_2
example : bitsToWordW ([] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 0) ||| (bitsToWordW []:BitVec 2) := bitsToWordSnoc [] false

-- bs_value_0_0_2
example : (bitsToWordW ([] ++ [false]) : BitVec 2).toNat = 0 := by decide

-- bs_snoc_0_1_2
example : bitsToWordW ([] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 0) ||| (bitsToWordW []:BitVec 2) := bitsToWordSnoc [] true

-- bs_value_0_1_2
example : (bitsToWordW ([] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- bs_miss_0_0_2
example : (bitsToWordW []:BitVec 2).getLsbD 0 = false := bitsToWordMiss [] 0 ⟨by decide,by decide⟩

-- bs_miss_0_1_2
example : (bitsToWordW []:BitVec 2).getLsbD 1 = false := bitsToWordMiss [] 1 ⟨by decide,by decide⟩

-- bs_snoc_1_0_2
example : bitsToWordW ([false] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 2) := bitsToWordSnoc [false] false

-- bs_value_1_0_2
example : (bitsToWordW ([false] ++ [false]) : BitVec 2).toNat = 0 := by decide

-- bs_snoc_1_1_2
example : bitsToWordW ([false] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 2) := bitsToWordSnoc [false] true

-- bs_value_1_1_2
example : (bitsToWordW ([false] ++ [true]) : BitVec 2).toNat = 2 := by decide

-- bs_miss_1_1_2
example : (bitsToWordW [false]:BitVec 2).getLsbD 1 = false := bitsToWordMiss [false] 1 ⟨by decide,by decide⟩

-- bs_snoc_2_0_2
example : bitsToWordW ([true] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 2) := bitsToWordSnoc [true] false

-- bs_value_2_0_2
example : (bitsToWordW ([true] ++ [false]) : BitVec 2).toNat = 1 := by decide

-- bs_snoc_2_1_2
example : bitsToWordW ([true] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 2) := bitsToWordSnoc [true] true

-- bs_value_2_1_2
example : (bitsToWordW ([true] ++ [true]) : BitVec 2).toNat = 3 := by decide

-- bs_miss_2_1_2
example : (bitsToWordW [true]:BitVec 2).getLsbD 1 = false := bitsToWordMiss [true] 1 ⟨by decide,by decide⟩

-- bs_snoc_3_0_2
example : bitsToWordW ([true,false,true] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 2) := bitsToWordSnoc [true,false,true] false

-- bs_value_3_0_2
example : (bitsToWordW ([true,false,true] ++ [false]) : BitVec 2).toNat = 1 := by decide

-- bs_snoc_3_1_2
example : bitsToWordW ([true,false,true] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 2) := bitsToWordSnoc [true,false,true] true

-- bs_value_3_1_2
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- bs_snoc_4_0_2
example : bitsToWordW ([false,true,false,true] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 2) := bitsToWordSnoc [false,true,false,true] false

-- bs_value_4_0_2
example : (bitsToWordW ([false,true,false,true] ++ [false]) : BitVec 2).toNat = 2 := by decide

-- bs_snoc_4_1_2
example : bitsToWordW ([false,true,false,true] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 2) := bitsToWordSnoc [false,true,false,true] true

-- bs_value_4_1_2
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 2).toNat = 2 := by decide

-- bs_snoc_5_0_2
example : bitsToWordW ([true,true,true,true] ++ [false]) = ((if false then (1:BitVec 2) else 0) <<< 4) ||| (bitsToWordW [true,true,true,true]:BitVec 2) := bitsToWordSnoc [true,true,true,true] false

-- bs_value_5_0_2
example : (bitsToWordW ([true,true,true,true] ++ [false]) : BitVec 2).toNat = 3 := by decide

-- bs_snoc_5_1_2
example : bitsToWordW ([true,true,true,true] ++ [true]) = ((if true then (1:BitVec 2) else 0) <<< 4) ||| (bitsToWordW [true,true,true,true]:BitVec 2) := bitsToWordSnoc [true,true,true,true] true

-- bs_value_5_1_2
example : (bitsToWordW ([true,true,true,true] ++ [true]) : BitVec 2).toNat = 3 := by decide

-- bs_prefix_0_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ []):BitVec 2).getLsbD i) = [] := genlistBitsToWordAlt [] [] (by decide)

-- bs_prefix_1_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]):BitVec 2).getLsbD i) = [] := genlistBitsToWordAlt [] [true] (by decide)

-- bs_prefix_2_2
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 2).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_prefix_3_2
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ []):BitVec 2).getLsbD i) = [false] := genlistBitsToWordAlt [false] [] (by decide)

-- bs_prefix_4_2
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [false]):BitVec 2).getLsbD i) = [true] := genlistBitsToWordAlt [true] [false] (by decide)

-- bs_prefix_6_2
example : (List.range 2).map (fun i => (bitsToWordW ([true,true] ++ []):BitVec 2).getLsbD i) = [true,true] := genlistBitsToWordAlt [true,true] [] (by decide)

-- bs_snoc_0_0_8
example : bitsToWordW ([] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 0) ||| (bitsToWordW []:BitVec 8) := bitsToWordSnoc [] false

-- bs_value_0_0_8
example : (bitsToWordW ([] ++ [false]) : BitVec 8).toNat = 0 := by decide

-- bs_snoc_0_1_8
example : bitsToWordW ([] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 0) ||| (bitsToWordW []:BitVec 8) := bitsToWordSnoc [] true

-- bs_value_0_1_8
example : (bitsToWordW ([] ++ [true]) : BitVec 8).toNat = 1 := by decide

-- bs_miss_0_0_8
example : (bitsToWordW []:BitVec 8).getLsbD 0 = false := bitsToWordMiss [] 0 ⟨by decide,by decide⟩

-- bs_miss_0_7_8
example : (bitsToWordW []:BitVec 8).getLsbD 7 = false := bitsToWordMiss [] 7 ⟨by decide,by decide⟩

-- bs_snoc_1_0_8
example : bitsToWordW ([false] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 8) := bitsToWordSnoc [false] false

-- bs_value_1_0_8
example : (bitsToWordW ([false] ++ [false]) : BitVec 8).toNat = 0 := by decide

-- bs_snoc_1_1_8
example : bitsToWordW ([false] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 8) := bitsToWordSnoc [false] true

-- bs_value_1_1_8
example : (bitsToWordW ([false] ++ [true]) : BitVec 8).toNat = 2 := by decide

-- bs_miss_1_1_8
example : (bitsToWordW [false]:BitVec 8).getLsbD 1 = false := bitsToWordMiss [false] 1 ⟨by decide,by decide⟩

-- bs_miss_1_7_8
example : (bitsToWordW [false]:BitVec 8).getLsbD 7 = false := bitsToWordMiss [false] 7 ⟨by decide,by decide⟩

-- bs_snoc_2_0_8
example : bitsToWordW ([true] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 8) := bitsToWordSnoc [true] false

-- bs_value_2_0_8
example : (bitsToWordW ([true] ++ [false]) : BitVec 8).toNat = 1 := by decide

-- bs_snoc_2_1_8
example : bitsToWordW ([true] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 8) := bitsToWordSnoc [true] true

-- bs_value_2_1_8
example : (bitsToWordW ([true] ++ [true]) : BitVec 8).toNat = 3 := by decide

-- bs_miss_2_1_8
example : (bitsToWordW [true]:BitVec 8).getLsbD 1 = false := bitsToWordMiss [true] 1 ⟨by decide,by decide⟩

-- bs_miss_2_7_8
example : (bitsToWordW [true]:BitVec 8).getLsbD 7 = false := bitsToWordMiss [true] 7 ⟨by decide,by decide⟩

-- bs_snoc_3_0_8
example : bitsToWordW ([true,false,true] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 8) := bitsToWordSnoc [true,false,true] false

-- bs_value_3_0_8
example : (bitsToWordW ([true,false,true] ++ [false]) : BitVec 8).toNat = 5 := by decide

-- bs_snoc_3_1_8
example : bitsToWordW ([true,false,true] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 8) := bitsToWordSnoc [true,false,true] true

-- bs_value_3_1_8
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 8).toNat = 13 := by decide

-- bs_miss_3_3_8
example : (bitsToWordW [true,false,true]:BitVec 8).getLsbD 3 = false := bitsToWordMiss [true,false,true] 3 ⟨by decide,by decide⟩

-- bs_miss_3_7_8
example : (bitsToWordW [true,false,true]:BitVec 8).getLsbD 7 = false := bitsToWordMiss [true,false,true] 7 ⟨by decide,by decide⟩

-- bs_snoc_4_0_8
example : bitsToWordW ([false,true,false,true] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 8) := bitsToWordSnoc [false,true,false,true] false

-- bs_value_4_0_8
example : (bitsToWordW ([false,true,false,true] ++ [false]) : BitVec 8).toNat = 10 := by decide

-- bs_snoc_4_1_8
example : bitsToWordW ([false,true,false,true] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 8) := bitsToWordSnoc [false,true,false,true] true

-- bs_value_4_1_8
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 8).toNat = 26 := by decide

-- bs_miss_4_4_8
example : (bitsToWordW [false,true,false,true]:BitVec 8).getLsbD 4 = false := bitsToWordMiss [false,true,false,true] 4 ⟨by decide,by decide⟩

-- bs_miss_4_7_8
example : (bitsToWordW [false,true,false,true]:BitVec 8).getLsbD 7 = false := bitsToWordMiss [false,true,false,true] 7 ⟨by decide,by decide⟩

-- bs_snoc_5_0_8
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true] ++ [false]) = ((if false then (1:BitVec 8) else 0) <<< 10) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true]:BitVec 8) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true] false

-- bs_value_5_0_8
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true] ++ [false]) : BitVec 8).toNat = 255 := by decide

-- bs_snoc_5_1_8
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true] ++ [true]) = ((if true then (1:BitVec 8) else 0) <<< 10) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true]:BitVec 8) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true] true

-- bs_value_5_1_8
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 8).toNat = 255 := by decide

-- bs_prefix_0_8
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ []):BitVec 8).getLsbD i) = [] := genlistBitsToWordAlt [] [] (by decide)

-- bs_prefix_1_8
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]):BitVec 8).getLsbD i) = [] := genlistBitsToWordAlt [] [true] (by decide)

-- bs_prefix_2_8
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 8).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_prefix_3_8
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ []):BitVec 8).getLsbD i) = [false] := genlistBitsToWordAlt [false] [] (by decide)

-- bs_prefix_4_8
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [false]):BitVec 8).getLsbD i) = [true] := genlistBitsToWordAlt [true] [false] (by decide)

-- bs_prefix_5_8
example : (List.range 2).map (fun i => (bitsToWordW ([true,false] ++ [true]):BitVec 8).getLsbD i) = [true,false] := genlistBitsToWordAlt [true,false] [true] (by decide)

-- bs_prefix_6_8
example : (List.range 8).map (fun i => (bitsToWordW ([true,true,true,true,true,true,true,true] ++ []):BitVec 8).getLsbD i) = [true,true,true,true,true,true,true,true] := genlistBitsToWordAlt [true,true,true,true,true,true,true,true] [] (by decide)

-- bs_snoc_0_0_64
example : bitsToWordW ([] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 0) ||| (bitsToWordW []:BitVec 64) := bitsToWordSnoc [] false

-- bs_value_0_0_64
example : (bitsToWordW ([] ++ [false]) : BitVec 64).toNat = 0 := by decide

-- bs_snoc_0_1_64
example : bitsToWordW ([] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 0) ||| (bitsToWordW []:BitVec 64) := bitsToWordSnoc [] true

-- bs_value_0_1_64
example : (bitsToWordW ([] ++ [true]) : BitVec 64).toNat = 1 := by decide

-- bs_miss_0_0_64
example : (bitsToWordW []:BitVec 64).getLsbD 0 = false := bitsToWordMiss [] 0 ⟨by decide,by decide⟩

-- bs_miss_0_63_64
example : (bitsToWordW []:BitVec 64).getLsbD 63 = false := bitsToWordMiss [] 63 ⟨by decide,by decide⟩

-- bs_snoc_1_0_64
example : bitsToWordW ([false] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 64) := bitsToWordSnoc [false] false

-- bs_value_1_0_64
example : (bitsToWordW ([false] ++ [false]) : BitVec 64).toNat = 0 := by decide

-- bs_snoc_1_1_64
example : bitsToWordW ([false] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 64) := bitsToWordSnoc [false] true

-- bs_value_1_1_64
example : (bitsToWordW ([false] ++ [true]) : BitVec 64).toNat = 2 := by decide

-- bs_miss_1_1_64
example : (bitsToWordW [false]:BitVec 64).getLsbD 1 = false := bitsToWordMiss [false] 1 ⟨by decide,by decide⟩

-- bs_miss_1_63_64
example : (bitsToWordW [false]:BitVec 64).getLsbD 63 = false := bitsToWordMiss [false] 63 ⟨by decide,by decide⟩

-- bs_snoc_2_0_64
example : bitsToWordW ([true] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 64) := bitsToWordSnoc [true] false

-- bs_value_2_0_64
example : (bitsToWordW ([true] ++ [false]) : BitVec 64).toNat = 1 := by decide

-- bs_snoc_2_1_64
example : bitsToWordW ([true] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 64) := bitsToWordSnoc [true] true

-- bs_value_2_1_64
example : (bitsToWordW ([true] ++ [true]) : BitVec 64).toNat = 3 := by decide

-- bs_miss_2_1_64
example : (bitsToWordW [true]:BitVec 64).getLsbD 1 = false := bitsToWordMiss [true] 1 ⟨by decide,by decide⟩

-- bs_miss_2_63_64
example : (bitsToWordW [true]:BitVec 64).getLsbD 63 = false := bitsToWordMiss [true] 63 ⟨by decide,by decide⟩

-- bs_snoc_3_0_64
example : bitsToWordW ([true,false,true] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 64) := bitsToWordSnoc [true,false,true] false

-- bs_value_3_0_64
example : (bitsToWordW ([true,false,true] ++ [false]) : BitVec 64).toNat = 5 := by decide

-- bs_snoc_3_1_64
example : bitsToWordW ([true,false,true] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 64) := bitsToWordSnoc [true,false,true] true

-- bs_value_3_1_64
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 64).toNat = 13 := by decide

-- bs_miss_3_3_64
example : (bitsToWordW [true,false,true]:BitVec 64).getLsbD 3 = false := bitsToWordMiss [true,false,true] 3 ⟨by decide,by decide⟩

-- bs_miss_3_63_64
example : (bitsToWordW [true,false,true]:BitVec 64).getLsbD 63 = false := bitsToWordMiss [true,false,true] 63 ⟨by decide,by decide⟩

-- bs_snoc_4_0_64
example : bitsToWordW ([false,true,false,true] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 64) := bitsToWordSnoc [false,true,false,true] false

-- bs_value_4_0_64
example : (bitsToWordW ([false,true,false,true] ++ [false]) : BitVec 64).toNat = 10 := by decide

-- bs_snoc_4_1_64
example : bitsToWordW ([false,true,false,true] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 64) := bitsToWordSnoc [false,true,false,true] true

-- bs_value_4_1_64
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 64).toNat = 26 := by decide

-- bs_miss_4_4_64
example : (bitsToWordW [false,true,false,true]:BitVec 64).getLsbD 4 = false := bitsToWordMiss [false,true,false,true] 4 ⟨by decide,by decide⟩

-- bs_miss_4_63_64
example : (bitsToWordW [false,true,false,true]:BitVec 64).getLsbD 63 = false := bitsToWordMiss [false,true,false,true] 63 ⟨by decide,by decide⟩

-- bs_snoc_5_0_64
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [false]) = ((if false then (1:BitVec 64) else 0) <<< 66) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]:BitVec 64) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] false

-- bs_value_5_0_64
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [false]) : BitVec 64).toNat = 18446744073709551615 := by decide

-- bs_snoc_5_1_64
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) = ((if true then (1:BitVec 64) else 0) <<< 66) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]:BitVec 64) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true

-- bs_value_5_1_64
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 64).toNat = 18446744073709551615 := by decide

-- bs_prefix_0_64
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ []):BitVec 64).getLsbD i) = [] := genlistBitsToWordAlt [] [] (by decide)

-- bs_prefix_1_64
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]):BitVec 64).getLsbD i) = [] := genlistBitsToWordAlt [] [true] (by decide)

-- bs_prefix_2_64
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 64).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_prefix_3_64
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ []):BitVec 64).getLsbD i) = [false] := genlistBitsToWordAlt [false] [] (by decide)

-- bs_prefix_4_64
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [false]):BitVec 64).getLsbD i) = [true] := genlistBitsToWordAlt [true] [false] (by decide)

-- bs_prefix_5_64
example : (List.range 2).map (fun i => (bitsToWordW ([true,false] ++ [true]):BitVec 64).getLsbD i) = [true,false] := genlistBitsToWordAlt [true,false] [true] (by decide)

-- bs_prefix_6_64
example : (List.range 64).map (fun i => (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ []):BitVec 64).getLsbD i) = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := genlistBitsToWordAlt [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] (by decide)

-- bs_snoc_0_0_80
example : bitsToWordW ([] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 0) ||| (bitsToWordW []:BitVec 80) := bitsToWordSnoc [] false

-- bs_value_0_0_80
example : (bitsToWordW ([] ++ [false]) : BitVec 80).toNat = 0 := by decide

-- bs_snoc_0_1_80
example : bitsToWordW ([] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 0) ||| (bitsToWordW []:BitVec 80) := bitsToWordSnoc [] true

-- bs_value_0_1_80
example : (bitsToWordW ([] ++ [true]) : BitVec 80).toNat = 1 := by decide

-- bs_miss_0_0_80
example : (bitsToWordW []:BitVec 80).getLsbD 0 = false := bitsToWordMiss [] 0 ⟨by decide,by decide⟩

-- bs_miss_0_79_80
example : (bitsToWordW []:BitVec 80).getLsbD 79 = false := bitsToWordMiss [] 79 ⟨by decide,by decide⟩

-- bs_snoc_1_0_80
example : bitsToWordW ([false] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 80) := bitsToWordSnoc [false] false

-- bs_value_1_0_80
example : (bitsToWordW ([false] ++ [false]) : BitVec 80).toNat = 0 := by decide

-- bs_snoc_1_1_80
example : bitsToWordW ([false] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 1) ||| (bitsToWordW [false]:BitVec 80) := bitsToWordSnoc [false] true

-- bs_value_1_1_80
example : (bitsToWordW ([false] ++ [true]) : BitVec 80).toNat = 2 := by decide

-- bs_miss_1_1_80
example : (bitsToWordW [false]:BitVec 80).getLsbD 1 = false := bitsToWordMiss [false] 1 ⟨by decide,by decide⟩

-- bs_miss_1_79_80
example : (bitsToWordW [false]:BitVec 80).getLsbD 79 = false := bitsToWordMiss [false] 79 ⟨by decide,by decide⟩

-- bs_snoc_2_0_80
example : bitsToWordW ([true] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 80) := bitsToWordSnoc [true] false

-- bs_value_2_0_80
example : (bitsToWordW ([true] ++ [false]) : BitVec 80).toNat = 1 := by decide

-- bs_snoc_2_1_80
example : bitsToWordW ([true] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 1) ||| (bitsToWordW [true]:BitVec 80) := bitsToWordSnoc [true] true

-- bs_value_2_1_80
example : (bitsToWordW ([true] ++ [true]) : BitVec 80).toNat = 3 := by decide

-- bs_miss_2_1_80
example : (bitsToWordW [true]:BitVec 80).getLsbD 1 = false := bitsToWordMiss [true] 1 ⟨by decide,by decide⟩

-- bs_miss_2_79_80
example : (bitsToWordW [true]:BitVec 80).getLsbD 79 = false := bitsToWordMiss [true] 79 ⟨by decide,by decide⟩

-- bs_snoc_3_0_80
example : bitsToWordW ([true,false,true] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 80) := bitsToWordSnoc [true,false,true] false

-- bs_value_3_0_80
example : (bitsToWordW ([true,false,true] ++ [false]) : BitVec 80).toNat = 5 := by decide

-- bs_snoc_3_1_80
example : bitsToWordW ([true,false,true] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 3) ||| (bitsToWordW [true,false,true]:BitVec 80) := bitsToWordSnoc [true,false,true] true

-- bs_value_3_1_80
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 80).toNat = 13 := by decide

-- bs_miss_3_3_80
example : (bitsToWordW [true,false,true]:BitVec 80).getLsbD 3 = false := bitsToWordMiss [true,false,true] 3 ⟨by decide,by decide⟩

-- bs_miss_3_79_80
example : (bitsToWordW [true,false,true]:BitVec 80).getLsbD 79 = false := bitsToWordMiss [true,false,true] 79 ⟨by decide,by decide⟩

-- bs_snoc_4_0_80
example : bitsToWordW ([false,true,false,true] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 80) := bitsToWordSnoc [false,true,false,true] false

-- bs_value_4_0_80
example : (bitsToWordW ([false,true,false,true] ++ [false]) : BitVec 80).toNat = 10 := by decide

-- bs_snoc_4_1_80
example : bitsToWordW ([false,true,false,true] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 4) ||| (bitsToWordW [false,true,false,true]:BitVec 80) := bitsToWordSnoc [false,true,false,true] true

-- bs_value_4_1_80
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 80).toNat = 26 := by decide

-- bs_miss_4_4_80
example : (bitsToWordW [false,true,false,true]:BitVec 80).getLsbD 4 = false := bitsToWordMiss [false,true,false,true] 4 ⟨by decide,by decide⟩

-- bs_miss_4_79_80
example : (bitsToWordW [false,true,false,true]:BitVec 80).getLsbD 79 = false := bitsToWordMiss [false,true,false,true] 79 ⟨by decide,by decide⟩

-- bs_snoc_5_0_80
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [false]) = ((if false then (1:BitVec 80) else 0) <<< 82) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]:BitVec 80) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] false

-- bs_value_5_0_80
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [false]) : BitVec 80).toNat = 1208925819614629174706175 := by decide

-- bs_snoc_5_1_80
example : bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) = ((if true then (1:BitVec 80) else 0) <<< 82) ||| (bitsToWordW [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]:BitVec 80) := bitsToWordSnoc [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] true

-- bs_value_5_1_80
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 80).toNat = 1208925819614629174706175 := by decide

-- bs_prefix_0_80
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ []):BitVec 80).getLsbD i) = [] := genlistBitsToWordAlt [] [] (by decide)

-- bs_prefix_1_80
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]):BitVec 80).getLsbD i) = [] := genlistBitsToWordAlt [] [true] (by decide)

-- bs_prefix_2_80
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ []):BitVec 80).getLsbD i) = [true] := genlistBitsToWordAlt [true] [] (by decide)

-- bs_prefix_3_80
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ []):BitVec 80).getLsbD i) = [false] := genlistBitsToWordAlt [false] [] (by decide)

-- bs_prefix_4_80
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [false]):BitVec 80).getLsbD i) = [true] := genlistBitsToWordAlt [true] [false] (by decide)

-- bs_prefix_5_80
example : (List.range 2).map (fun i => (bitsToWordW ([true,false] ++ [true]):BitVec 80).getLsbD i) = [true,false] := genlistBitsToWordAlt [true,false] [true] (by decide)

-- bs_prefix_6_80
example : (List.range 80).map (fun i => (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ []):BitVec 80).getLsbD i) = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := genlistBitsToWordAlt [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] (by decide)

example {width : Nat} [NeZero width] (xs ys : List Bool) (h : (xs ++ ys).length ≤ width) :
    (List.range xs.length).map (fun i => (bitsToWordW (xs ++ ys):BitVec width).getLsbD i) = xs := genlistBitsToWordAlt xs ys h
example {width : Nat} [NeZero width] (xs : List Bool) (b : Bool) :
    bitsToWordW (xs ++ [b]) = ((if b then (1:BitVec width) else 0) <<< xs.length) ||| bitsToWordW xs := bitsToWordSnoc xs b
