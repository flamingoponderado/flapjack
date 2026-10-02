import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapSentinelLength
open Flapjack.Compiler.Backend.WordToStack
set_option maxRecDepth 4096

-- sl_length_0_2
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 2) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_0_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 2).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_0_2
example : (bitsToWordW ([] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- sl_length_5_2
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 2) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_5_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 2).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_5_2
example : (bitsToWordW ([] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- sl_length_6_2
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 2) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_6_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 2).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_6_2
example : (bitsToWordW ([] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- sl_length_7_2
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 2) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_7_2
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 2).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_7_2
example : (bitsToWordW ([] ++ [true]) : BitVec 2).toNat = 1 := by decide

-- sl_length_0_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 8) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_0_8
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 8).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_0_8
example : (bitsToWordW ([] ++ [true]) : BitVec 8).toNat = 1 := by decide

-- sl_length_1_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([false] ++ [true]) : BitVec 8) = 2 := bitLengthBitsToWord [false] (by decide)

-- sl_prefix_1_8
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ [true]) : BitVec 8).getLsbD i) = [false] := genlistBitsToWord [false] (by decide)

-- sl_value_1_8
example : (bitsToWordW ([false] ++ [true]) : BitVec 8).toNat = 2 := by decide

-- sl_length_2_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([true] ++ [true]) : BitVec 8) = 2 := bitLengthBitsToWord [true] (by decide)

-- sl_prefix_2_8
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [true]) : BitVec 8).getLsbD i) = [true] := genlistBitsToWord [true] (by decide)

-- sl_value_2_8
example : (bitsToWordW ([true] ++ [true]) : BitVec 8).toNat = 3 := by decide

-- sl_length_3_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true] ++ [true]) : BitVec 8) = 4 := bitLengthBitsToWord [true,false,true] (by decide)

-- sl_prefix_3_8
example : (List.range 3).map (fun i => (bitsToWordW ([true,false,true] ++ [true]) : BitVec 8).getLsbD i) = [true,false,true] := genlistBitsToWord [true,false,true] (by decide)

-- sl_value_3_8
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 8).toNat = 13 := by decide

-- sl_length_4_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 8) = 5 := bitLengthBitsToWord [false,true,false,true] (by decide)

-- sl_prefix_4_8
example : (List.range 4).map (fun i => (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 8).getLsbD i) = [false,true,false,true] := genlistBitsToWord [false,true,false,true] (by decide)

-- sl_value_4_8
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 8).toNat = 26 := by decide

-- sl_length_5_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,false,false,false,false,false] ++ [true]) : BitVec 8) = 7 := bitLengthBitsToWord [false,false,false,false,false,false] (by decide)

-- sl_prefix_5_8
example : (List.range 6).map (fun i => (bitsToWordW ([false,false,false,false,false,false] ++ [true]) : BitVec 8).getLsbD i) = [false,false,false,false,false,false] := genlistBitsToWord [false,false,false,false,false,false] (by decide)

-- sl_value_5_8
example : (bitsToWordW ([false,false,false,false,false,false] ++ [true]) : BitVec 8).toNat = 64 := by decide

-- sl_length_6_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,true,true,true,true,true] ++ [true]) : BitVec 8) = 7 := bitLengthBitsToWord [true,true,true,true,true,true] (by decide)

-- sl_prefix_6_8
example : (List.range 6).map (fun i => (bitsToWordW ([true,true,true,true,true,true] ++ [true]) : BitVec 8).getLsbD i) = [true,true,true,true,true,true] := genlistBitsToWord [true,true,true,true,true,true] (by decide)

-- sl_value_6_8
example : (bitsToWordW ([true,true,true,true,true,true] ++ [true]) : BitVec 8).toNat = 127 := by decide

-- sl_length_7_8
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true,false,true,false] ++ [true]) : BitVec 8) = 7 := bitLengthBitsToWord [true,false,true,false,true,false] (by decide)

-- sl_prefix_7_8
example : (List.range 6).map (fun i => (bitsToWordW ([true,false,true,false,true,false] ++ [true]) : BitVec 8).getLsbD i) = [true,false,true,false,true,false] := genlistBitsToWord [true,false,true,false,true,false] (by decide)

-- sl_value_7_8
example : (bitsToWordW ([true,false,true,false,true,false] ++ [true]) : BitVec 8).toNat = 85 := by decide

-- sl_length_0_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 64) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_0_64
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 64).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_0_64
example : (bitsToWordW ([] ++ [true]) : BitVec 64).toNat = 1 := by decide

-- sl_length_1_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([false] ++ [true]) : BitVec 64) = 2 := bitLengthBitsToWord [false] (by decide)

-- sl_prefix_1_64
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ [true]) : BitVec 64).getLsbD i) = [false] := genlistBitsToWord [false] (by decide)

-- sl_value_1_64
example : (bitsToWordW ([false] ++ [true]) : BitVec 64).toNat = 2 := by decide

-- sl_length_2_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([true] ++ [true]) : BitVec 64) = 2 := bitLengthBitsToWord [true] (by decide)

-- sl_prefix_2_64
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [true]) : BitVec 64).getLsbD i) = [true] := genlistBitsToWord [true] (by decide)

-- sl_value_2_64
example : (bitsToWordW ([true] ++ [true]) : BitVec 64).toNat = 3 := by decide

-- sl_length_3_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true] ++ [true]) : BitVec 64) = 4 := bitLengthBitsToWord [true,false,true] (by decide)

-- sl_prefix_3_64
example : (List.range 3).map (fun i => (bitsToWordW ([true,false,true] ++ [true]) : BitVec 64).getLsbD i) = [true,false,true] := genlistBitsToWord [true,false,true] (by decide)

-- sl_value_3_64
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 64).toNat = 13 := by decide

-- sl_length_4_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 64) = 5 := bitLengthBitsToWord [false,true,false,true] (by decide)

-- sl_prefix_4_64
example : (List.range 4).map (fun i => (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 64).getLsbD i) = [false,true,false,true] := genlistBitsToWord [false,true,false,true] (by decide)

-- sl_value_4_64
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 64).toNat = 26 := by decide

-- sl_length_5_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 64) = 63 := bitLengthBitsToWord [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] (by decide)

-- sl_prefix_5_64
example : (List.range 62).map (fun i => (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 64).getLsbD i) = [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := genlistBitsToWord [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] (by decide)

-- sl_value_5_64
example : (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 64).toNat = 4611686018427387904 := by decide

-- sl_length_6_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 64) = 63 := bitLengthBitsToWord [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (by decide)

-- sl_prefix_6_64
example : (List.range 62).map (fun i => (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 64).getLsbD i) = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := genlistBitsToWord [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (by decide)

-- sl_value_6_64
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 64).toNat = 9223372036854775807 := by decide

-- sl_length_7_64
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 64) = 63 := bitLengthBitsToWord [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (by decide)

-- sl_prefix_7_64
example : (List.range 62).map (fun i => (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 64).getLsbD i) = [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] := genlistBitsToWord [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (by decide)

-- sl_value_7_64
example : (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 64).toNat = 6148914691236517205 := by decide

-- sl_length_0_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([] ++ [true]) : BitVec 80) = 1 := bitLengthBitsToWord [] (by decide)

-- sl_prefix_0_80
example : (List.range 0).map (fun i => (bitsToWordW ([] ++ [true]) : BitVec 80).getLsbD i) = [] := genlistBitsToWord [] (by decide)

-- sl_value_0_80
example : (bitsToWordW ([] ++ [true]) : BitVec 80).toNat = 1 := by decide

-- sl_length_1_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([false] ++ [true]) : BitVec 80) = 2 := bitLengthBitsToWord [false] (by decide)

-- sl_prefix_1_80
example : (List.range 1).map (fun i => (bitsToWordW ([false] ++ [true]) : BitVec 80).getLsbD i) = [false] := genlistBitsToWord [false] (by decide)

-- sl_value_1_80
example : (bitsToWordW ([false] ++ [true]) : BitVec 80).toNat = 2 := by decide

-- sl_length_2_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([true] ++ [true]) : BitVec 80) = 2 := bitLengthBitsToWord [true] (by decide)

-- sl_prefix_2_80
example : (List.range 1).map (fun i => (bitsToWordW ([true] ++ [true]) : BitVec 80).getLsbD i) = [true] := genlistBitsToWord [true] (by decide)

-- sl_value_2_80
example : (bitsToWordW ([true] ++ [true]) : BitVec 80).toNat = 3 := by decide

-- sl_length_3_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true] ++ [true]) : BitVec 80) = 4 := bitLengthBitsToWord [true,false,true] (by decide)

-- sl_prefix_3_80
example : (List.range 3).map (fun i => (bitsToWordW ([true,false,true] ++ [true]) : BitVec 80).getLsbD i) = [true,false,true] := genlistBitsToWord [true,false,true] (by decide)

-- sl_value_3_80
example : (bitsToWordW ([true,false,true] ++ [true]) : BitVec 80).toNat = 13 := by decide

-- sl_length_4_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 80) = 5 := bitLengthBitsToWord [false,true,false,true] (by decide)

-- sl_prefix_4_80
example : (List.range 4).map (fun i => (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 80).getLsbD i) = [false,true,false,true] := genlistBitsToWord [false,true,false,true] (by decide)

-- sl_value_4_80
example : (bitsToWordW ([false,true,false,true] ++ [true]) : BitVec 80).toNat = 26 := by decide

-- sl_length_5_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 80) = 79 := bitLengthBitsToWord [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] (by decide)

-- sl_prefix_5_80
example : (List.range 78).map (fun i => (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 80).getLsbD i) = [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] := genlistBitsToWord [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] (by decide)

-- sl_value_5_80
example : (bitsToWordW ([false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] ++ [true]) : BitVec 80).toNat = 302231454903657293676544 := by decide

-- sl_length_6_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 80) = 79 := bitLengthBitsToWord [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (by decide)

-- sl_prefix_6_80
example : (List.range 78).map (fun i => (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 80).getLsbD i) = [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] := genlistBitsToWord [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] (by decide)

-- sl_value_6_80
example : (bitsToWordW ([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ [true]) : BitVec 80).toNat = 604462909807314587353087 := by decide

-- sl_length_7_80
example : Flapjack.StackSem.bitLength (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 80) = 79 := bitLengthBitsToWord [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (by decide)

-- sl_prefix_7_80
example : (List.range 78).map (fun i => (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 80).getLsbD i) = [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] := genlistBitsToWord [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] (by decide)

-- sl_value_7_80
example : (bitsToWordW ([true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ [true]) : BitVec 80).toNat = 402975273204876391568725 := by decide

example {width : Nat} [NeZero width] (bits : List Bool) (h : bits.length+1<width) := bitLengthBitsToWord (width := width) bits h
example {width : Nat} [NeZero width] (bits : List Bool) (h : bits.length+1<width) := genlistBitsToWord (width := width) bits h
