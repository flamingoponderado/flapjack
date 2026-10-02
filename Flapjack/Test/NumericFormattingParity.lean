import Flapjack.Misc.Words.Formatting

set_option maxRecDepth 10000

namespace Flapjack.Test
open Flapjack
-- Original oracle digits_0_0
example : holN2l 0 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_0_1
example : holN2l 0 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_0_37
example : holN2l 0 37 = [37] := by
  simp [holN2l]
-- Original oracle digits_0_123456
example : holN2l 0 123456 = [123456] := by
  simp [holN2l]
-- Original oracle digits_1_0
example : holN2l 1 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_1_1
example : holN2l 1 1 = [0] := by
  simp [holN2l]
-- Original oracle digits_1_37
example : holN2l 1 37 = [0] := by
  simp [holN2l]
-- Original oracle digits_1_123456
example : holN2l 1 123456 = [0] := by
  simp [holN2l]
-- Original oracle digits_2_0
example : holN2l 2 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_2_1
example : holN2l 2 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_2_37
example : holN2l 2 37 = [1, 0, 1, 0, 0, 1] := by
  simp [holN2l]
-- Original oracle digits_2_123456
example : holN2l 2 123456 = [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1] := by
  simp [holN2l]
-- Original oracle digits_3_0
example : holN2l 3 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_3_1
example : holN2l 3 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_3_37
example : holN2l 3 37 = [1, 0, 1, 1] := by
  simp [holN2l]
-- Original oracle digits_3_123456
example : holN2l 3 123456 = [0, 1, 1, 0, 0, 1, 1, 2, 0, 0, 2] := by
  simp [holN2l]
-- Original oracle digits_10_0
example : holN2l 10 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_10_1
example : holN2l 10 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_10_37
example : holN2l 10 37 = [7, 3] := by
  simp [holN2l]
-- Original oracle digits_10_123456
example : holN2l 10 123456 = [6, 5, 4, 3, 2, 1] := by
  simp [holN2l]
-- Original oracle digits_16_0
example : holN2l 16 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_16_1
example : holN2l 16 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_16_37
example : holN2l 16 37 = [5, 2] := by
  simp [holN2l]
-- Original oracle digits_16_123456
example : holN2l 16 123456 = [0, 4, 2, 14, 1] := by
  simp [holN2l]
-- Original oracle digits_37_0
example : holN2l 37 0 = [0] := by
  simp [holN2l]
-- Original oracle digits_37_1
example : holN2l 37 1 = [1] := by
  simp [holN2l]
-- Original oracle digits_37_37
example : holN2l 37 37 = [0, 1] := by
  simp [holN2l]
-- Original oracle digits_37_123456
example : holN2l 37 123456 = [24, 6, 16, 2] := by
  simp [holN2l]
-- Original oracle hex_0
example : (holHex 0).toNat = 48 := by
  decide
-- Original oracle hex_1
example : (holHex 1).toNat = 49 := by
  decide
-- Original oracle hex_2
example : (holHex 2).toNat = 50 := by
  decide
-- Original oracle hex_3
example : (holHex 3).toNat = 51 := by
  decide
-- Original oracle hex_4
example : (holHex 4).toNat = 52 := by
  decide
-- Original oracle hex_5
example : (holHex 5).toNat = 53 := by
  decide
-- Original oracle hex_6
example : (holHex 6).toNat = 54 := by
  decide
-- Original oracle hex_7
example : (holHex 7).toNat = 55 := by
  decide
-- Original oracle hex_8
example : (holHex 8).toNat = 56 := by
  decide
-- Original oracle hex_9
example : (holHex 9).toNat = 57 := by
  decide
-- Original oracle hex_10
example : (holHex 10).toNat = 65 := by
  decide
-- Original oracle hex_11
example : (holHex 11).toNat = 66 := by
  decide
-- Original oracle hex_12
example : (holHex 12).toNat = 67 := by
  decide
-- Original oracle hex_13
example : (holHex 13).toNat = 68 := by
  decide
-- Original oracle hex_14
example : (holHex 14).toNat = 69 := by
  decide
-- Original oracle hex_15
example : (holHex 15).toNat = 70 := by
  decide
-- Original oracle hex_16
example : (holHex 16).toNat = 0 := by
  decide
-- Original oracle hex_17
example : (holHex 17).toNat = 0 := by
  decide
-- Original oracle hex_999
example : (holHex 999).toNat = 0 := by
  decide
-- Original oracle custom_0
example : (holN2s 0 (fun x => BitVec.ofNat 8 (x+17)) 37).map BitVec.toNat = [54] := by
  simp [holN2s, holN2l] <;> decide
-- Original oracle custom_1
example : (holN2s 1 (fun x => BitVec.ofNat 8 (x+17)) 37).map BitVec.toNat = [17] := by
  simp [holN2s, holN2l] <;> decide
-- Original oracle custom_3
example : (holN2s 3 (fun x => BitVec.ofNat 8 (x+17)) 123456).map BitVec.toNat = [19, 17, 17, 19, 18, 18, 17, 17, 18, 18, 17] := by
  simp [holN2s, holN2l] <;> decide
-- Original oracle custom_17
example : (holN2s 17 (fun x => BitVec.ofNat 8 (x+17)) 123456).map BitVec.toNat = [18, 25, 19, 20, 19] := by
  simp [holN2s, holN2l] <;> decide
-- Original oracle decimal_0
example : (holNumToDecString 0).map BitVec.toNat = [48] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_1
example : (holNumToDecString 1).map BitVec.toNat = [49] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_9
example : (holNumToDecString 9).map BitVec.toNat = [57] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_10
example : (holNumToDecString 10).map BitVec.toNat = [49, 48] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_999
example : (holNumToDecString 999).map BitVec.toNat = [57, 57, 57] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_18446744073709551615
example : (holNumToDecString 18446744073709551615).map BitVec.toNat = [49, 56, 52, 52, 54, 55, 52, 52, 48, 55, 51, 55, 48, 57, 53, 53, 49, 54, 49, 53] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle decimal_1329227995784915872903807060280344699
example : (holNumToDecString 1329227995784915872903807060280344699).map BitVec.toNat = [49, 51, 50, 57, 50, 50, 55, 57, 57, 53, 55, 56, 52, 57, 49, 53, 56, 55, 50, 57, 48, 51, 56, 48, 55, 48, 54, 48, 50, 56, 48, 51, 52, 52, 54, 57, 57] := by
  simp [holNumToDecString, holN2s, holN2l] <;> decide
-- Original oracle word_base_0
example : (holW2s 0 holHex (37 : BitVec 8)).map BitVec.toNat = [0] := by
  simp [holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_base_1
example : (holW2s 1 holHex (37 : BitVec 8)).map BitVec.toNat = [48] := by
  simp [holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_base_2
example : (holW2s 2 holHex (12345 : BitVec 16)).map BitVec.toNat = [49, 49, 48, 48, 48, 48, 48, 48, 49, 49, 49, 48, 48, 49] := by
  simp [holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_base_3
example : (holW2s 16 holHex (604462909807314587353089 : BitVec 80)).map BitVec.toNat = [56, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49] := by
  simp [holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_0
example : (holWordToHexString (0 : BitVec 1)).map BitVec.toNat = [48] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_1
example : (holWordToHexString (3 : BitVec 1)).map BitVec.toNat = [49] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_2
example : (holWordToHexString (255 : BitVec 7)).map BitVec.toNat = [55, 70] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_3
example : (holWordToHexString (165 : BitVec 8)).map BitVec.toNat = [65, 53] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_4
example : (holWordToHexString (4660 : BitVec 16)).map BitVec.toNat = [49, 50, 51, 52] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_5
example : (holWordToHexString (18446744073709551615 : BitVec 64)).map BitVec.toNat = [70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_6
example : (holWordToHexString (604462909807314587353089 : BitVec 80)).map BitVec.toNat = [56, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 49] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide
-- Original oracle word_hex_7
example : (holWordToHexString (1267650600228229401496703205499 : BitVec 80)).map BitVec.toNat = [55, 66] := by
  simp [holWordToHexString, holW2s, holN2s, holN2l] <;> decide

end Flapjack.Test
