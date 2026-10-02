import Flapjack.Compiler.Backend.WordToStack.Proofs.WordExtraction

namespace Flapjack.Test.WordToStackWordExtractionParity
open Flapjack Flapjack.WordToStackProofs

-- extract_w1_0: independently decoded original complete output.
example : (theWords (width := 1) []).map (List.map BitVec.toNat) = some [] := by rfl

-- extract_w1_1: independently decoded original complete output.
example : (theWords (width := 1) [none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_2: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0)]).map (List.map BitVec.toNat) = some [0] := by rfl

-- extract_w1_3: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1)]).map (List.map BitVec.toNat) = some [1] := by rfl

-- extract_w1_4: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_5: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1] := by rfl

-- extract_w1_6: independently decoded original complete output.
example : (theWords (width := 1) [none,none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_7: independently decoded original complete output.
example : (theWords (width := 1) [none,some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_8: independently decoded original complete output.
example : (theWords (width := 1) [none,some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_9: independently decoded original complete output.
example : (theWords (width := 1) [none,some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_10: independently decoded original complete output.
example : (theWords (width := 1) [none,some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_11: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_12: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0] := by rfl

-- extract_w1_13: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),some (.word 1)]).map (List.map BitVec.toNat) = some [0,1] := by rfl

-- extract_w1_14: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_15: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [0,1] := by rfl

-- extract_w1_16: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_17: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),some (.word 0)]).map (List.map BitVec.toNat) = some [1,0] := by rfl

-- extract_w1_18: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),some (.word 1)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w1_19: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_20: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w1_21: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_22: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5),some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_23: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5),some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_24: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_25: independently decoded original complete output.
example : (theWords (width := 1) [some (.loc 3 5),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_26: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_27: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427),some (.word 0)]).map (List.map BitVec.toNat) = some [1,0] := by rfl

-- extract_w1_28: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427),some (.word 1)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w1_29: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_30: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w1_31: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by rfl

-- extract_w1_32: independently decoded original complete output.
example : (theWords (width := 1) [some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w1_33: independently decoded original complete output.
example : (theWords (width := 1) [none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_0: independently decoded original complete output.
example : (theWords (width := 8) []).map (List.map BitVec.toNat) = some [] := by rfl

-- extract_w8_1: independently decoded original complete output.
example : (theWords (width := 8) [none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_2: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0)]).map (List.map BitVec.toNat) = some [0] := by rfl

-- extract_w8_3: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1)]).map (List.map BitVec.toNat) = some [1] := by rfl

-- extract_w8_4: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_5: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [3] := by rfl

-- extract_w8_6: independently decoded original complete output.
example : (theWords (width := 8) [none,none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_7: independently decoded original complete output.
example : (theWords (width := 8) [none,some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_8: independently decoded original complete output.
example : (theWords (width := 8) [none,some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_9: independently decoded original complete output.
example : (theWords (width := 8) [none,some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_10: independently decoded original complete output.
example : (theWords (width := 8) [none,some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_11: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_12: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0] := by rfl

-- extract_w8_13: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),some (.word 1)]).map (List.map BitVec.toNat) = some [0,1] := by rfl

-- extract_w8_14: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_15: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [0,3] := by rfl

-- extract_w8_16: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_17: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),some (.word 0)]).map (List.map BitVec.toNat) = some [1,0] := by rfl

-- extract_w8_18: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),some (.word 1)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w8_19: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_20: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1,3] := by rfl

-- extract_w8_21: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_22: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5),some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_23: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5),some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_24: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_25: independently decoded original complete output.
example : (theWords (width := 8) [some (.loc 3 5),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_26: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_27: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427),some (.word 0)]).map (List.map BitVec.toNat) = some [3,0] := by rfl

-- extract_w8_28: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427),some (.word 1)]).map (List.map BitVec.toNat) = some [3,1] := by rfl

-- extract_w8_29: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_30: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [3,3] := by rfl

-- extract_w8_31: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by rfl

-- extract_w8_32: independently decoded original complete output.
example : (theWords (width := 8) [some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w8_33: independently decoded original complete output.
example : (theWords (width := 8) [none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_0: independently decoded original complete output.
example : (theWords (width := 64) []).map (List.map BitVec.toNat) = some [] := by rfl

-- extract_w64_1: independently decoded original complete output.
example : (theWords (width := 64) [none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_2: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0)]).map (List.map BitVec.toNat) = some [0] := by rfl

-- extract_w64_3: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1)]).map (List.map BitVec.toNat) = some [1] := by rfl

-- extract_w64_4: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_5: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [3] := by rfl

-- extract_w64_6: independently decoded original complete output.
example : (theWords (width := 64) [none,none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_7: independently decoded original complete output.
example : (theWords (width := 64) [none,some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_8: independently decoded original complete output.
example : (theWords (width := 64) [none,some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_9: independently decoded original complete output.
example : (theWords (width := 64) [none,some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_10: independently decoded original complete output.
example : (theWords (width := 64) [none,some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_11: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_12: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0] := by rfl

-- extract_w64_13: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),some (.word 1)]).map (List.map BitVec.toNat) = some [0,1] := by rfl

-- extract_w64_14: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_15: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [0,3] := by rfl

-- extract_w64_16: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_17: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),some (.word 0)]).map (List.map BitVec.toNat) = some [1,0] := by rfl

-- extract_w64_18: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),some (.word 1)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w64_19: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_20: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1,3] := by rfl

-- extract_w64_21: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_22: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5),some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_23: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5),some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_24: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_25: independently decoded original complete output.
example : (theWords (width := 64) [some (.loc 3 5),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_26: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_27: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427),some (.word 0)]).map (List.map BitVec.toNat) = some [3,0] := by rfl

-- extract_w64_28: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427),some (.word 1)]).map (List.map BitVec.toNat) = some [3,1] := by rfl

-- extract_w64_29: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_30: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [3,3] := by rfl

-- extract_w64_31: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by rfl

-- extract_w64_32: independently decoded original complete output.
example : (theWords (width := 64) [some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w64_33: independently decoded original complete output.
example : (theWords (width := 64) [none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_0: independently decoded original complete output.
example : (theWords (width := 80) []).map (List.map BitVec.toNat) = some [] := by rfl

-- extract_w80_1: independently decoded original complete output.
example : (theWords (width := 80) [none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_2: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0)]).map (List.map BitVec.toNat) = some [0] := by rfl

-- extract_w80_3: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1)]).map (List.map BitVec.toNat) = some [1] := by rfl

-- extract_w80_4: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_5: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1180591620717411303427] := by rfl

-- extract_w80_6: independently decoded original complete output.
example : (theWords (width := 80) [none,none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_7: independently decoded original complete output.
example : (theWords (width := 80) [none,some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_8: independently decoded original complete output.
example : (theWords (width := 80) [none,some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_9: independently decoded original complete output.
example : (theWords (width := 80) [none,some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_10: independently decoded original complete output.
example : (theWords (width := 80) [none,some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_11: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_12: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0] := by rfl

-- extract_w80_13: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),some (.word 1)]).map (List.map BitVec.toNat) = some [0,1] := by rfl

-- extract_w80_14: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_15: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [0,1180591620717411303427] := by rfl

-- extract_w80_16: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_17: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),some (.word 0)]).map (List.map BitVec.toNat) = some [1,0] := by rfl

-- extract_w80_18: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),some (.word 1)]).map (List.map BitVec.toNat) = some [1,1] := by rfl

-- extract_w80_19: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_20: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1,1180591620717411303427] := by rfl

-- extract_w80_21: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_22: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5),some (.word 0)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_23: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5),some (.word 1)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_24: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_25: independently decoded original complete output.
example : (theWords (width := 80) [some (.loc 3 5),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_26: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427),none]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_27: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427),some (.word 0)]).map (List.map BitVec.toNat) = some [1180591620717411303427,0] := by rfl

-- extract_w80_28: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427),some (.word 1)]).map (List.map BitVec.toNat) = some [1180591620717411303427,1] := by rfl

-- extract_w80_29: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_30: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = some [1180591620717411303427,1180591620717411303427] := by rfl

-- extract_w80_31: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)]).map (List.map BitVec.toNat) = some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by rfl

-- extract_w80_32: independently decoded original complete output.
example : (theWords (width := 80) [some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)]).map (List.map BitVec.toNat) = none := by rfl

-- extract_w80_33: independently decoded original complete output.
example : (theWords (width := 80) [none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)]).map (List.map BitVec.toNat) = none := by rfl

private def captures1 : List (List (Option (WordLocW 1)) × Option (List Nat)) := [
  ([],some []),
  ([none],none),
  ([some (.word 0)],some [0]),
  ([some (.word 1)],some [1]),
  ([some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427)],some [1]),
  ([none,none],none),
  ([none,some (.word 0)],none),
  ([none,some (.word 1)],none),
  ([none,some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427)],none),
  ([some (.word 0),none],none),
  ([some (.word 0),some (.word 0)],some [0,0]),
  ([some (.word 0),some (.word 1)],some [0,1]),
  ([some (.word 0),some (.loc 3 5)],none),
  ([some (.word 0),some (.word 1180591620717411303427)],some [0,1]),
  ([some (.word 1),none],none),
  ([some (.word 1),some (.word 0)],some [1,0]),
  ([some (.word 1),some (.word 1)],some [1,1]),
  ([some (.word 1),some (.loc 3 5)],none),
  ([some (.word 1),some (.word 1180591620717411303427)],some [1,1]),
  ([some (.loc 3 5),none],none),
  ([some (.loc 3 5),some (.word 0)],none),
  ([some (.loc 3 5),some (.word 1)],none),
  ([some (.loc 3 5),some (.loc 3 5)],none),
  ([some (.loc 3 5),some (.word 1180591620717411303427)],none),
  ([some (.word 1180591620717411303427),none],none),
  ([some (.word 1180591620717411303427),some (.word 0)],some [1,0]),
  ([some (.word 1180591620717411303427),some (.word 1)],some [1,1]),
  ([some (.word 1180591620717411303427),some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427),some (.word 1180591620717411303427)],some [1,1]),
  ([some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)],some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
  ([some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)],none)]

private def captures8 : List (List (Option (WordLocW 8)) × Option (List Nat)) := [
  ([],some []),
  ([none],none),
  ([some (.word 0)],some [0]),
  ([some (.word 1)],some [1]),
  ([some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427)],some [3]),
  ([none,none],none),
  ([none,some (.word 0)],none),
  ([none,some (.word 1)],none),
  ([none,some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427)],none),
  ([some (.word 0),none],none),
  ([some (.word 0),some (.word 0)],some [0,0]),
  ([some (.word 0),some (.word 1)],some [0,1]),
  ([some (.word 0),some (.loc 3 5)],none),
  ([some (.word 0),some (.word 1180591620717411303427)],some [0,3]),
  ([some (.word 1),none],none),
  ([some (.word 1),some (.word 0)],some [1,0]),
  ([some (.word 1),some (.word 1)],some [1,1]),
  ([some (.word 1),some (.loc 3 5)],none),
  ([some (.word 1),some (.word 1180591620717411303427)],some [1,3]),
  ([some (.loc 3 5),none],none),
  ([some (.loc 3 5),some (.word 0)],none),
  ([some (.loc 3 5),some (.word 1)],none),
  ([some (.loc 3 5),some (.loc 3 5)],none),
  ([some (.loc 3 5),some (.word 1180591620717411303427)],none),
  ([some (.word 1180591620717411303427),none],none),
  ([some (.word 1180591620717411303427),some (.word 0)],some [3,0]),
  ([some (.word 1180591620717411303427),some (.word 1)],some [3,1]),
  ([some (.word 1180591620717411303427),some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427),some (.word 1180591620717411303427)],some [3,3]),
  ([some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)],some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
  ([some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)],none)]

private def captures64 : List (List (Option (WordLocW 64)) × Option (List Nat)) := [
  ([],some []),
  ([none],none),
  ([some (.word 0)],some [0]),
  ([some (.word 1)],some [1]),
  ([some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427)],some [3]),
  ([none,none],none),
  ([none,some (.word 0)],none),
  ([none,some (.word 1)],none),
  ([none,some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427)],none),
  ([some (.word 0),none],none),
  ([some (.word 0),some (.word 0)],some [0,0]),
  ([some (.word 0),some (.word 1)],some [0,1]),
  ([some (.word 0),some (.loc 3 5)],none),
  ([some (.word 0),some (.word 1180591620717411303427)],some [0,3]),
  ([some (.word 1),none],none),
  ([some (.word 1),some (.word 0)],some [1,0]),
  ([some (.word 1),some (.word 1)],some [1,1]),
  ([some (.word 1),some (.loc 3 5)],none),
  ([some (.word 1),some (.word 1180591620717411303427)],some [1,3]),
  ([some (.loc 3 5),none],none),
  ([some (.loc 3 5),some (.word 0)],none),
  ([some (.loc 3 5),some (.word 1)],none),
  ([some (.loc 3 5),some (.loc 3 5)],none),
  ([some (.loc 3 5),some (.word 1180591620717411303427)],none),
  ([some (.word 1180591620717411303427),none],none),
  ([some (.word 1180591620717411303427),some (.word 0)],some [3,0]),
  ([some (.word 1180591620717411303427),some (.word 1)],some [3,1]),
  ([some (.word 1180591620717411303427),some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427),some (.word 1180591620717411303427)],some [3,3]),
  ([some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)],some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
  ([some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)],none)]

private def captures80 : List (List (Option (WordLocW 80)) × Option (List Nat)) := [
  ([],some []),
  ([none],none),
  ([some (.word 0)],some [0]),
  ([some (.word 1)],some [1]),
  ([some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427)],some [1180591620717411303427]),
  ([none,none],none),
  ([none,some (.word 0)],none),
  ([none,some (.word 1)],none),
  ([none,some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427)],none),
  ([some (.word 0),none],none),
  ([some (.word 0),some (.word 0)],some [0,0]),
  ([some (.word 0),some (.word 1)],some [0,1]),
  ([some (.word 0),some (.loc 3 5)],none),
  ([some (.word 0),some (.word 1180591620717411303427)],some [0,1180591620717411303427]),
  ([some (.word 1),none],none),
  ([some (.word 1),some (.word 0)],some [1,0]),
  ([some (.word 1),some (.word 1)],some [1,1]),
  ([some (.word 1),some (.loc 3 5)],none),
  ([some (.word 1),some (.word 1180591620717411303427)],some [1,1180591620717411303427]),
  ([some (.loc 3 5),none],none),
  ([some (.loc 3 5),some (.word 0)],none),
  ([some (.loc 3 5),some (.word 1)],none),
  ([some (.loc 3 5),some (.loc 3 5)],none),
  ([some (.loc 3 5),some (.word 1180591620717411303427)],none),
  ([some (.word 1180591620717411303427),none],none),
  ([some (.word 1180591620717411303427),some (.word 0)],some [1180591620717411303427,0]),
  ([some (.word 1180591620717411303427),some (.word 1)],some [1180591620717411303427,1]),
  ([some (.word 1180591620717411303427),some (.loc 3 5)],none),
  ([some (.word 1180591620717411303427),some (.word 1180591620717411303427)],some [1180591620717411303427,1180591620717411303427]),
  ([some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0),some (.word 0)],some [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
  ([some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.word 1),some (.loc 3 5)],none),
  ([none,some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427),some (.word 1180591620717411303427)],none)]

-- Independent mapped-source type has no equality instance.
example {width : Nat} [NeZero width] (functions : List (Nat → Nat))
    (value : Nat → Nat) (member : value ∈ functions) :
    ∃ word : BitVec width, (some (WordLocW.word (value 0)) : Option (WordLocW width)) = some (.word word) := by
  apply theWordsMapExists functions (functions.map (fun f => (f 0 : BitVec width))) value
    (fun f => some (.word (f 0)))
  constructor
  · have extraction : ∀ fs : List (Nat → Nat),
        theWords (fs.map (fun f => some (.word (f 0 : BitVec width)))) =
          some (fs.map (fun f => (f 0 : BitVec width))) := by
        intro fs
        induction fs with
        | nil => rfl
        | cons f fs ih => simp only [List.map_cons,theWords]; rw [ih]
    exact extraction functions
  · exact member

private def check {width : Nat} [NeZero width]
    (captures : List (List (Option (WordLocW width)) × Option (List Nat))) : Bool :=
  captures.all (fun (values,expected) =>
    (theWords values).map (List.map BitVec.toNat) == expected)

def run : IO Bool := do
  let ok := check captures1 && check captures8 && check captures64 && check captures80
  IO.println (if ok then "PASS original full WordToStack extraction (136 kernel/runtime outputs)"
    else "FAIL original full WordToStack extraction")
  pure ok

end Flapjack.Test.WordToStackWordExtractionParity
