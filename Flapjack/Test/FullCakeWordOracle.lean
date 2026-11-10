-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang
import Flapjack.Test.CakeWordOracleHelpers

namespace Flapjack.Test.FullCakeWordOracle

open Flapjack.Test.CakeWordOracleHelpers

private def matches_fragment67 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.seq ((.ite .test 4 ((.imm 1)) .skip ((.seq ((.assign 1 ((.const 18446744073709551615)))) ((.alloc 1 (live61, .ln))))))) ((.seq ((.move 0 [(1, 4)])) ((.seq ((.seq ((.assign 1 ((.shift .lsr ((.var 1)) (.const 2))))) ((.seq ((.ite .lower 1 ((.imm 65536)) ((.assign 1 ((.shift .lsl ((.op .add [(.var 1), (.const 1)])) (.const 3))))) ((.assign 1 ((.const 18446744073709551615)))))) ((.seq ((.assign 3 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 3 ((.reg 1)) ((.seq .skip ((.seq ((.alloc 1 (live62, live63))) .skip)))) .skip)))))))) ((.mustTerminate ((.call ((some ([6], (live64, .ln), .skip, 64, 2))) ((some 10)) [4, 2] none)))))))))) ((.seq ((.assign 8 ((.const 4)))) ((.seq ((.assign 10 ((.const 0)))) ((.seq ((.seq ((.store ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))]), (.op .add [(.const 8), (.shift .lsl ((.var 10)) (.const 1))])])) 8)) ((.assign 12 (.const 2))))) ((.seq ((.seq ((.set .globals ((.var 6)))) ((.seq ((.set .globReal ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 6)) (.const 5))])))) ((.assign 14 (.const 2))))))) ((.seq ((.call ((some ([18], (live65, .ln), .skip, 64, 3))) ((some 76)) [] ((some (16, (.move 0 [(18, 16)]), 64, 4))))) ((.return 0 [18])))))))))))))) =>
      decide (live61 = Flapjack.sptListInsert [0] .ln) &&
      decide (live62 = Flapjack.sptListInsert [0] .ln) &&
      decide (live63 = Flapjack.sptListInsert [2, 4] .ln) &&
      decide (live64 = Flapjack.sptListInsert [0] .ln) &&
      decide (live65 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches_fragment72 (entry : Flapjack.WordLangProgHOL (BitVec 64)) : Bool :=
  match entry with
  | ((.seq ((.ite .equal 6 ((.imm 0)) ((.assign 8 (.const 18))) ((.assign 8 (.const 2))))) ((.ite .equal 8 ((.imm 18)) ((.seq ((.assign 10 (.const 2))) ((.seq ((.assign 12 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 8)])))))) ((.seq ((.call ((some ([14], (live80, live81), .skip, 72, 2))) none [10, 4, 12] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 14)) ((.assign 16 (.const 2))))))))))) ((.return 0 [14])))))))))) ((.seq ((.assign 20 (.const 2))) ((.seq ((.call ((some ([22], (live82, live83), .skip, 72, 3))) ((some 72)) [20, 4] none)) ((.seq ((.seq ((.assign 1 ((.op .add [(.lookup .currHeap), (.shift .lsr ((.var 2)) (.const 5))])))) ((.seq ((.assign 3 ((.const 281474976710715)))) ((.seq ((.store ((.var 1)) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 22)) ((.assign 24 (.const 2))))))))))) ((.return 0 [22])))))))))))) =>
      decide (live80 = Flapjack.sptListInsert [0] .ln) &&
      decide (live81 = Flapjack.sptListInsert [2] .ln) &&
      decide (live82 = Flapjack.sptListInsert [0] .ln) &&
      decide (live83 = Flapjack.sptListInsert [2] .ln)
  | _ => false

private def matches57 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (64, 1, (.seq ((.assign 2 ((.const 0)))) ((.seq ((.assign 4 ((.const 12)))) fragment67))), 0) =>
      matches_fragment67 fragment67
  | _ => false

private def matches63 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (72, 3, (.seq ((.assign 6 ((.load ((.op .add [(.op .add [(.lookup .currHeap), (.shift .lsr ((.var 4)) (.const 5))]), (.const 16)])))))) fragment72), 0) =>
      matches_fragment72 fragment72
  | _ => false

private def matches64 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (76, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live84, .ln), .skip, 76, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 16)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 80)) [0] none))))))))), 0) =>
      decide (live84 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches65 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (80, 1, (.seq ((.assign 2 ((.const 4)))) ((.seq ((.call ((some ([4], (live85, .ln), .skip, 80, 2))) ((some 62)) [2] none)) ((.seq ((.assign 6 (.const 2))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 24)])) 6)) ((.assign 8 (.const 2))))) ((.call none ((some 84)) [0] none))))))))), 0) =>
      decide (live85 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches66 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (84, 1, (.seq ((.call ((some ([2], (live86, .ln), .skip, 84, 2))) ((some 73)) [] none)) ((.seq ((.assign 4 (.const 2))) ((.call none ((some 88)) [0] none))))), 0) =>
      decide (live86 = Flapjack.sptListInsert [0] .ln)
  | _ => false

private def matches67 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (73, 1, (.return 0 [2]), 0) =>
      true
  | _ => false

private def matches68 (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat)) : Bool :=
  match entry with
  | (88, 1, (.seq ((.seq ((.assign 1 ((.op .sub [(.lookup .triggerGC), (.lookup .nextFree)])))) ((.ite .lower 1 ((.imm 16)) ((.seq .skip ((.seq ((.assign 1 ((.const 16)))) ((.seq ((.alloc 1 (live87, .ln))) .skip)))))) .skip)))) ((.seq ((.assign 2 (.const 2))) ((.seq ((.seq ((.set .triggerGC ((.op .sub [(.lookup .triggerGC), (.const 16)])))) ((.seq ((.assign 1 ((.op .sub [(.lookup .endOfHeap), (.const 16)])))) ((.seq ((.set .endOfHeap ((.var 1)))) ((.seq ((.assign 3 ((.const 281474976710667)))) ((.seq ((.seq ((.store ((.op .add [(.var 1), (.const 0)])) 3)) ((.seq ((.store ((.op .add [(.var 1), (.const 8)])) 2)) .skip)))) ((.assign 4 ((.op .or [(.shift .lsl ((.op .sub [(.var 1), (.lookup .currHeap)])) (.const 5)), (.const 1)])))))))))))))) ((.seq ((.seq ((.store ((.op .add [(.lookup .globReal), (.const 32)])) 4)) ((.assign 6 (.const 2))))) ((.return 0 [6]))))))))), 0) =>
      decide (live87 = Flapjack.sptListInsert [0] .ln)
  | _ => false

/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  code.length == 69 &&
    (match code[0]? with | some entry => shared_matches0_3 entry | none => false) &&
    (match code[1]? with | some entry => shared_matches1_2 entry | none => false) &&
    (match code[2]? with | some entry => shared_matches2_2 entry | none => false) &&
    (match code[3]? with | some entry => shared_matches3_2 entry | none => false) &&
    (match code[4]? with | some entry => shared_matches4_2 entry | none => false) &&
    (match code[5]? with | some entry => shared_matches5_2 entry | none => false) &&
    (match code[6]? with | some entry => shared_matches6_2 entry | none => false) &&
    (match code[7]? with | some entry => shared_matches7_2 entry | none => false) &&
    (match code[8]? with | some entry => shared_matches8_2 entry | none => false) &&
    (match code[9]? with | some entry => shared_matches9_2 entry | none => false) &&
    (match code[10]? with | some entry => shared_matches10_2 entry | none => false) &&
    (match code[11]? with | some entry => shared_matches11_2 entry | none => false) &&
    (match code[12]? with | some entry => shared_matches12_2 entry | none => false) &&
    (match code[13]? with | some entry => shared_matches13_2 entry | none => false) &&
    (match code[14]? with | some entry => shared_matches14 entry | none => false) &&
    (match code[15]? with | some entry => shared_matches15 entry | none => false) &&
    (match code[16]? with | some entry => shared_matches16 entry | none => false) &&
    (match code[17]? with | some entry => shared_matches17 entry | none => false) &&
    (match code[18]? with | some entry => shared_matches18 entry | none => false) &&
    (match code[19]? with | some entry => shared_matches19 entry | none => false) &&
    (match code[20]? with | some entry => shared_matches20 entry | none => false) &&
    (match code[21]? with | some entry => shared_matches21 entry | none => false) &&
    (match code[22]? with | some entry => shared_matches22 entry | none => false) &&
    (match code[23]? with | some entry => shared_matches23 entry | none => false) &&
    (match code[24]? with | some entry => shared_matches24 entry | none => false) &&
    (match code[25]? with | some entry => shared_matches25 entry | none => false) &&
    (match code[26]? with | some entry => shared_matches26 entry | none => false) &&
    (match code[27]? with | some entry => shared_matches27 entry | none => false) &&
    (match code[28]? with | some entry => shared_matches28 entry | none => false) &&
    (match code[29]? with | some entry => shared_matches29 entry | none => false) &&
    (match code[30]? with | some entry => shared_matches30 entry | none => false) &&
    (match code[31]? with | some entry => shared_matches31 entry | none => false) &&
    (match code[32]? with | some entry => shared_matches32 entry | none => false) &&
    (match code[33]? with | some entry => shared_matches33 entry | none => false) &&
    (match code[34]? with | some entry => shared_matches34 entry | none => false) &&
    (match code[35]? with | some entry => shared_matches35 entry | none => false) &&
    (match code[36]? with | some entry => shared_matches36 entry | none => false) &&
    (match code[37]? with | some entry => shared_matches37 entry | none => false) &&
    (match code[38]? with | some entry => shared_matches38 entry | none => false) &&
    (match code[39]? with | some entry => shared_matches39 entry | none => false) &&
    (match code[40]? with | some entry => shared_matches40 entry | none => false) &&
    (match code[41]? with | some entry => shared_matches41 entry | none => false) &&
    (match code[42]? with | some entry => shared_matches42 entry | none => false) &&
    (match code[43]? with | some entry => shared_matches43 entry | none => false) &&
    (match code[44]? with | some entry => shared_matches44 entry | none => false) &&
    (match code[45]? with | some entry => shared_matches45 entry | none => false) &&
    (match code[46]? with | some entry => shared_matches46 entry | none => false) &&
    (match code[47]? with | some entry => shared_matches47 entry | none => false) &&
    (match code[48]? with | some entry => shared_matches48 entry | none => false) &&
    (match code[49]? with | some entry => shared_matches49 entry | none => false) &&
    (match code[50]? with | some entry => shared_matches50 entry | none => false) &&
    (match code[51]? with | some entry => shared_matches51 entry | none => false) &&
    (match code[52]? with | some entry => shared_matches52 entry | none => false) &&
    (match code[53]? with | some entry => shared_matches53 entry | none => false) &&
    (match code[54]? with | some entry => shared_matches54 entry | none => false) &&
    (match code[55]? with | some entry => shared_matches55 entry | none => false) &&
    (match code[56]? with | some entry => shared_matches56 entry | none => false) &&
    (match code[57]? with | some entry => matches57 entry | none => false) &&
    (match code[58]? with | some entry => shared_matches58 entry | none => false) &&
    (match code[59]? with | some entry => shared_matches59 entry | none => false) &&
    (match code[60]? with | some entry => shared_matches60 entry | none => false) &&
    (match code[61]? with | some entry => shared_matches61 entry | none => false) &&
    (match code[62]? with | some entry => shared_matches62 entry | none => false) &&
    (match code[63]? with | some entry => matches63 entry | none => false) &&
    (match code[64]? with | some entry => matches64 entry | none => false) &&
    (match code[65]? with | some entry => matches65 entry | none => false) &&
    (match code[66]? with | some entry => matches66 entry | none => false) &&
    (match code[67]? with | some entry => matches67 entry | none => false) &&
    (match code[68]? with | some entry => matches68 entry | none => false)

end Flapjack.Test.FullCakeWordOracle
