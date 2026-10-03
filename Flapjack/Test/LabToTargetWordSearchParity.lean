import Flapjack.Compiler.Backend.LabToTarget.WordSearch
namespace Flapjack.Test.LabToTargetWordSearchParity
open Flapjack.Misc Flapjack.Compiler.Backend.LabToTarget
example {width : Nat} [NeZero width] (values : List (BitVec width))
    (target : BitVec width) (offset : Nat) :
    findIndex target.toNat (values.map BitVec.toNat) offset = findIndex target values offset :=
  findIndex_mapToNat values target offset
example (base : BitVec 80) (pcs : List (BitVec 80)) (offset : Nat) :
    findIndex (base+BitVec.ofNat 80 7).toNat
      ((pcs.drop 3).map BitVec.toNat) offset =
      findIndex (base+BitVec.ofNat 80 7) (pcs.drop 3) offset :=
  findIndex_mapToNat _ _ _
example : findIndex (7 : BitVec 8) [7,13] 0 = some 0 := by decide
example : findIndex (13 : BitVec 8).toNat ([7,13].map (fun (w : BitVec 8) => w.toNat)) 10 =
    findIndex (13 : BitVec 8) [7,13] 10 := findIndex_mapToNat _ _ _
example : findIndex (7 : BitVec 8) [7,7] 10 = some 10 := by decide
example : findIndex (8 : BitVec 8) [7,13] 10 = none := by decide
example : findIndex (7 : BitVec 8) [] 10 = none := by decide
example : findIndex (257 : BitVec 8) [1,2] 10 = some 10 := by decide
example : findIndex (BitVec.ofNat 80 (2^70+3)).toNat
    ([0,BitVec.ofNat 80 (2^70+3)].map BitVec.toNat) 99 = some 100 := by decide
end Flapjack.Test.LabToTargetWordSearchParity
