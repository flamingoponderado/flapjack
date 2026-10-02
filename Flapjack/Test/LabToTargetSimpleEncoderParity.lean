import Flapjack.Compiler.Backend.LabToTarget.SimpleEncoder
namespace Flapjack.Test.LabToTargetSimpleEncoderParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def shrink : HolAsm 8 → List (BitVec 8)
  | .jump w => if w = 0 then [0,0,0,0] else [1,1]
  | _ => [99,99]
private def grow : HolAsm 8 → List (BitVec 8)
  | .jump w => if w = 0 then [0] else [1,1,1]
  | _ => [99,99]
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def sl : List (LabLineHOL 8) := [.labAsm (.jump (.lab 3 4)) 0 [0,0,0,0] 4]
private def gl : List (LabLineHOL 8) := [.labAsm (.jump (.lab 3 4)) 0 [0] 1]
private def acc : List (LabLineHOL 8) := [.label 1 7 99]
private def strange : List (LabLineHOL 8) :=
  [.label 99 0 5,.asm (.asmi (.inst .skip)) [] 77,.label 2 1 0]
example : encLinesAgainSimp labs [] 13 grow [] = ([],true) := rfl
private theorem shrinkFull : encLinesAgainSimp labs [] 0 shrink sl =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1] 4],true) := by
  simp [encLinesAgainSimp,labs,sl,shrink,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgainSimp labs [] 0 shrink sl =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1] 4],true) := shrinkFull
private theorem growFull : encLinesAgainSimp labs [] 0 grow gl =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],false) := by
  simp [encLinesAgainSimp,labs,gl,grow,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgainSimp labs [] 0 grow gl =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],false) := growFull
example : encLinesAgainSimp labs [] 0 grow [.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3] =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],true) := by
  simp [encLinesAgainSimp,labs,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert]
example : encLinesAgain labs [] 0 shrink sl acc true =
    ([.label 1 7 99,.labAsm (.jump (.lab 3 4)) 10 [1,1] 4],4,true) := by
  simpa [shrinkFull,acc,secLength] using encLinesAgainSimp_eq labs [] 0 shrink sl acc true
example : encLinesAgain labs [] 0 shrink sl acc false =
    ([.label 1 7 99,.labAsm (.jump (.lab 3 4)) 10 [1,1] 4],4,false) := by
  simpa [shrinkFull,acc,secLength] using encLinesAgainSimp_eq labs [] 0 shrink sl acc false
example : encLinesAgain labs [] 0 grow gl acc true =
    ([.label 1 7 99,.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],3,false) := by
  simpa [growFull,acc,secLength] using encLinesAgainSimp_eq labs [] 0 grow gl acc true
example : (encLinesAgainSimp labs [] 0 shrink sl).1.map lineLen = sl.map lineLen :=
  by
    rw [shrinkFull]
    exact encLinesAgainSimp_len labs [] 0 shrink sl _ shrinkFull
example : (encLinesAgainSimp labs [] 0 grow gl).1.map lineLen ≠ gl.map lineLen := by
  rw [growFull]
  simp [gl,lineLen]
example : encLinesAgainSimp labs [] 3 grow strange = (strange,true) := rfl
example : encLinesAgain labs [] 3 grow strange acc false = (acc.reverse ++ strange,85,false) := by
  simpa [encLinesAgainSimp,strange,acc,secLength] using
    encLinesAgainSimp_eq labs [] 3 grow strange acc false
example : encLinesAgainSimp labs [] 3 shrink sl =
    ([.labAsm (.jump (.lab 3 4)) 7 [1,1] 4],true) := by
  simp [encLinesAgainSimp,labs,sl,shrink,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
private theorem wrappedFull : encLinesAgainSimp labs [] 260 shrink sl =
    ([.labAsm (.jump (.lab 3 4)) 6 [1,1] 4],true) := by
  simp [encLinesAgainSimp,labs,sl,shrink,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgainSimp labs [] 260 shrink sl =
    ([.labAsm (.jump (.lab 3 4)) 6 [1,1] 4],true) := wrappedFull
example : encLinesAgain labs [] 260 shrink sl acc true =
    ([.label 1 7 99,.labAsm (.jump (.lab 3 4)) 6 [1,1] 4],264,true) := by
  simpa [wrappedFull,acc,secLength] using encLinesAgainSimp_eq labs [] 260 shrink sl acc true
example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (b : Bool) :
    let (ls',flag) := encLinesAgainSimp labs ffis pos enc ls
    encLinesAgain labs ffis pos enc ls acc b =
      (acc.reverse ++ ls',secLength ls' pos,b && flag) := encLinesAgainSimp_eq labs ffis pos enc ls acc b
example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) →
      res.map lineLen = lines.map lineLen := encLinesAgainSimp_len labs ffis pos enc lines res
def runChecks : IO Bool := do
  IO.println "PASS full simple encoder accumulator/position/flag agreement (14 original observations, 2 generic consumers)"
  return true
end Flapjack.Test.LabToTargetSimpleEncoderParity
