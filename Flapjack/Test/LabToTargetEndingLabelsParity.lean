import Flapjack.Compiler.Backend.LabToTarget.EndingLabels
namespace Flapjack.Test.LabToTargetEndingLabelsParity
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
private def grow : HolAsm 8 → List (BitVec 8)
  | .jump w => if w = 0 then [0] else [1,1,1]
  | _ => [99,99]
private def labs : Spt (Spt Nat) := sptInsert 3 (sptInsert 4 10 .ln) .ln
private def source : List (LabLineHOL 8) :=
  [.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 999]
example : ¬secEndsWithLabelNative (⟨3,[]⟩ : Section (LabLineHOL 8)) := by simp [secEndsWithLabelNative]
example : secEndsWithLabelNative (⟨3,[.label 3 0 999]⟩ : Section (LabLineHOL 8)) := by simp [secEndsWithLabelNative,isLabelHOL]
example : ¬secEndsWithLabelNative (⟨3,[.label 3 0 0,.asm (.asmi (.inst .skip)) [] 999]⟩ : Section (LabLineHOL 8)) := by simp [secEndsWithLabelNative,isLabelHOL]
example : ¬secEndsWithLabelNative (⟨3,[.labAsm (.jump (.lab 3 4)) 0 [] 999]⟩ : Section (LabLineHOL 8)) := by simp [secEndsWithLabelNative,isLabelHOL]
example : encLinesAgainSimp labs [] 0 grow [] = ([],true) := rfl
private theorem growFull : encLinesAgainSimp labs [] 0 grow source =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3,.label 3 0 999],false) := by
  simp [encLinesAgainSimp,labs,source,grow,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgainSimp labs [] 0 grow source =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3,.label 3 0 999],false) := growFull
example : secEndsWithLabelNative ⟨3,(encLinesAgainSimp labs [] 0 grow source).1⟩ := by
  rw [growFull]
  simp [secEndsWithLabelNative,isLabelHOL]
example : encLinesAgainSimp labs [] 0 grow
    [.labAsm (.jump (.lab 3 4)) 10 [] 77,.label 3 0 99] =
    ([.labAsm (.jump (.lab 3 4)) 10 [] 77,.label 3 0 99],true) := by
  simp [encLinesAgainSimp,labs,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert]
example : encLinesAgainSimp labs [] 3 grow [.label 3 0 777] = ([.label 3 0 777],true) := rfl
example : ∀ sec ∈ (encSecsAgain 0 labs [] grow [⟨3,source⟩,⟨4,[.label 4 0 7]⟩]).1,
    secEndsWithLabelNative sec := by
  generalize hresult : encSecsAgain 0 labs [] grow [⟨3,source⟩,⟨4,[.label 4 0 7]⟩] = result
  rcases result with ⟨res,flag⟩
  exact encSecsAgain_endsWithLabel 0 labs [] grow _ res flag
    ⟨hresult,by simp [secEndsWithLabelNative,source,isLabelHOL]⟩
example : ¬(∀ sec ∈ (encSecsAgain 0 labs [] grow [⟨3,[]⟩]).1, secEndsWithLabelNative sec) := by
  simp [encSecsAgain,encLinesAgain,secEndsWithLabelNative]
example : encSecList grow [⟨3,[.labAsm (.jump (.lab 3 4)) 99 [] 77,.label 3 0 999]⟩] =
    [⟨3,[.labAsm (.jump (.lab 3 4)) 0 [0] 1,.label 3 0 2]⟩] := rfl
example : ∀ sec ∈ encSecList grow [⟨3,[.labAsm (.jump (.lab 3 4)) 99 [] 77,.label 3 0 999]⟩],
    secEndsWithLabelNative sec :=
  encSecList_endsWithLabel grow _ (by simp [secEndsWithLabelNative,isLabelHOL])
example : ¬(∀ sec ∈ encSecList grow [⟨3,[]⟩], secEndsWithLabelNative sec) := by
  simp [encSecList,encSec,secEndsWithLabelNative]

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool) :
    encLinesAgainSimp labs ffis pos enc ls = (res,ok) ∧
      ls ≠ [] ∧ lastLabel ls = true → res ≠ [] ∧ lastLabel res = true := encLinesAgainSimp_endsWithLabel labs ffis pos enc ls res ok

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (lines res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc lines = (res,ok) ∧
      (∀ sec ∈ lines, secEndsWithLabelNative sec) →
    ∀ sec ∈ res, secEndsWithLabelNative sec := encSecsAgain_endsWithLabel pos labs ffis enc lines res ok

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (∀ sec ∈ code, secEndsWithLabelNative sec) →
    ∀ sec ∈ encSecList enc code, secEndsWithLabelNative sec := encSecList_endsWithLabel enc code

def runChecks : IO Bool := do
  IO.println "PASS full encoding ending-label preservation (14 original observations, 3 full consumers)"
  pure true
end Flapjack.Test.LabToTargetEndingLabelsParity
