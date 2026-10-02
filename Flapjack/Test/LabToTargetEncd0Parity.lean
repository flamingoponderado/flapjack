import Flapjack.Compiler.Backend.LabToTarget.EncodingInvariant
namespace Flapjack.Test.LabToTargetEncd0Parity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString Flapjack.Misc
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
private def code : LabProgHOL 8 := [⟨1,sl⟩,⟨2,[]⟩]
private theorem shrinkValid : ∀ line ∈ sl, lineEncd0 shrink line := by
  intro line hm
  simp only [sl,List.mem_singleton] at hm
  subst line
  exact ⟨rfl,by decide +kernel,0,rfl⟩
private theorem growValid : ∀ line ∈ gl, lineEncd0 grow line := by
  intro line hm
  simp only [gl,List.mem_singleton] at hm
  subst line
  exact ⟨rfl,by decide +kernel,0,rfl⟩
private theorem accValid : ∀ line ∈ acc, lineEncd0 shrink line := by simp [acc,lineEncd0]
private theorem codeValid : allEncd0 shrink code := by
  intro sec hm
  simp [code] at hm
  rcases hm with rfl | rfl
  · exact shrinkValid
  · simp [secEncd0]
example : lineEncd0 shrink (.label 99 0 999) := trivial
example : ¬lineEncd0 shrink (.asm (.asmi (.inst .skip)) [] 0) := by
  simp [lineEncd0,cbwToAsmExact,cbwToAsmHOL,shrink]
example : ∀ line ∈ sl, lineEncd0 shrink line := shrinkValid
example : ∀ line ∈ gl, lineEncd0 grow line := growValid
example : ∀ line ∈ (encLinesAgain labs [] 0 shrink sl acc true).1, lineEncd0 shrink line :=
  encLinesAgain_encd0 labs [] 0 shrink sl acc true _ _ ⟨rfl,shrinkValid,accValid⟩
example : ∀ line ∈ (encLinesAgain labs [] 0 grow gl [] true).1, lineEncd0 grow line :=
  encLinesAgain_encd0 labs [] 0 grow gl [] true _ _ ⟨rfl,growValid,by simp⟩
example : encLinesAgain labs [] 0 shrink sl acc true =
    ([.label 1 7 99,.labAsm (.jump (.lab 3 4)) 10 [1,1] 4],4,true) := by
  simp [encLinesAgain,labs,sl,acc,shrink,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgain labs [] 0 grow gl [] true =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],3,false) := by
  simp [encLinesAgain,labs,gl,grow,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert,labInst]
example : encLinesAgain labs [] 0 grow [.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3] [] false =
    ([.labAsm (.jump (.lab 3 4)) 10 [1,1,1] 3],3,false) := by
  simp [encLinesAgain,labs,getJumpOffset,getLabel,findPos,lookupAny,sptLookup,sptInsert]
example : allEncd0 shrink (encSecList shrink code) := encSecList_encd0 shrink code
example : allEncd0 shrink (encSecsAgain 0 labs [] shrink code).1 :=
  encSecsAgain_encd0 0 labs [] shrink code _ _ ⟨rfl,codeValid⟩
example : ∀ line ∈ (linesUpdLabLen 3 sl acc).1, lineEncd0 shrink line :=
  linesUpdLabLen_encd0 3 sl acc shrink ⟨shrinkValid,accValid⟩
example : allEncd0 shrink (updLabLen 3 code) := updLabLen_encd0 3 code shrink codeValid
example : allEncd0 (fun _ => []) (encSecList (fun _ => []) code) := encSecList_encd0 _ _
example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncd0 enc (encSecList enc ls) := encSecList_encd0 enc ls
example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
      (∀ line ∈ lines, lineEncd0 enc line) ∧
      (∀ line ∈ acc, lineEncd0 enc line) →
    ∀ line ∈ res, lineEncd0 enc line := encLinesAgain_encd0 labs ffis pos enc lines acc ok res ok'
example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc ls = (res,ok) ∧ allEncd0 enc ls →
      allEncd0 enc res := encSecsAgain_encd0 pos labs ffis enc ls res ok
example {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (enc : HolAsm width → List (BitVec 8)) :
    (∀ line ∈ ls, lineEncd0 enc line) ∧
      (∀ line ∈ acc, lineEncd0 enc line) →
    ∀ line ∈ (linesUpdLabLen pos ls acc).1, lineEncd0 enc line := linesUpdLabLen_encd0 pos ls acc enc
example {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) :
    allEncd0 enc ss → allEncd0 enc (updLabLen pos ss) := updLabLen_encd0 pos ss enc
def runChecks : IO Bool := do
  IO.println "PASS full encd0 max-length witness invariant (14 original observations, 5 generic consumers)"
  return true
end Flapjack.Test.LabToTargetEncd0Parity
