import Flapjack.Compiler.Backend.LabToTarget.PreconditionPreservation
namespace Flapjack.Test.LabToTargetPreconditionPreservationParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack
open Flapjack.Basis.Pure.MlString
private def encode8 : HolAsm 8 → List (BitVec 8)
  | .inst .skip => [0,0]
  | .jump w => [w,99]
  | .jumpCmp _ _ _ w => [w,88]
  | .loc _ w => [w,77]
  | _ => [10,11]
private def cfg : AsmConfigExact 8 :=
  { isa := .riscv, encode := encode8, bigEndian := false, codeAlignment := 0,
    linkReg := some 7, avoidRegs := [], regCount := 8, fpRegCount := 4,
    twoRegArith := false, validImm := fun _ _ => true,
    addrOffset := (128,127), hwOffset := (128,127), byteOffset := (128,127),
    jumpOffset := (128,127), cjumpOffset := (128,127), locOffset := (128,127) }
private def labs : Spt (Spt Nat) := sptInsert 1 (sptInsert 5 20 .ln) .ln
private def ffis : List HolFfiName := [.extCall (.implode [97]), .extCall (.implode [98])]
private def input : List (LabLineHOL 8) :=
  [.label 1 5 0,.asm (.asmi (.inst .skip)) [0,0] 2,
   .labAsm (.jump (.lab 1 5)) 99 [] 0,.label 1 6 5]
private def acc : List (LabLineHOL 8) := [.asm (.asmi (.inst .skip)) [0] 7]
private def code : List (Section (LabLineHOL 8)) := [⟨1,input⟩,⟨2,[]⟩]
example : (∀ l ∈ input,lineOkPreHOL cfg l) ∧ (∀ l ∈ acc,lineOkPreHOL cfg l) := by
  simp [input,acc,lineOkPreHOL] <;> decide +kernel
example : (encLinesAgain labs ffis 4 cfg.encode input acc true).2.2 = false ∧
    (∀ l ∈ (encLinesAgain labs ffis 4 cfg.encode input acc true).1,lineOkPreHOL cfg l) := by
  constructor
  · decide +kernel
  · exact encLinesAgain_pre labs ffis 4 cfg.encode input acc true _ _ cfg
      ⟨rfl,by simp [input,lineOkPreHOL] <;> decide +kernel,
       by simp [acc,lineOkPreHOL] <;> decide +kernel⟩
example : (encSecsAgain 4 labs ffis cfg.encode code).2 = false ∧
    allEncOkPreHOL cfg (encSecsAgain 4 labs ffis cfg.encode code).1 := by
  constructor
  · decide +kernel
  · exact encSecsAgain_pre 4 labs ffis cfg.encode code _ _ cfg
      ⟨rfl,by simp [code,input,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL] <;> decide +kernel⟩
example : ∀ l ∈ addNop [3,4] input,lineOkPreHOL cfg l := by
  exact addNop_pre cfg [3,4] input (by simp [input,lineOkPreHOL] <;> decide +kernel)
example : ∀ l ∈ padSection [3,4] input acc,lineOkPreHOL cfg l := by
  exact padSection_pre [3,4] input acc cfg
    ⟨by simp [input,lineOkPreHOL] <;> decide +kernel,
     by simp [acc,lineOkPreHOL] <;> decide +kernel⟩
example : allEncOkPreHOL cfg (padCode [3,4] code) := by
  exact padCode_pre [3,4] code cfg
    (by simp [code,input,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL] <;> decide +kernel)
example : ∀ l ∈ (linesUpdLabLen 3 input acc).1,lineOkPreHOL cfg l := by
  exact linesUpdLabLen_pre cfg 3 input acc
    ⟨by simp [input,lineOkPreHOL] <;> decide +kernel,
     by simp [acc,lineOkPreHOL] <;> decide +kernel⟩
example : allEncOkPreHOL cfg (updLabLen 3 code) := by
  exact updLabLen_pre cfg 3 code
    (by simp [code,input,allEncOkPreHOL,secOkPreHOL,lineOkPreHOL] <;> decide +kernel)
example : ¬ (∀ l ∈ padSection [3] [] [.asm (.asmi (.jumpReg 99)) [] 0],lineOkPreHOL cfg l) := by
  simp [padSection,lineOkPreHOL] <;> decide +kernel

example {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines acc : List (LabLineHOL width))
    (ok : Bool) (res : List (LabLineHOL width)) (result : Nat × Bool)
    (c : AsmConfigExact width) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,result) ∧
    (∀ l ∈ lines,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ res,lineOkPreHOL c l := encLinesAgain_pre labs ffis pos enc lines acc ok res result c

example {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8))
    (code res : List (Section (LabLineHOL width))) (ok : Bool) (c : AsmConfigExact width) :
    encSecsAgain pos labs ffis enc code = (res,ok) ∧ allEncOkPreHOL c code →
    allEncOkPreHOL c res := encSecsAgain_pre pos labs ffis enc code res ok c

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (nop : List (BitVec 8)) (xs : List (LabLineHOL width)) :
    (∀ l ∈ xs,lineOkPreHOL c l) → ∀ l ∈ addNop nop xs,lineOkPreHOL c l := addNop_pre c nop xs

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (xs acc : List (LabLineHOL width)) (c : AsmConfigExact width) :
    (∀ l ∈ xs,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ padSection nop xs acc,lineOkPreHOL c l := padSection_pre nop xs acc c

example {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (code : List (Section (LabLineHOL width))) (c : AsmConfigExact width) :
    allEncOkPreHOL c code → allEncOkPreHOL c (padCode nop code) := padCode_pre nop code c

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (n : Nat) (lines acc : List (LabLineHOL width)) :
    (∀ l ∈ lines,lineOkPreHOL c l) ∧ (∀ l ∈ acc,lineOkPreHOL c l) →
    ∀ l ∈ (linesUpdLabLen n lines acc).1,lineOkPreHOL c l := linesUpdLabLen_pre c n lines acc

example {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (n : Nat) (code : List (Section (LabLineHOL width))) :
    allEncOkPreHOL c code → allEncOkPreHOL c (updLabLen n code) := updLabLen_pre c n code

def runChecks : IO Bool := do
  IO.println "PASS full precondition-preservation chain (8 original observations, 7 full consumers)"
  pure true
end Flapjack.Test.LabToTargetPreconditionPreservationParity
