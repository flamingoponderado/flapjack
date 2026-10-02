import Flapjack.Compiler.Backend.LabToTarget.NopInvariant
namespace Flapjack.Test.LabToTargetNopInvariantParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private def enc : HolAsm 8 → List (BitVec 8)
  | .jump w => [w]
  | .jumpCmp _ _ _ w => [w]
  | .loc _ w => [w]
  | _ => [0]
example : lineEncWithNop enc .ln [] 5 (.asm (.asmi (.inst .skip)) [0,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm .halt 77 [235,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm .install 77 [219,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm (.callFFI (MlString.implode [])) 77 [203,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm (.jump (.lab 1 2)) 77 [251,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm (.jumpCmp .equal 1 (.imm 3) (.lab 1 2)) 77 [251,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm (.locValue 1 (.lab 1 2)) 77 [251,0] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.labAsm (.call (.lab 1 2)) 77 [99] 1) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : lineEncWithNop enc .ln [] 5 (.label 1 2 0) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : ¬lineEncWithNop enc .ln [] 5 (.label 1 2 1) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : ¬lineEncWithNop enc .ln [] 5 (.asm (.asmi (.inst .skip)) [0,0] 3) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : ¬lineEncWithNop enc .ln [] 5 (.labAsm (.jump (.lab 1 2)) 77 [251,1] 2) := by
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : linesEncWithNop enc .ln [] 5 [.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 2)) 77 [249,0] 2] := by
  simp only [linesEncWithNop]
  unfold lineEncWithNop encWithNop enc
  decide +kernel
example : allEncWithNop enc .ln [] 5 [⟨0,[]⟩,⟨1,[.label 1 2 0,.asm (.asmi (.inst .skip)) [0,0] 2,.labAsm (.jump (.lab 1 2)) 77 [249,0] 2]⟩,⟨2,[]⟩,⟨3,[.labAsm (.jump (.lab 1 2)) 88 [247] 1]⟩] := by
  simp only [allEncWithNop]
  unfold lineEncWithNop encWithNop enc
  decide +kernel

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (l1 l2 : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos (l1 ++ l2) ↔
      linesEncWithNop enc labs ffis pos l1 ∧
      linesEncWithNop enc labs ffis (pos + (l1.map lineLength).sum) l2 := linesEncWithNop_append enc labs ffis pos l1 l2

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (id : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    (allEncWithNop enc labs ffis pos [] ↔ True) ∧
      (allEncWithNop enc labs ffis pos (⟨id, ls⟩ :: ss) ↔
        linesEncWithNop enc labs ffis pos ls ∧
        allEncWithNop enc labs ffis (pos + (ls.map lineLength).sum) ss) := allEncWithNop_alt enc labs ffis pos id ls ss

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncWithNop enc labs ffis pos line → lineLengthOk line := lineEncWithNop_lengthOk enc labs ffis pos line

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos ls → ∀ line ∈ ls, lineLengthOk line := linesEncWithNop_lengthOk enc labs ffis pos ls

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncWithNop enc labs ffis pos line → labelZero line := lineEncWithNop_labelZero enc labs ffis pos line

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    linesEncWithNop enc labs ffis pos ls → ∀ line ∈ ls, labelZero line := linesEncWithNop_labelZero enc labs ffis pos ls

example {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncWithNop enc labs ffis pos ss → ∀ sec ∈ ss, secLabelZero sec := allEncWithNop_labelZero enc labs ffis pos ss

def runChecks : IO Bool := do
  IO.println "PASS full encoding-with-NOP structural invariants (14 original observations, 7 full consumers)"
  pure true
end Flapjack.Test.LabToTargetNopInvariantParity
