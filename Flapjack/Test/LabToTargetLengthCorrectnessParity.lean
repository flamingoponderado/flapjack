import Flapjack.Compiler.Backend.LabToTarget.LengthCorrectness
namespace Flapjack.Test.LabToTargetLengthCorrectnessParity
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example : lineLengthOk (width := 8) (.label 1 2 0) := rfl
example : ¬lineLengthOk (width := 8) (.label 1 2 1) := by simp [lineLengthOk,lineBytes,lineLen]
example : lineLengthOk (width := 8) (.asm (.asmi (.inst .skip)) [1,2] 2) := rfl
example : ¬lineLengthOk (width := 8) (.asm (.asmi (.inst .skip)) [1,2] 3) := by simp [lineLengthOk,lineBytes,lineLen]
example : lineLengthOk (width := 8) (.labAsm (.jump (.lab 1 2)) 77 [1,2] 2) := rfl
example : secLengthOk (width := 8) ⟨7,[.label 1 2 0,.asm (.asmi (.inst .skip)) [1,2] 2,.labAsm (.jump (.lab 1 2)) 77 [3] 1]⟩ := by simp [secLengthOk,lineLengthOk,lineBytes,lineLen]
example : secLength (width := 8) [.label 1 2 0,.asm (.asmi (.inst .skip)) [1,2] 2,.labAsm (.jump (.lab 1 2)) 77 [3] 1] 17 = 20 := rfl
example : secLength (width := 8) [.asm (.asmi (.inst .skip)) [1] 3] 17 ≠ ([.asm (.asmi (.inst .skip)) [1] 3].map (lineLength (width := 8))).sum + 17 := by decide
example {width : Nat} [NeZero width]
    (ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (n : Nat) :
    (∀ line ∈ ls, lineLengthOk line) → secLength ls n = (ls.map lineLength).sum + n := secLength_sumLineLength ls n

def runChecks : IO Bool := do
  IO.println "PASS full annotated length correctness (8 original observations, full arbitrary-position consumer)"
  pure true
end Flapjack.Test.LabToTargetLengthCorrectnessParity
