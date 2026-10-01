import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding

/-! Original encoding observations exercise both offset branches, growth flags,
position threading, section identities and a nonempty accumulator. -/
namespace Flapjack.Test.LabToTargetEncodingSimilarityParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.Misc
private abbrev L := Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
  (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)
private def enc (_ : HolAsm 8) : List (BitVec 8) := [2,3,4]
private def lines : List L :=
  [.label 1 2 1, .asm (.asmi (.inst .skip)) [6] 1,
    .labAsm (.jump (.lab 1 2)) 7 [7] 1]
example : encSecList enc [⟨4, lines⟩] =
    [⟨4,[.label 1 2 3, .asm (.asmi (.inst .skip)) [2,3,4] 3,
      .labAsm (.jump (.lab 1 2)) 0 [2,3,4] 3]⟩] := by cbv
example : encLinesAgain .ln [] 0 enc lines [] true =
    ([.label 1 2 1, .asm (.asmi (.inst .skip)) [6] 1,
      .labAsm (.jump (.lab 1 2)) 254 [2,3,4] 3],5,false) := by cbv
example : encLinesAgain .ln [] 2 enc
    ([.labAsm (.jump (.lab 1 2)) 254 [7] 4] : List L)
    [.asm (.asmi (.inst .skip)) [9] 4] false =
    ([.asm (.asmi (.inst .skip)) [9] 4,
      .labAsm (.jump (.lab 1 2)) 254 [7] 4],6,false) := by cbv
example : encLinesAgain .ln [] 2 enc
    ([.labAsm (.jump (.lab 1 2)) 7 [7] 4] : List L)
    [.asm (.asmi (.inst .skip)) [9] 4] true =
    ([.asm (.asmi (.inst .skip)) [9] 4,
      .labAsm (.jump (.lab 1 2)) 254 [2,3,4] 4],6,true) := by cbv
example : encSecsAgain 0 .ln [] enc [⟨4,lines⟩,⟨8,[]⟩] =
    ([⟨4,[.label 1 2 1, .asm (.asmi (.inst .skip)) [6] 1,
      .labAsm (.jump (.lab 1 2)) 254 [2,3,4] 3]⟩,⟨8,[]⟩],false) := by cbv
example : codeSimilar [⟨4,lines⟩,⟨8,[]⟩]
    (encSecsAgain 0 .ln [] enc [⟨4,lines⟩,⟨8,[]⟩]).1 := by
  apply encSecsAgain_implies_similar 0 .ln [] enc _ _ _ rfl
end Flapjack.Test.LabToTargetEncodingSimilarityParity
