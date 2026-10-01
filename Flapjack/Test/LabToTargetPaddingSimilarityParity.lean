import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Padding

/-! Original padding observations, including nonempty accumulators and nops. -/
namespace Flapjack.Test.LabToTargetPaddingSimilarityParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
private abbrev L := Line (AsmOrCbw (HolAsm 8) HolMemop (HolAddr 8))
  (AsmWithLab HolCmp (HolRegImm 8) MlString) (BitVec 8)
private def fixture : List L :=
  [.label 1 2 9, .asm (.asmi (.inst .skip)) [1] 1, .labAsm (.jump (.lab 1 2)) 13 [2] 1]
example : addNop [7] fixture =
    [.label 1 2 9, .asm (.asmi (.inst .skip)) [1,7] 2,
      .labAsm (.jump (.lab 1 2)) 13 [2] 1] := by cbv
example : padSection [7] fixture [] =
    [.label 1 2 0, .asm (.asmi (.inst .skip)) [1] 1,
      .labAsm (.jump (.lab 1 2)) 13 [2] 1] := by cbv
example : padSection [] fixture [] =
    [.label 1 2 0, .asm (.asmi (.inst .skip)) [1] 1,
      .labAsm (.jump (.lab 1 2)) 13 [2] 1] := by cbv
example : padSection [7] ([.label 1 2 1, .asm (.asmi (.inst .skip)) [] 2] : List L)
    [.labAsm (.jump (.lab 1 2)) 19 [4] 1] =
    [.labAsm (.jump (.lab 1 2)) 19 [4,7] 2,
      .label 1 2 0, .asm (.asmi (.inst .skip)) [7,7] 2] := by cbv
example : padSection [7] ([.label 1 2 9, .label 1 3 0] : List L) [] =
    [.label 1 2 0, .label 1 3 0] := by cbv
example : codeSimilar [⟨4, fixture⟩] (padCode [7] [⟨4, fixture⟩]) :=
  codeSimilar_padCode _ _ _ (codeSimilar_refl _)

/-- The full source premise is used at arbitrary positive width and arbitrary
nonempty-or-empty accumulator, rather than replacing it with a closed case. -/
example {width : Nat} [NeZero width] (nop : List (BitVec 8))
    (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    LinesRel lineSimilar (aux.reverse ++ lines) (padSection nop lines aux) := by
  apply lineSimilar_padSection
  have reflRel : ∀ ls : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)),
      LinesRel lineSimilar ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons h t ih => exact .cons (lineSimilar_refl h) ih
  exact reflRel _
end Flapjack.Test.LabToTargetPaddingSimilarityParity
