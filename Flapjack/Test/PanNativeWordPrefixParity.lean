import Flapjack.Pancake.PanToWord.ProductionPrefix

namespace Flapjack.Test.PanNativeWordPrefixParity
open Flapjack Pancake.PanLang

private def declarations (width : Nat) : List (Decl (BitVec width)) :=
  [.function ⟨"f", false, false, [], .return (.const 7), .one⟩,
   .function ⟨"main", false, false, [], .call none "f" [], .one⟩]

private theorem source (width : Nat) : ∀ d ∈ declarations width, DeclByteRanged d := by
  intro d member
  simp [declarations] at member
  rcases member with rfl | rfl
  all_goals simp [DeclByteRanged, FunDeclByteRanged, ListParamByteRanged,
    ProgByteRanged, ExpByteRanged, NameRanged, ShapeByteRanged]

/-- Entire original Word program rows, including argument counts, call
arguments/continuations, labels, variables, constant and every Seq/Skip. -/
private def payloadMatches {width : Nat} : List (Nat × Nat × WordLangProgHOL (BitVec width)) → Bool
  | [(64, 1, .seq .skip (.seq (.call none (some 65) [0] none) .skip)),
     (65, 1, .seq (.call none (some 66) [0] none) .skip),
     (66, 1, .seq (.assign 2 (.const value)) (.seq (.return 0 [2]) .skip))] => value == 7
  | _ => false

private def check (width : Nat) [NeZero width] : Bool :=
  match compileFlapjackFrontendWordNative? (declarations width) (source width) with
  | some rows => payloadMatches rows
  | none => false

#guard check 8
#guard check 64
example {width : Nat} [NeZero width] :
    compileFlapjackFrontendWordNative? (declarations width) (source width) =
      some (panToWordCompileProgHOL .riscv
        ((panTargetMoveStartToFront "main" (declarations width)).map declToHOL)) :=
  compileFlapjackFrontendWordNative_original (declarations width) (source width)

def runChecks : IO Bool := do
  if !(check 8 && check 64) then throw (IO.userError "complete original native Word prefix differs")
  IO.println "PASS original full native Word prefix: all3 row payloads/arguments/continuations,64/65/66 calls65/66, widths8+64 and general source theorem"
  return true
end Flapjack.Test.PanNativeWordPrefixParity
