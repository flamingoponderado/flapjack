import Flapjack.Compiler.Backend.WordToStack.ProductionBodyImage.Instructions
import Flapjack.Compiler.Backend.WordToStack.NativeMoves

/-! Complete native move output in the actual production decoder image.
These are Flapjack codec facts, with no HOL correctness theorem counterpart.
The literal source move helpers emit only accepted arithmetic and stack leaves.
No frame bounds, scheduler correctness, desired output, or target run is assumed.
-/
namespace Flapjack.ProductionBodyImage
open Compiler.Backend Compiler.Backend.WordToStack.Native
open Compiler.Backend.StackLang Compiler.Encoders.Asm

/-- Every source/destination formatting pair produces a complete decoder image.
All four literal wMoveSingle clauses and truncated natural offsets are retained. -/
theorem moveSingleImage {width : Nat} [NeZero width]
    (pair : Sum Nat Nat × Sum Nat Nat) (frame : Nat × Nat × Nat) :
    OutputImage (wMoveSingleNative (width := width) pair frame) := by
  rcases pair with ⟨destination, source⟩
  cases destination <;> cases source
  · exact arithmeticImage _
  · exact stackLoadImage _ _
  · exact stackStoreImage _ _
  · exact sequenceImage _ _ (stackLoadImage _ _) (stackStoreImage _ _)

/-- Empty, singleton, and longer source move lists construct the full decoder
image, preserving literal source sequencing rather than flattening the body. -/
theorem moveAuxImage {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    OutputImage (wMoveAuxNative (width := width) moves frame) := by
  induction moves with
  | nil =>
      refine ⟨.skip, ?_⟩
      simp [wMoveAuxNative, holProgToProduction, holProgToProgW, Prog.map, progToProduction]
  | cons pair rest ih =>
      cases rest with
      | nil => exact moveSingleImage pair frame
      | cons next tail => exact sequenceImage _ _ (moveSingleImage pair frame) ih

/-- Arbitrary optional scheduler operands, including NONE's source temporary,
retain their exact format_var output. No scheduling property is required. -/
theorem formattedMovesImage {width : Nat} [NeZero width]
    (moves : List (Option Nat × Option Nat)) (frame : Nat × Nat × Nat) :
    OutputImage (wMoveAuxNative (width := width)
      (moves.map (fun pair =>
        (WordToStackRegFormat.formatVar frame.1 pair.1,
         WordToStackRegFormat.formatVar frame.1 pair.2))) frame) :=
  moveAuxImage _ frame

/-- Actual parmove output supplies a concrete list to the source helper. This
all-input image theorem neither assumes a scheduler result nor proves semantic
move correctness; it retains the executed helper's exact generated body. -/
theorem moveCompilerImage {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (frame : Nat × Nat × Nat) :
    OutputImage (wMoveNative (width := width) moves frame) := by
  unfold wMoveNative
  exact formattedMovesImage _ frame

/-- The complete native single-move body survives the actual decoder inverse.
This is codec infrastructure, not a narrowed HOL move simulation theorem. -/
theorem moveSingleRoundtrip {width : Nat} [NeZero width]
    (pair : Sum Nat Nat × Sum Nat Nat) (frame : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (wMoveSingleNative (width := width) pair frame) = some body ∧
      productionToHolProg body = some (wMoveSingleNative (width := width) pair frame) := by
  obtain ⟨body, image⟩ := moveSingleImage (width := width) pair frame
  exact ⟨body, image, productionToHolProg_of_holProgToProduction _ body image⟩

/-- All ordered auxiliary move bodies survive the inverse without a successful
output premise. Decoder success is constructed from the literal helper. -/
theorem moveAuxRoundtrip {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (wMoveAuxNative (width := width) moves frame) = some body ∧
      productionToHolProg body = some (wMoveAuxNative (width := width) moves frame) := by
  obtain ⟨body, image⟩ := moveAuxImage (width := width) moves frame
  exact ⟨body, image, productionToHolProg_of_holProgToProduction _ body image⟩

/-- The actual full native move compiler's output roundtrip, including source
scheduler temporary moves and exact arithmetic/register/frame-slot payloads. -/
theorem moveCompilerRoundtrip {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (frame : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (wMoveNative (width := width) moves frame) = some body ∧
      productionToHolProg body = some (wMoveNative (width := width) moves frame) := by
  obtain ⟨body, image⟩ := moveCompilerImage (width := width) moves frame
  exact ⟨body, image, productionToHolProg_of_holProgToProduction _ body image⟩

end Flapjack.ProductionBodyImage
