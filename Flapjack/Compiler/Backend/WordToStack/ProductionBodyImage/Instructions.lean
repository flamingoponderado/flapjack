import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Compiler.Backend.StackLang.ProductionCodec
import Flapjack.RiscV.AllocatorMemoryInvariant

/-! Native instruction output in the actual production decoder image.
These are Flapjack codec facts, not restricted ports of HOL correctness.
The existing runtime memory guard matters: original Load16/Store16 lower to
Inst Skip, which has no production instruction counterpart. -/
namespace Flapjack.ProductionBodyImage
open Compiler.Backend
open Compiler.Backend.WordToStack.Native Compiler.Backend.StackLang
open Compiler.Encoders.Asm RiscV

/-- Decoder-image packaging for compiler-generated bodies. No HOL original. -/
def OutputImage {width : Nat} [NeZero width] (body : HolProg width) : Prop :=
  ∃ production, holProgToProduction body = some production

/-- Successful child decoders construct the real complete sequence result.
This helper is used with concrete compiler-generated children. -/
theorem sequenceImage {width : Nat} [NeZero width] (first second : HolProg width)
    (left : OutputImage first) (right : OutputImage second) : OutputImage (.seq first second) := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right
  refine ⟨.seq a b, ?_⟩
  simp only [holProgToProduction, holProgToProgW, Prog.map, progToProduction] at ha hb ⊢
  rw [ha, hb]
  rfl

/-- The original stack-load leaf always has a concrete production image. -/
theorem stackLoadImage {width : Nat} [NeZero width] (register offset : Nat) :
    OutputImage (.stackLoad register offset : HolProg width) := by
  refine ⟨.stackLoad register offset, ?_⟩
  simp [holProgToProduction, holProgToProgW, Prog.map, progToProduction]

/-- The original stack-store leaf always has a concrete production image. -/
theorem stackStoreImage {width : Nat} [NeZero width] (register offset : Nat) :
    OutputImage (.stackStore register offset : HolProg width) := by
  refine ⟨.stackStore register offset, ?_⟩
  simp [holProgToProduction, holProgToProgW, Prog.map, progToProduction]

/-- All ordered loads retain their complete decoder image. -/
theorem stackLoadsImage {width : Nat} [NeZero width] (loads : List (Nat × Nat))
    (body : HolProg width) (image : OutputImage body) : OutputImage (wStackLoadNative loads body) := by
  induction loads with
  | nil => exact image
  | cons pair rest ih =>
    exact sequenceImage _ _ (stackLoadImage pair.1 pair.2) ih

/-- Full first-temporary writes preserve concrete image on both formatting
branches. The instruction theorem discharges the callback for its real leaves. -/
theorem registerWriteImage {width : Nat} [NeZero width] (make : Nat → HolProg width)
    (register : Nat) (frame : Nat × Nat × Nat) (image : ∀ n, OutputImage (make n)) :
    OutputImage (wRegWrite1Native make register frame) := by
  by_cases h : register / 2 < frame.1
  · simp only [wRegWrite1Native, if_pos h]
    exact image _
  · simp only [wRegWrite1Native, if_neg h]
    exact sequenceImage _ _ (image _) (stackStoreImage _ _)

/-- A concrete accepted instruction produces the complete production leaf. -/
theorem instructionImage {width : Nat} [NeZero width] (instruction : HolInst width)
    (production : WordInst (BitVec width))
    (decoded : wordLangInstFromHOL instruction.toWordLangInst = some production) :
    OutputImage (.inst instruction) := by
  refine ⟨.inst production, ?_⟩
  simp only [holProgToProduction, holProgToProgW, Prog.map, progToProduction]
  rw [decoded]
  rfl

/-- Native constants always retain their word payload in the decoder. -/
theorem constantImage {width : Nat} [NeZero width] (register : Nat) (value : BitVec width) :
    OutputImage (.inst (.const register value)) :=
  instructionImage _ (.const register value) rfl

/-- All eight native arithmetic constructors have a real production counterpart.
This includes LongDiv and the four-register original AddCarry. -/
theorem arithmeticImage {width : Nat} [NeZero width] (operation : HolArith width) :
    OutputImage (.inst (.arith operation)) := by
  cases operation <;>
    simp [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction,
      HolInst.toWordLangInst, HolArith.toWordLangArith, wordLangInstFromHOL,
      wordLangArithFromHOL]

/-- Memory instruction leaves preserve their complete address and offset. This
is the decoder image, not a claim that wInst lowers sixteen-bit operations. -/
theorem memoryImage {width : Nat} [NeZero width] (operation : WordMemOp)
    (register address : Nat) (offset : BitVec width) :
    OutputImage (.inst (.mem operation register (.addr address offset))) := by
  simp only [OutputImage, holProgToProduction, holProgToProgW, Prog.map, progToProduction,
    HolInst.toWordLangInst, HolAddr.toWordLangAddr, wordLangInstFromHOL]
  split <;> simp

/-- Every native arithmetic lowering clause, including ordered spill loads and
writes, has a real decoder image at arbitrary frame/register tuples. -/
theorem arithmeticCompilerImage {width : Nat} [NeZero width] (operation : HolArith width)
    (frame : Nat × Nat × Nat) : OutputImage (wInstNative (.arith operation) frame) := by
  cases operation <;> try cases ‹HolRegImm width›
  all_goals dsimp only [wInstNative]
  all_goals first
    | exact arithmeticImage _
    | apply stackLoadsImage
      first
        | exact arithmeticImage _
        | apply registerWriteImage
          intro register
          exact arithmeticImage _

/-- The six memory operations accepted by the actual allocator retain their
full native lowering output. Sixteen-bit operations are excluded by that
existing runtime guard, not by a fabricated successful-output premise. -/
theorem memoryCompilerImage {width : Nat} [NeZero width] (operation : WordMemOp)
    (destination address : Nat) (offset : BitVec width) (frame : Nat × Nat × Nat)
    (supported : operation ≠ .load16 ∧ operation ≠ .store16) :
    OutputImage (wInstNative (.mem operation destination (.addr address offset)) frame) := by
  cases operation <;> try simp at supported
  all_goals dsimp only [wInstNative]
  all_goals apply stackLoadsImage
  all_goals first
    | exact memoryImage _ _ _ _
    | apply registerWriteImage
      intro register
      exact memoryImage _ _ _ _

/-- Complete native instruction-output image on the actual production input
domain. The decoder and existing memory guard name that domain; the actual
allocator caller must derive them. No output-codec, desired relation, bounds
or target evaluation is assumed. This is not a narrowed HOL theorem port. -/
theorem instructionCompilerImage {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (production : WordInst (BitVec width))
    (decoded : wordLangInstFromHOL instruction = some production)
    (supported : allocatorMemorySupported (.inst production) = true)
    (frame : Nat × Nat × Nat) :
    OutputImage (wInstNative (HolInst.ofWordLangInst instruction) frame) := by
  cases instruction with
  | skip => simp [wordLangInstFromHOL] at decoded
  | const destination value =>
      simp only [HolInst.ofWordLangInst, wInstNative]
      apply registerWriteImage
      intro register
      exact constantImage register value
  | arith operation =>
      exact arithmeticCompilerImage (HolArith.ofWordLangArith operation) frame
  | mem operation destination address =>
      rcases address with ⟨base, offset⟩
      have allowed : operation ≠ .load16 ∧ operation ≠ .store16 := by
        constructor <;> intro equal <;> subst operation
        all_goals simp only [wordLangInstFromHOL] at decoded
        all_goals split at decoded <;> cases decoded <;>
          simp [allocatorMemorySupported] at supported
      exact memoryCompilerImage operation destination base offset frame allowed

/-- The derived output decoder result recovers the entire original native body,
including every ordered load/write and exact instruction payload. This uses
its actual constructed image, not an assumed successful output conversion. -/
theorem instructionCompilerRoundtrip {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) (production : WordInst (BitVec width))
    (decoded : wordLangInstFromHOL instruction = some production)
    (supported : allocatorMemorySupported (.inst production) = true)
    (frame : Nat × Nat × Nat) :
    ∃ body, holProgToProduction (wInstNative (HolInst.ofWordLangInst instruction) frame) = some body ∧
      productionToHolProg body = some (wInstNative (HolInst.ofWordLangInst instruction) frame) := by
  obtain ⟨body, image⟩ := instructionCompilerImage instruction production decoded supported frame
  exact ⟨body, image, productionToHolProg_of_holProgToProduction _ body image⟩

end Flapjack.ProductionBodyImage
