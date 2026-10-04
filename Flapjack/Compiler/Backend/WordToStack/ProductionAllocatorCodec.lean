import Flapjack.Compiler.Backend.WordToStack.ProductionSsaCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionDeadCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionCseCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionThreeToTwoDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionUnreachCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain
import Flapjack.RiscV.WordCopyCodecDomain
import Flapjack.RiscV.WordDeadCode

namespace Flapjack
open RiscV RiscV.CakeRegAlloc

/-- Flapjack-specific composition in the exact executed allocator order.
This is a codec acceptance implication, not equality: dead/unreachable
elimination can remove a rejected instruction. No output acceptance is assumed. -/
private theorem allocatorStagesCodec {width : Nat} [WordCseHash (BitVec width)] (parameters : List Nat)
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveDeadProgram
      (wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
        (wordCopyProp (wordCseProp (wordRemoveDeadProgram
          (wordFullSsaCcTrans parameters.length program).2.2))))))).isSome = true := by
  apply wordLangProgToHOL_wordRemoveDeadProgram_isSome
  apply wordLangProgToHOL_wordRemoveUnreachableAfterCopy_isSome
  rw [wordLangProgToHOL_wordThreeToTwoReg_isSome, wordCopyProp_codecDomain,
    wordLangProgToHOL_wordCseProp_isSome]
  apply wordLangProgToHOL_wordRemoveDeadProgram_isSome
  rw [wordLangProgToHOL_wordFullSsaCcTrans_isSome]
  exact accepted

/-- The real retained allocator output has an accepted native codec whenever
its input does. The successful allocation equation binds the actual output;
it does not assume a desired output codec, evaluation, maximum or colouring.
Initial source-to-Word acceptance is a separate obligation. This caller
infrastructure has no HOL theorem tag and is not allocator correctness. -/
theorem retainedAllocator_programCodec {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true)
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output) :
    (wordLangProgToHOL output.program).isSome = true := by
  have stages := allocatorStagesCodec parameters program accepted
  unfold cakeAllocateWordFunctionAfterDeadWithColour
    cakeAllocateWordFunctionAfterDeadWithColourFromLimit
    cakeAllocateWordFunctionAfterDeadWithColourFromLimitWith
    cakeAllocateWordFunctionAfterDeadWithColourWithSsa
    cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at allocated
  simp only [Option.bind_some] at allocated
  repeat' (split at allocated <;> simp_all)
  all_goals rcases allocated with ⟨_, _, _, rfl⟩
  all_goals exact stages

/-- Existential native encoding of the actual coloured result, derived from
the input codec and actual allocator result. Arbitrary real allocator colours
are used directly, with no reconstructed colour or output-codec premise.
This does not establish native ABI/configuration/body output correspondence,
or execute the native compiler in production. -/
theorem retainedAllocator_colouredCodec {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true)
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output) :
    ∃ native, wordLangProgToHOL output.colouredProgram = some native := by
  have encoded : (wordLangProgToHOL output.colouredProgram).isSome = true := by
    rw [CakeAllocationWithColour.colouredProgram,
      wordLangProgToHOL_wordApplyColour_isSome]
    exact retainedAllocator_programCodec label parameters program accepted output allocated
  cases h : wordLangProgToHOL output.colouredProgram with
  | none => simp [h] at encoded
  | some native => exact ⟨native, rfl⟩

end Flapjack
