import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAAllocation
import Flapjack.Compiler.Backend.WordToStack.ProductionDeadCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionCseCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionThreeToTwoDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionUnreachCodecDomain
import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain
import Flapjack.RiscV.WordCopyCodecDomain

namespace Flapjack
open RiscV RiscV.CakeRegAlloc

/-- Successful native metadata decoding re-encodes the entire actual SSA
program, up to the reviewed cutset normalization. No output acceptance premise
is assumed; this is Flapjack carrier infrastructure, not a HOL theorem port. -/
theorem wordFullSsaCcTransNativeWithStateFromHOL_outputCodec
    {width : Nat} [NeZero width] (count : Nat)
    (native : WordLangProgHOL (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some output) :
    (wordLangProgToHOL output.2.2).isSome = true := by
  unfold wordFullSsaCcTransNativeWithStateFromHOL at produced
  cases decoded : wordLangProgFromHOL
      (Compiler.Backend.WordAlloc.fullSsaCcTransWithMetadata count native).program with
  | none => simp [decoded] at produced
  | some body =>
      simp only [decoded, Option.map_some, Option.some.injEq] at produced
      subst output
      have encoded := wordLangProgToHOL_of_fromHOL _ body decoded
      simp [encoded]

/-- Both native dead-code success and the explicit broad fallback preserve an
accepted input codec. This proves carrier closure, not evaluator equivalence. -/
theorem wordRemoveDeadProgramViaHOL_outputCodec {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveDeadProgramViaHOL program)).isSome = true := by
  unfold wordRemoveDeadProgramViaHOL
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at accepted
  | some native =>
      simp only [Option.bind_some]
      cases decoded : wordLangProgFromHOL (WordAlloc.removeDeadProg native) with
      | none =>
          exact wordLangProgToHOL_wordRemoveDeadProgram_isSome program accepted
      | some body =>
          have reencoded := wordLangProgToHOL_of_fromHOL _ body decoded
          simp [reencoded]

/-- Codec closure in the actual native allocator cleanup order, with both
reviewed native dead-code routers. Flapjack production infrastructure. -/
theorem nativeAllocatorStagesCodec {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordRemoveDeadProgramViaHOL
      (wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
        (wordCopyProp (wordCseProp (wordRemoveDeadProgramViaHOL program))))))).isSome = true := by
  apply wordRemoveDeadProgramViaHOL_outputCodec
  apply wordLangProgToHOL_wordRemoveUnreachableAfterCopy_isSome
  rw [wordLangProgToHOL_wordThreeToTwoReg_isSome, wordCopyProp_codecDomain,
    wordLangProgToHOL_wordCseProp_isSome]
  exact wordRemoveDeadProgramViaHOL_outputCodec program accepted

/-- Encoder closure for the actual native SSA retained allocator output. The
allocation equation binds the actual returned program; it does not supply a
desired output codec or target evaluation. This is not HOL pass correctness. -/
theorem nativeSsaRetainedAllocator_programCodec {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters program = some output) :
    (wordLangProgToHOL output.program).isSome = true := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourNativeSSA at allocated
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at allocated
  | some native =>
      simp only [encoded, Option.bind_some] at allocated
      unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsa at allocated
      split at allocated
      · simp_all
      · cases produced : wordFullSsaCcTransNativeWithStateFromHOL parameters.length native with
        | none => simp [produced] at allocated
        | some result =>
            rcases result with ⟨state, formals, body⟩
            have accepted := wordFullSsaCcTransNativeWithStateFromHOL_outputCodec
              parameters.length native (state, formals, body) produced
            have stages := nativeAllocatorStagesCodec body accepted
            simp only [produced, Option.bind_some] at allocated
            repeat' (split at allocated <;> simp_all)
            all_goals rcases allocated with ⟨_, _, _, rfl⟩
            all_goals exact stages

/-- The actual native retained colouring result also has a native encoding;
colouring is the real allocator result, with no reconstructed colour premise. -/
theorem nativeSsaRetainedAllocator_colouredCodec {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (allocated : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters program = some output) :
    ∃ native, wordLangProgToHOL output.colouredProgram = some native := by
  have accepted : (wordLangProgToHOL output.colouredProgram).isSome = true := by
    rw [CakeAllocationWithColour.colouredProgram, wordLangProgToHOL_wordApplyColour_isSome]
    exact nativeSsaRetainedAllocator_programCodec label parameters program output allocated
  cases encoded : wordLangProgToHOL output.colouredProgram with
  | none => simp [encoded] at accepted
  | some native => exact ⟨native, rfl⟩

end Flapjack
