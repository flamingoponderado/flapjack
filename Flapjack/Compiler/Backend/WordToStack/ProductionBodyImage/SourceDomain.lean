import Flapjack.Compiler.Backend.WordToStack.ProductionFrameCaller
import Flapjack.Compiler.Backend.WordToStack.ProductionColourDomain
import Flapjack.Compiler.Backend.WordAlloc.ProductionNormalizedMemoryGuard
import Flapjack.Compiler.Backend.WordUnreach.ProductionEncoderDomain

/-! Actual source-caller input domain for the native body decoder-image proof.
These are Flapjack compiler-carrier facts with no HOL originals. Actual allocator
guards and codecs supply the native input, without assumed target execution or
output decoding. The decoded production tree may normalize zero offsets, cutsets
and names; its literal equality to the pre-encoding tree is not asserted. -/

namespace Flapjack.ProductionBodyImage
open RiscV RiscV.CakeRegAlloc ProductionCleanupConventions
open Compiler.Backend Compiler.Encoders.Asm

/-- The shared executed allocator certifies its retained program directly from
its last memory-domain check, for arbitrary supplied cleanup and SSA stages. -/
theorem retainedAllocatorMemorySupported {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option
      (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output) :
    allocatorMemorySupported output.program = true := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at produced
  split at produced <;> simp_all
  simp only [Option.bind_eq_some_iff] at produced
  rcases produced with ⟨⟨state, formals, body⟩, _, produced⟩
  repeat' (split at produced <;> simp_all)
  all_goals rcases produced with ⟨_, checked, rfl⟩
  all_goals exact checked

/-- Real retained allocation and native source input derive both required
decoder-domain witnesses for the actual coloured input. Codec success and
memory support of the actual decoded tree are conclusions, not premises. -/
theorem retainedNativeDecoderDomain {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option
      (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : NativeInput output.program) :
    ∃ (native : WordLangProgHOL (BitVec width)) (decoded : WordProg (BitVec width)),
      wordLangProgToHOL output.colouredProgram = some native ∧
      wordLangProgFromHOL native = some decoded ∧
      allocatorMemorySupported decoded = true := by
  obtain ⟨before, encoded, _, _⟩ := input.encoded output.program
  have accepted : (wordLangProgToHOL output.colouredProgram).isSome = true := by
    rw [CakeAllocationWithColour.colouredProgram, wordLangProgToHOL_wordApplyColour_isSome]
    simp only [encoded, Option.isSome_some]
  obtain ⟨native, encoding⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨decoded, decoding⟩ := Option.isSome_iff_exists.mp
    (WordUnreach.wordLangProgFromHOL_of_toHOL_isSome output.colouredProgram native encoding)
  refine ⟨native, decoded, encoding, decoding, ?_⟩
  rw [WordAlloc.decodedMemoryGuard native decoded decoding,
    WordAlloc.memoryGuardProgram_production output.colouredProgram native encoding,
    CakeAllocationWithColour.colouredProgram, allocatorMemorySupported_wordApplyColour]
  exact retainedAllocatorMemorySupported copy dead unreach ssa label parameters source output produced

/-- The actual PanToWord source row and native-copy allocator supply the complete
native instruction domain, including nested return and exception continuations.
The source convention and both codec directions are derived internally. -/
theorem panToWordRowNativeDecoderDomain {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : AsmConfigExact width)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (produced : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
      (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output) :
    ∃ (retained : CakeAllocationWithColour (BitVec width))
      (native : WordLangProgHOL (BitVec width)) (decoded : WordProg (BitVec width)),
      retained.toLegacy = output ∧
      wordLangProgToHOL retained.colouredProgram = some native ∧
      wordLangProgFromHOL native = some decoded ∧
      allocatorMemorySupported decoded = true := by
  have input := panToWordRow_input functions label arity body row config output produced
  have accepted := panToWordRow_codec functions label arity body row
  obtain ⟨before, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted)
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at produced
  simp only [encoded] at produced
  obtain ⟨retained, actualRun, same⟩ := Option.map_eq_some_iff.mp produced
  subst output
  obtain ⟨native, decoded, encoding, decoding, supported⟩ :=
    retainedNativeDecoderDomain _ _ _ _ label (wordSsaAbiParameters arity)
      _ retained actualRun input
  exact ⟨retained, native, decoded, rfl, encoding, decoding, supported⟩

end Flapjack.ProductionBodyImage
