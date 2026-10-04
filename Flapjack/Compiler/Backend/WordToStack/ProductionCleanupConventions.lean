import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Conventions
import Flapjack.Compiler.Backend.WordAlloc.ProductionCopyOutputCodec
import Flapjack.Compiler.Backend.WordCse.ProductionAllocatorInput
import Flapjack.Compiler.Backend.WordAlloc.ProductionThreeToTwoIdentity
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output

namespace Flapjack.ProductionCleanupConventions
open RiscV WordConvs Compiler.Backend

/-- A real decoded native program supplies both original allocator-input
conventions. This is a derived producer invariant, not a pass simulation or
successful target-run assumption. No separate HOL declaration exists. -/
def NativeInput {width : Nat} [NeZero width] (program : WordProg (BitVec width)) : Prop :=
  ∃ native, wordLangProgFromHOL native = some program ∧
    preAllocConventionsHOL native = true ∧ flatExpConventions native = true

/-- The actual encoder normalizes cutset trees while preserving both complete
native predicates; syntactic native tree equality is not assumed. -/
theorem NativeInput.encoded {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (input : NativeInput program) :
    ∃ native, wordLangProgToHOL program = some native ∧
      preAllocConventionsHOL native = true ∧ flatExpConventions native = true := by
  obtain ⟨native, decoded, pre, flat⟩ := input
  exact ⟨wordLangProgNormalizeCutsets native, wordLangProgToHOL_of_fromHOL native program decoded,
    by simpa only [preAllocConventionsHOL_normalizeCutsets] using pre,
    by simpa only [flatExpConventions_normalizeCutsets] using flat⟩

/-- Actual full SSA metadata decoding supplies the whole original pre-allocation
convention. Flatness is the genuine original input guard, supplied by the
executed instruction selector at the caller. -/
theorem nativeSsa_input {width : Nat} [NeZero width]
    (count : Nat) (native : WordLangProgHOL (BitVec width))
    (result : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some result)
    (flat : flatExpConventions native = true) : NativeInput result.2.2 := by
  unfold wordFullSsaCcTransNativeWithStateFromHOL at produced
  obtain ⟨body, decoded, same⟩ := Option.map_eq_some_iff.mp produced
  subst result
  refine ⟨WordAlloc.fullSsaCcTrans count native, ?_, WordAlloc.fullSsaCcTrans_preAllocConventions count native,
    WordAlloc.fullSsaCcTrans_flatExpConventions native count flat⟩
  simpa only [WordAlloc.fullSsaCcTransWithMetadata_program] using decoded

/-- Actual dead-code routing preserves both native conventions and derives its
output decoder result; no output fallback or relation is assumed. -/
theorem dead_input {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (input : NativeInput program)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) :
    NativeInput (wordRemoveDeadProgramViaHOL program) := by
  obtain ⟨native, encoded, pre, flat⟩ := input.encoded program
  obtain ⟨output, decoded, same⟩ := Flapjack.WordAlloc.wordRemoveDeadProgramViaHOL_sourceNative program native encoded
  refine ⟨Flapjack.WordAlloc.removeDeadProg native, ?_, ?_, ?_⟩
  · simpa only [same] using decoded
  · exact (removeDeadProgConventions (fun _ => true) native config).2.2.1 pre
  · exact (removeDeadProgConventions (fun _ => true) native config).1 flat

/-- The optimized actual CSE implementation returns the complete reviewed
native result on its decoded producer image; both conventions follow from the
original preservation theorems. -/
theorem cse_input {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (input : NativeInput program) :
    NativeInput (wordCseProp program) := by
  obtain ⟨native, decoded, pre, flat⟩ := input
  exact ⟨WordCse.wordCommonSubexpElim native,
    WordCse.wordCommonSubexpElim_production_transport native program decoded,
    WordCse.pre_alloc_conventions_word_common_subexp_elim native pre,
    flat_exp_conventions_word_common_subexp_elim native flat⟩

/-- The executed native copy adapter derives its full output and preserves the
original conventions, without assuming any successful output. -/
theorem copy_input {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (input : NativeInput program) :
    NativeInput (wordCopyPropViaHOL program) := by
  obtain ⟨native, encoded, pre, flat⟩ := input.encoded program
  obtain ⟨output, decoded, same⟩ := wordCopyPropViaHOL_sourceNative program native encoded
  refine ⟨WordCopy.copyProp native, ?_, pre_alloc_conventions_copy_prop native pre,
    flat_exp_conventions_copy_prop native flat⟩
  simpa only [same] using decoded

/-- Actual RISC-V three-to-two cleanup is identity on this derived flat input,
so both original conventions and the whole decoder result are retained. -/
theorem threeToTwo_input {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (input : NativeInput program) :
    NativeInput (wordThreeToTwoReg program) := by
  obtain ⟨native, encoded, pre, flat⟩ := input.encoded program
  rw [WordProgCarrierCodec.productionFlat_codec program native encoded] at flat
  rw [Flapjack.WordAlloc.wordThreeToTwoReg_flat_identity program flat]
  exact input

/-- Actual unreachable cleanup success identifies its returned program. The
native pass proves its own complete stack and flat conventions. -/
theorem unreach_input {width : Nat} [NeZero width]
    (program output : WordProg (BitVec width)) (input : NativeInput program)
    (produced : wordRemoveUnreachViaHOL? program = some output) : NativeInput output := by
  obtain ⟨native, encoded, pre, flat⟩ := input.encoded program
  have decoded : wordLangProgFromHOL (WordUnreach.removeUnreach native) = some output := by
    simpa only [wordRemoveUnreachViaHOL?, encoded, Option.bind_some] using produced
  exact ⟨WordUnreach.removeUnreach native, decoded,
    preAllocConventions_removeUnreach native pre, flatExpConventions_removeUnreach native flat⟩

/-- Complete actual retained allocator input has the original stack and ABI
conventions. Source encoding and selector flatness are genuine input guards;
the allocation equation only identifies the real returned value. -/
theorem routedAllocator_input {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (flat : flatExpConventions native = true)
    (config : Compiler.Encoders.Asm.AsmConfigExact width)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy
      name parameters program = some output) : NativeInput output.2.2.1 := by
  unfold CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at allocated
  simp only [encoded] at allocated
  obtain ⟨retained, produced, same⟩ := Option.map_eq_some_iff.mp allocated
  subst output
  change NativeInput retained.program
  unfold CakeRegAlloc.cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at produced
  split at produced
  · simp_all
  · cases ssaRun : wordFullSsaCcTransNativeWithStateFromHOL parameters.length native with
    | none => simp [ssaRun] at produced
    | some result =>
        rcases result with ⟨state, formals, body⟩
        have ssaInput := nativeSsa_input parameters.length native (state, formals, body) ssaRun flat
        have before := threeToTwo_input _
          (copy_input _ (cse_input _ (dead_input body ssaInput config)))
        simp only [ssaRun, Option.bind_some] at produced
        repeat' (split at produced <;> simp_all)
        all_goals rcases produced with ⟨_, _, _, rfl⟩
        all_goals exact dead_input _ (unreach_input _ _ before (by assumption)) config

/-- The actual Loop function producer and selector discharge every source
codec/flat guard, and actual SSA plus cleanup discharge both native allocator
conventions. No final output convention or target execution is assumed. -/
theorem sourceAllocator_input {width : Nat} [NeZero width]
    (name : Nat) (parameters allocatorParameters : List Nat)
    (body : LoopProg (BitVec width))
    (config : Compiler.Encoders.Asm.AsmConfigExact width)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy
      name allocatorParameters
      (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) = some output) :
    NativeInput output.2.2.1 := by
  obtain ⟨native, encoded, flat⟩ := executedSourceAllocatorInput_nativeFlat name parameters body
  exact routedAllocator_input name allocatorParameters _ native encoded flat config output allocated

/-- Every accepted actual Word row obtains selector flatness and both native
allocator conventions. The flat guard is derived from the executed selector,
not assumed as a property of the row. -/
theorem acceptedWordRow_input {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (body : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL body).isSome = true)
    (config : Compiler.Encoders.Asm.AsmConfigExact width)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy
      name parameters (wordBeforeSsaAllocatorBody body) = some output) : NativeInput output.2.2.1 := by
  have available := wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted
  obtain ⟨native, encoded⟩ := Option.isSome_iff_exists.mp available
  have observed := wordBeforeSsaAllocatorBody_nativeFlat_map body
  have flat : flatExpConventions native = true := by
    simpa only [encoded, Option.map_some, Option.some.injEq] using observed
  exact routedAllocator_input name parameters _ native encoded flat config output allocated

/-- The actual executed panToWordCompileProg row producer supplies native codec
acceptance for every row, with source syntax as its only input. This closes the
FromWord allocator's source-image guard, without assuming an output preimage. -/
theorem panToWordRow_codec {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions) :
    (wordLangProgToHOL body).isSome = true := by
  simp only [panToWordCompileProg, panToWordCompileProgRouted, List.mem_map] at row
  obtain ⟨⟨sourceLabel, parameters, sourceBody⟩, member, same⟩ := row
  cases same
  exact wordLangProgToHOL_loopToWordCompFuncRouted_isSome sourceLabel parameters sourceBody

/-- At the actual FromWord row producer, source syntax/selection/SSA/cleanup
supply both native allocator conventions; no input or output guard is supplied. -/
theorem panToWordRow_input {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions)
    (config : Compiler.Encoders.Asm.AsmConfigExact width)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : CakeRegAlloc.cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy
      label (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) = some output) :
    NativeInput output.2.2.1 :=
  acceptedWordRow_input label _ body (panToWordRow_codec functions label arity body row)
    config output allocated

end Flapjack.ProductionCleanupConventions
