import Flapjack.Compiler.Backend.WordRemove.Production
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAOutputCodec
import Flapjack.Compiler.Backend.WordToStack.ProductionSourceFlat

/-! Codec closure at the actual retained allocator-to-WordRemove boundary.
These producer invariants have no HOL originals and are not pass-correctness
ports. The allocation equation identifies the actual returned tuple; an output
codec premise or target execution is never assumed. -/
namespace Flapjack.RiscV
open CakeRegAlloc

/-- An accepted source input uses native SSA; every actual retained allocator
result is encodable. The broader rejected-input extension is kept separate. -/
theorem routedAllocator_programCodec {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (source : (wordLangProgToHOL program).isSome = true)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSA name parameters program = some output) :
    (wordLangProgToHOL output.2.2.1).isSome = true := by
  rw [cakeAllocateWordFunctionAfterDeadRoutedSSA_native name parameters program source] at allocated
  unfold cakeAllocateWordFunctionAfterDeadNativeSSA at allocated
  obtain ⟨retained, produced, same⟩ := Option.map_eq_some_iff.mp allocated
  subst output
  exact nativeSsaRetainedAllocator_programCodec name parameters program retained produced

/-- Every executed Loop source function supplies the input codec itself, so
legacy allocator fallback is unreachable for this source-provenance route.
No source/output codec, allocation availability or memory guard is assumed. -/
theorem sourceAllocator_programCodec {width : Nat} [NeZero width]
    (name : Nat) (parameters allocatorParameters : List Nat)
    (body : LoopProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSA name allocatorParameters
      (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) = some output) :
    (wordLangProgToHOL output.2.2.1).isSome = true :=
  routedAllocator_programCodec name allocatorParameters _ output
    (executedSourceAllocatorInput_isSome name parameters body) allocated

/-- The actual allocator result discharges the WordRemove guard, eliminating
its codec-rejection branch for source-produced functions. Real allocation
failure and the broad five-register AddCarry extension remain unchanged. -/
theorem sourceAllocator_wordRemove_isSome {width : Nat} [NeZero width]
    (name : Nat) (parameters allocatorParameters : List Nat)
    (body : LoopProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSA name allocatorParameters
      (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) = some output) :
    (wordRemoveMustTerminateViaHOL? output.2.2.1).isSome = true :=
  wordRemoveMustTerminateViaHOL?_isSome _
    (sourceAllocator_programCodec name parameters allocatorParameters body output allocated)

/-- Native decoded source rows discharge the FromWord caller guard. This is
carrier closure, not allocation availability or downstream correctness. -/
theorem decodedSourceAllocator_wordRemove_isSome {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat)
    (native : WordLangProgHOL (BitVec width)) (body : WordProg (BitVec width))
    (decoded : wordLangProgFromHOL native = some body)
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSA name parameters
      (wordBeforeSsaAllocatorBody body) = some output) :
    (wordRemoveMustTerminateViaHOL? output.2.2.1).isSome = true := by
  have accepted : (wordLangProgToHOL body).isSome = true := by
    rw [wordLangProgToHOL_of_fromHOL native body decoded]
    rfl
  exact wordRemoveMustTerminateViaHOL?_isSome _
    (routedAllocator_programCodec name parameters _ output
      (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body accepted) allocated)

end Flapjack.RiscV
