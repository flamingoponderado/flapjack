import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapCaller
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

/-! Actual source allocator/WordRemove error-boundary facts. These are
production caller facts with no HOL semantic theorem tag. Arbitrary raw Word
extension inputs are distinct from source-produced rows. -/
namespace Flapjack.ProductionWordRemoveCaller
open RiscV RiscV.CakeRegAlloc ProductionCleanupConventions

/-- Actual source-row inputs satisfy the independently proved structural codec
domain. In particular they cannot select the raw five-register extension branch. -/
theorem sourceRow_supportsCodec {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions) :
    WordProgCarrierCodec.supportsCodec (wordBeforeSsaAllocatorBody body) = true := by
  rw [← WordProgCarrierCodec.codecDomain]
  exact wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body
    (panToWordRow_codec functions label arity body row)

/-- The precisely identified raw extension still selects the historical
allocator. This describes executed dispatch, not HOL correspondence for the
five-register primitive, and makes no guarantee about its eventual output codec. -/
theorem rawExtension_legacyDispatch {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (extension : WordProgCarrierCodec.supportsCodec program = false) :
    cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label parameters program =
      cakeAllocateWordFunctionAfterDead label parameters program := by
  have rejected : wordLangProgToHOL program = none := by
    have domain := WordProgCarrierCodec.codecDomain program
    rw [extension] at domain
    cases encoded : wordLangProgToHOL program with
    | none => rfl
    | some native => rw [encoded] at domain; cases domain
  simp only [cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy, rejected]

/-- Actual source rows select the native allocator branch itself, independently
of allocation success. No output encoder preimage or allocator run is assumed. -/
theorem sourceRow_nativeDispatch {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (label arity : Nat) (body : WordProg (BitVec width))
    (row : (label, arity, body) ∈ panToWordCompileProg functions) :
    ∃ native : WordLangProgHOL (BitVec width),
      wordLangProgToHOL (wordBeforeSsaAllocatorBody body) = some native ∧
      cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label (wordSsaAbiParameters arity)
        (wordBeforeSsaAllocatorBody body) =
      (cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy wordCopyPropViaHOL
        wordRemoveDeadProgramViaHOL wordRemoveUnreachViaHOL?
        (fun count _ => wordFullSsaCcTransNativeWithStateFromHOL count native)
        label (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body)).map
        CakeAllocationWithColour.toLegacy := by
  obtain ⟨native, encoded⟩ := Option.isSome_iff_exists.mp
    (wordLangProgToHOL_wordBeforeSsaAllocatorBody_isSome body
      (panToWordRow_codec functions label arity body row))
  exact ⟨native, encoded, by simp only [cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy, encoded]⟩

/-- An actual source-row allocation diagnostic comes from an allocator None,
not a rejected post-allocation WordRemove codec. Other lowering failures remain
distinct and no allocation availability or successful target run is assumed. -/
theorem sourceRows_allocationFailure {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (rows : List (Nat × Nat × WordProg (BitVec width)))
    (sourceRows : ∀ row ∈ rows, row ∈ panToWordCompileProg functions)
    (state : WordStackBitmapState) (chunks : List (List Nat)) (failedLabel : Nat)
    (failed : pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
      state chunks rows = .error (.allocationFailure failedLabel)) :
    ∃ arity body, (failedLabel, arity, body) ∈ rows ∧
      cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy failedLabel (wordSsaAbiParameters arity)
        (wordBeforeSsaAllocatorBody body) = none := by
  induction rows generalizing state chunks with
  | nil => simp only [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux] at failed; cases failed
  | cons head tail ih =>
    rcases head with ⟨label, arity, body⟩
    cases allocated : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy label
        (wordSsaAbiParameters arity) (wordBeforeSsaAllocatorBody body) with
    | none =>
      simp only [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux,
        allocated, Except.error.injEq, PipelineRiscVLoweringError.allocationFailure.injEq] at failed
      subst failedLabel
      exact ⟨arity, body, List.mem_cons_self, allocated⟩
    | some output =>
      have cleanup := ProductionBitmapCaller.panToWordRow_wordRemove_isSome
        functions label arity body (sourceRows _ List.mem_cons_self) output allocated
      obtain ⟨cleaned, removed⟩ := Option.isSome_iff_exists.mp cleanup
      simp only [pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux,
        allocated, removed] at failed
      split at failed
      · cases failed
      · split at failed
        · have recursiveFailed :
              pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
                _ _ tail = .error (.allocationFailure failedLabel) := Eq.trans (by assumption) failed
          obtain ⟨a, b, member, allocation⟩ := ih
            (fun row member => sourceRows row (List.mem_cons_of_mem _ member)) _ _ recursiveFailed
          exact ⟨a, b, List.mem_cons_of_mem _ member, allocation⟩
        · cases failed

/-- The public FromWord source caller's allocation diagnostic identifies an
actual failed allocator. This is the complete produced row list, with no
caller-supplied source-membership or successful lowering condition. -/
theorem sourceCaller_allocationFailure {width : Nat} [NeZero width]
    (functions : List (Nat × List Nat × LoopProg (BitVec width)))
    (state : WordStackBitmapState) (failedLabel : Nat)
    (failed : pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
      state (panToWordCompileProg functions) = .error (.allocationFailure failedLabel)) :
    ∃ arity body, (failedLabel, arity, body) ∈ panToWordCompileProg functions ∧
      cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy failedLabel (wordSsaAbiParameters arity)
        (wordBeforeSsaAllocatorBody body) = none := by
  unfold pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked at failed
  split at failed
  · have recursiveFailed :
        pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordCheckedAux
          state [state.data] (panToWordCompileProg functions) =
            .error (.allocationFailure failedLabel) := by
      simp only [Except.error.injEq] at failed
      simp_all only []
    exact sourceRows_allocationFailure functions _ (fun _ member => member) state _ _ recursiveFailed
  · cases failed

end Flapjack.ProductionWordRemoveCaller
