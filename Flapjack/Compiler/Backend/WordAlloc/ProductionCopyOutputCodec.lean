import Flapjack.Compiler.Backend.WordAlloc.ProductionCopyAllocation
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAOutputCodec
import Flapjack.Compiler.Backend.WordToStack.ProductionSourceFlat
import Flapjack.Compiler.Backend.WordRemove.Production

namespace Flapjack.RiscV
open CakeRegAlloc

/-- Accepted copy inputs retain the whole native result's encoder image.
This codec closure has no independent HOL original and assumes no successful
output decoder or target execution. -/
theorem wordCopyPropViaHOL_outputCodec {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (accepted : (wordLangProgToHOL program).isSome = true) :
    (wordLangProgToHOL (wordCopyPropViaHOL program)).isSome = true := by
  obtain ⟨native, encoded⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨output, decoded, same⟩ := wordCopyPropViaHOL_sourceNative program native encoded
  rw [same, wordLangProgToHOL_of_fromHOL _ output decoded]
  rfl

/-- Actual SSA and the preceding dead/CSE stages supply the copy adapter's
input encoder guard. No post-copy relation or successful target is assumed.
This is production carrier infrastructure, without a separate HOL original. -/
theorem nativeAllocatorCopyInput_codec {width : Nat} [NeZero width]
    (count : Nat) (native : WordLangProgHOL (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width))
    (produced : wordFullSsaCcTransNativeWithStateFromHOL count native = some output) :
    (wordLangProgToHOL (wordCseProp (wordRemoveDeadProgramViaHOL output.2.2))).isSome = true := by
  rw [wordLangProgToHOL_wordCseProp_isSome]
  exact wordRemoveDeadProgramViaHOL_outputCodec _
    (wordFullSsaCcTransNativeWithStateFromHOL_outputCodec count native output produced)

/-- The actual native-copy allocator result supplies the retained program's
codec guard. Only input provenance and the actual returned allocation tuple
are premises; no desired output codec is supplied. All failure branches of
the executed allocator remain present. Flapjack infrastructure. -/
theorem routedNativeCopyAllocator_programCodec {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (program : WordProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (source : (wordLangProgToHOL program).isSome = true)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy name parameters program = some output) :
    (wordLangProgToHOL output.2.2.1).isSome = true := by
  unfold cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy at allocated
  cases encoded : wordLangProgToHOL program with
  | none => simp [encoded] at source
  | some native =>
      simp only [encoded] at allocated
      obtain ⟨retained, produced, same⟩ := Option.map_eq_some_iff.mp allocated
      subst output
      change (wordLangProgToHOL retained.program).isSome = true
      unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at produced
      split at produced
      · simp_all
      · cases ssaRun : wordFullSsaCcTransNativeWithStateFromHOL parameters.length native with
        | none => simp [ssaRun] at produced
        | some result =>
            rcases result with ⟨state, formals, body⟩
            simp only [ssaRun, Option.bind_some] at produced
            repeat' (split at produced <;> simp_all)
            all_goals rcases produced with ⟨_, _, _, rfl⟩
            all_goals exact wordRemoveDeadProgramViaHOL_outputCodec (width := width) _ (wordRemoveUnreachViaHOL?_outputCodec _ _ (by assumption))

/-- Every actual Loop producer supplies the native-copy route's input guard
and its resulting WordRemove guard. Legacy codec rejection is unreachable on
this producer image; allocation availability is not asserted. -/
theorem sourceNativeCopyAllocator_wordRemove_isSome {width : Nat} [NeZero width]
    (name : Nat) (parameters allocatorParameters : List Nat)
    (body : LoopProg (BitVec width))
    (output : WordSsaState × List Nat × WordProg (BitVec width) × WordSpillState)
    (allocated : cakeAllocateWordFunctionAfterDeadRoutedSSAWithNativeCopy name allocatorParameters
      (wordBeforeSsaAllocatorBody (LoopToWord.loopToWordCompFunc name parameters body)) = some output) :
    (wordRemoveMustTerminateViaHOL? output.2.2.1).isSome = true :=
  wordRemoveMustTerminateViaHOL?_isSome _
    (routedNativeCopyAllocator_programCodec name allocatorParameters _ output
      (executedSourceAllocatorInput_isSome name parameters body) allocated)

/-- The shared consumer constructs its retained spill state from its actual
colouring and records the actual IRC run, for any copy/SSA/cleanup producers.
This derives producer equations; no desired colour map or simulation premise
is supplied. There is no separate HOL declaration for this API invariant. -/
theorem allocatorWithCopy_retained {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (copy dead : WordProg α → WordProg α)
    (unreach : WordProg α → Option (WordProg α))
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output) :
    output.allocation = cakeColourWordSpillState cakeRiscVRegisterCount
        parameters output.program output.colouring ∧
      cakeDoRegAlloc .irc
        ((wordGetHeuristics 3 label output.program).2.map
          (cakeSpillCostMap (cakeMkBij (wordClashTree output.program [])).nextNode))
        cakeRiscVRegisterCount
        ((wordGetHeuristics 3 label output.program).1.map
          (fun move => (move.priority, (move.left, move.right))))
        (wordClashTree output.program []) (cakeGetForced output.program)
        (cakeGetStackOnly output.program) = some output.colouring := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy at produced
  split at produced <;> simp_all
  cases ssaRun : ssa parameters.length source with
  | none => simp [ssaRun] at produced
  | some result =>
      rcases result with ⟨state, formals, body⟩
      simp only [ssaRun, Option.bind_some] at produced
      repeat' (split at produced <;> simp_all)
      all_goals rcases produced with ⟨_, _, _, rfl⟩
      all_goals simp_all [cakeDoRegAlloc]

end Flapjack.RiscV
