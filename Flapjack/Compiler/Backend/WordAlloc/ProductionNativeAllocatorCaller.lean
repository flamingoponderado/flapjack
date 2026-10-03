import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorCleanupMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAOutputCodec
import Flapjack.Compiler.Backend.WordAlloc.ProductionTotalColourOutput

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc RegAlloc Flapjack.Compiler.Encoders.Asm

/-- Construct the actual native-SSA allocator result from accepted source
encoding and the explicit existing production memory domain. SSA availability,
cleanup domains and IRC success are derived, not assumed as target results.
This implementation theorem has no HOL original. Source-image discharge of
the extra memory guard and faithful spill-state/location semantics remain
separate obligations; this is not a narrowed HOL allocation theorem. -/
theorem nativeAllocatorCaller_production {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (config : AsmConfigExact width) (target : config.isa = .riscv) :
    ∃ (output : CakeAllocationWithColour (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)),
      cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source = some output ∧
      wordLangProgToHOL output.program = some nativeOutput ∧
      regAlloc .IRC (getHeuristics 3 label nativeOutput).2 cakeRiscVRegisterCount
        (getHeuristics 3 label nativeOutput).1 (getClashTree nativeOutput [])
        (getForced config nativeOutput []) (getStackOnly nativeOutput) =
          .success (sptFromAList output.colouring) ∧
      wordLangProgToHOL output.colouredProgram =
        some (applyColour (totalColour (sptFromAList output.colouring)) nativeOutput) := by
  have available := wordFullSsaCcTransNativeWithState_domain parameters.length source
  simp only [wordFullSsaCcTransNativeWithState, encoded, Option.bind_some, Option.isSome_some] at available
  cases produced : wordFullSsaCcTransNativeWithStateFromHOL parameters.length native with
  | none => simp [produced] at available
  | some result =>
      rcases result with ⟨state, formals, body⟩
      have bodySupported : allocatorMemorySupported body = true :=
        (decodedSsaMemoryGuard_production parameters.length source native encoded _ produced).trans supported
      have bodyAccepted := wordFullSsaCcTransNativeWithStateFromHOL_outputCodec
        parameters.length native (state, formals, body) produced
      let beforeDead := wordRemoveUnreachableAfterCopy (wordThreeToTwoReg
        (wordCopyProp (wordCseProp (wordRemoveDeadProgramViaHOL body))))
      let cleanup := wordRemoveDeadProgramViaHOL beforeDead
      have beforeSupported : allocatorMemorySupported beforeDead = true := by
        apply unreachMemoryGuard
        rw [threeToTwoMemoryGuard, copyWrapperMemoryGuard]
        apply cseWrapperMemoryGuard
        exact routedRemoveDeadMemoryGuard body bodySupported
      have cleanupSupported : allocatorMemorySupported cleanup = true :=
        routedRemoveDeadMemoryGuard beforeDead beforeSupported
      have cleanupAccepted : (wordLangProgToHOL cleanup).isSome = true :=
        nativeAllocatorStagesCodec body bodyAccepted
      cases cleanupEncoded : wordLangProgToHOL cleanup with
      | none => simp [cleanupEncoded] at cleanupAccepted
      | some cleanupNative =>
          obtain ⟨colours, nativeRun, actualRun⟩ := allocatorWrapperFromCompleteActualInputs
            cleanup cleanupNative cleanupEncoded config target .IRC 3 label cakeRiscVRegisterCount
          simp only [cakeDoRegAlloc, Algorithm.toProduction, beforeDead, cleanup] at actualRun
          change cakeDoRegAllocFromState .irc _ cakeRiscVRegisterCount
            ((wordGetHeuristics 3 label cleanup).1.map (fun move => (move.priority, (move.left, move.right))))
            _ _ = some colours at actualRun
          let output : CakeAllocationWithColour (BitVec width) :=
            ⟨state, formals, cleanup,
              cakeColourWordSpillState cakeRiscVRegisterCount parameters cleanup colours, colours⟩
          have allocated : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source =
              some output := by
            simp [cakeAllocateWordFunctionAfterDeadWithColourNativeSSA,
              cakeAllocateWordFunctionAfterDeadWithColourWithSsa, encoded, supported, produced,
              bodySupported, beforeSupported, cleanupSupported, beforeDead, cleanup, output,
              actualRun]
          refine ⟨output, cleanupNative, allocated, cleanupEncoded, nativeRun, ?_⟩
          simpa only [output, CakeAllocationWithColour.colouredProgram, wordApplyTotalColour] using
            totalColourProgram_production colours cleanup cleanupNative cleanupEncoded

end Flapjack.WordAlloc
