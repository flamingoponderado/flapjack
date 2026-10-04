import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeAllocatorCaller
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoRegAllocCorrect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced

namespace Flapjack.WordAlloc
open RegAlloc RiscV RiscV.CakeRegAlloc Compiler.Encoders.Asm

/-- The actual native SSA caller produces a colouring satisfying the complete
native allocator checker contract. Forced membership comes from the source
program, and deterministic native execution identifies the allocator theorem's
colouring with the actual returned map. No desired allocation, colouring
validity or target evaluation is a premise. This implementation composition has
no separate HOL original; it does not assert full program state simulation. -/
theorem nativeAllocator_colouringContract {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (supported : allocatorMemorySupported source = true)
    (config : AsmConfigExact width) (target : config.isa = .riscv) :
    ∃ (output : CakeAllocationWithColour (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)) (livein flivein : NumSet),
      cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
        wordCopyPropViaHOL wordRemoveDeadProgramViaHOL wordRemoveUnreachViaHOL?
        wordFullSsaCcTransNativeWithState label parameters source = some output ∧
      wordLangProgToHOL output.program = some nativeOutput ∧
      wordLangProgToHOL output.colouredProgram =
        some (applyColour (totalColour (sptFromAList output.colouring)) nativeOutput) ∧
      checkClashTree (spDefault (sptFromAList output.colouring))
        (getClashTree nativeOutput []) .ln .ln = some (livein, flivein) ∧
      (∀ x, inClashTree (getClashTree nativeOutput []) x →
        sptDomain (sptFromAList output.colouring) x ∧
          if isPhyVar x then spDefault (sptFromAList output.colouring) x = x / 2
          else if isStackVar x then cakeRiscVRegisterCount ≤ spDefault (sptFromAList output.colouring) x
          else True) ∧
      (∀ x, sptDomain (sptFromAList output.colouring) x →
        inClashTree (getClashTree nativeOutput []) x) ∧
      ∀ pair ∈ getForced config nativeOutput [],
        spDefault (sptFromAList output.colouring) pair.1 =
          spDefault (sptFromAList output.colouring) pair.2 → pair.1 = pair.2 := by
  obtain ⟨output, nativeOutput, allocated, outputEncoded, nativeRun, colouredEncoded⟩ :=
    nativeAllocatorCaller_production label parameters source native encoded supported config target
  obtain ⟨colouring, livein, flivein, correctRun, checked, conventions, support, forced⟩ :=
    regAllocCorrect .IRC (getHeuristics 3 label nativeOutput).2 cakeRiscVRegisterCount
      (getHeuristics 3 label nativeOutput).1 (getClashTree nativeOutput [])
      (getForced config nativeOutput []) (getStackOnly nativeOutput)
      (getForcedInGetClashTree nativeOutput [] config)
  rw [nativeRun] at correctRun
  cases correctRun
  exact ⟨output, nativeOutput, livein, flivein, allocated, outputEncoded,
    colouredEncoded, checked, conventions, support, forced⟩

end Flapjack.WordAlloc
