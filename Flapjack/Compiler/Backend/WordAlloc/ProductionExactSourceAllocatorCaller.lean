import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeAllocatorCaller
import Flapjack.Pancake.LoopToWord.ProductionAllocatorMemoryImage

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc RegAlloc Flapjack.Compiler.Encoders.Asm

/-- Every exact Loop-to-Word function image obtains the actual routed allocator
result and a matching native IRC colouring/coloured encoder. All decoder,
encoder, memory-domain, SSA and allocator availability facts are source-derived;
no desired target execution, output support or allocator success is assumed.
The actual allocator formal list is an explicit input. This implementation
correspondence has no HOL original; formal mapping and full spill-state/location
semantics remain separate obligations, not narrowed HOL hypotheses. -/
theorem exactSourceAllocatorCaller_production {width : Nat} [NeZero width]
    (name : Nat) (parameters : List Nat) (source : HolLoopProg width)
    (allocatorParameters : List Nat)
    (config : AsmConfigExact width) (target : config.isa = .riscv) :
    ∃ (compiled : WordProg (BitVec width))
        (output : CakeAllocationWithColour (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)),
      wordLangProgFromHOL (loopToWordCompFuncHOL name parameters source) = some compiled ∧
      cakeAllocateWordFunctionAfterDeadRoutedSSA name allocatorParameters compiled = some output.toLegacy ∧
      wordLangProgToHOL output.program = some nativeOutput ∧
      regAlloc .IRC (getHeuristics 3 name nativeOutput).2 cakeRiscVRegisterCount
        (getHeuristics 3 name nativeOutput).1 (getClashTree nativeOutput [])
        (getForced config nativeOutput []) (getStackOnly nativeOutput) =
          .success (sptFromAList output.colouring) ∧
      wordLangProgToHOL output.colouredProgram =
        some (applyColour (totalColour (sptFromAList output.colouring)) nativeOutput) := by
  obtain ⟨compiled, decoded, supported, accepted⟩ :=
    LoopToWord.compFuncAllocatorMemoryDomain name parameters source
  cases encoded : wordLangProgToHOL compiled with
  | none => simp [encoded] at accepted
  | some native =>
      obtain ⟨output, nativeOutput, allocated, outputEncoded, nativeRun, colouredEncoded⟩ :=
        nativeAllocatorCaller_production name allocatorParameters compiled native encoded supported config target
      have routed : cakeAllocateWordFunctionAfterDeadRoutedSSA name allocatorParameters compiled =
          some output.toLegacy := by
        rw [cakeAllocateWordFunctionAfterDeadRoutedSSA_native name allocatorParameters compiled accepted]
        simp [cakeAllocateWordFunctionAfterDeadNativeSSA, allocated]
      exact ⟨compiled, output, nativeOutput, decoded, routed, outputEncoded, nativeRun, colouredEncoded⟩

end Flapjack.WordAlloc
