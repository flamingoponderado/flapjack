module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMemoryGuard
public import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF
public import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicProgram
public import Flapjack.RiscV.OracleAllocator
public import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeCopyMemoryGuard
public import Flapjack.RiscV.PipelineDiagnostics
public import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.WordAllocCorrect

@[expose] public section

namespace Flapjack.WordAlloc
open RegAlloc RiscV RiscV.CakeRegAlloc Compiler.Encoders.Asm

/-- The source codec's established canonical-set invariant implies HOL's
cutset well-formedness. This is Flapjack proof factoring, not a separate port. -/
theorem allocatorSetsWf_cutsets {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf program) : wfCutsets program := by
  fun_induction WordAllocatorProgramSetsWf program <;>
    simp_all [wfCutsets, wfNames, StackOnlySetsWf]
  case case8 =>
    split at valid <;> simp_all [wfCutsets]
    split at valid <;> simp_all [wfCutsets, wfNames]

end Flapjack.WordAlloc
