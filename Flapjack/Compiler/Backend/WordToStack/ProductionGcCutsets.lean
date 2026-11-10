module

public import Flapjack.RiscV.PipelineDiagnostics
public import Flapjack.Compiler.Backend.WordToStack.ProductionFlatCodec
public import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileConventions.Output
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashOccurrences
public import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport

@[expose] public section

namespace Flapjack.ProductionGcCutsets
open RiscV

/-- Checking every program name also checks the subset stored in cutsets.
This local consequence supplies the clash-tree predicate at actual GC sites;
it is infrastructure, with no separate HOL declaration asserted. -/
theorem everyVar_stackSubset {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (program : WordLangProgHOL (BitVec width))
    (checked : everyVarHOL predicate program = true) : everyStackVarHOL predicate program = true := by
  fun_induction everyStackVarHOL predicate program <;>
    simp_all [everyVarHOL, Bool.and_eq_true]
  case case4 target arguments handler values names body l1 l2 ihReturns ihHandler =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [everyVarHOL, Bool.and_eq_true]

end Flapjack.ProductionGcCutsets
