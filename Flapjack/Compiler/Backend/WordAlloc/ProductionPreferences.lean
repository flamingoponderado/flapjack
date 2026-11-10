module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionCutsetContext
public import Flapjack.Compiler.Backend.WordAlloc.ProductionCallInputs
public import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper
public import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
public import Flapjack.RiscV.SpillCosts

@[expose] public section

namespace Flapjack.WordAlloc
open RiscV Compiler.Encoders.Asm

/-! Actual heuristic input producer. Untagged implementation correspondence:
getPrefs already carries its reviewed HOL reference. The real accepted program
encoder supplies recursive native children; accumulator and move order remain
arbitrary, including exception-before-return handler traversal. -/

end Flapjack.WordAlloc
