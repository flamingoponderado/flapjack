import Flapjack.Compiler.Backend.WordAlloc.ProductionCutsetContext
import Flapjack.Compiler.Backend.WordAlloc.ProductionCallInputs
import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper
import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
import Flapjack.RiscV.SpillCosts

namespace Flapjack.WordAlloc
open RiscV Compiler.Encoders.Asm

/-! Actual heuristic input producer. Untagged implementation correspondence:
getPrefs already carries its reviewed HOL reference. The real accepted program
encoder supplies recursive native children; accumulator and move order remain
arbitrary, including exception-before-return handler traversal. -/

end Flapjack.WordAlloc
