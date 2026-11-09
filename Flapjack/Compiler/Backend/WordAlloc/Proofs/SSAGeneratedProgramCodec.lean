module

public import Flapjack.Compiler.Backend.WordAlloc.SSAHelpers
public import Flapjack.Pancake.LoopToWord

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-! These are Flapjack carrier-boundary lemmas, without independent HOL originals.
They prove decoder availability for complete native SSA helper outputs; they do
not establish the full pass simulation or switch its production caller. -/

end Flapjack.Compiler.Backend.WordAlloc
