module

public import Flapjack.RiscV.WordToStack

@[expose] public section

/-!
Original oracle: scripts/hol-probes/word_to_stack_tail_handler_probeScript.sml,
word_to_stackScript.sml comp_def495-504. Original complete result equality
(including bitmap state) is T for direct/indirect calls and both perf modes.
These generic kernel regressions exercise the actual production functions,
not the proof-side native duplicate. No HOL tags: optimized production trees
and optional failure carriers require their separate correspondence proof.
-/
namespace Flapjack.Test.WordToStackTailHandlerParity
open Flapjack RiscV

end Flapjack.Test.WordToStackTailHandlerParity
