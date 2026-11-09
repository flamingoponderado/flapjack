module

public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.Pancake.LoopToWord

@[expose] public section

/-! Flapjack-only representation infrastructure for the executed Word decoder.
The native unreachable-code pass retains instruction leaves, so it cannot
introduce an unsupported instruction into a decoder-accepted program. These
are codec-domain facts, not HOL pass-correctness ports or evaluation premises.
-/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

end Flapjack.Compiler.Backend.WordUnreach
