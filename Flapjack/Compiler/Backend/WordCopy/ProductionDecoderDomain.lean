module

public import Flapjack.Compiler.Backend.WordCopy
public import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain

@[expose] public section

namespace Flapjack.Compiler.Backend.WordCopy
open Flapjack WordUnreach

/-! Actual decoder-image infrastructure for native copy propagation. These
have no separate HOL original. The instruction/program clauses are those of
the reviewed pass; decoder acceptance is preserved rather than assumed for its
output. Whole production caller adoption remains open. -/

end Flapjack.Compiler.Backend.WordCopy
