import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

/-! Flapjack-only allocator-domain infrastructure for routing the executed
unreachable-code pass. The native pass retains instruction leaves, so it cannot
introduce an instruction the executed allocator rejects. These are codec and
runtime-domain facts, not HOL pass-correctness ports or evaluation premises. -/

namespace Flapjack.Compiler.Backend.WordUnreach

open Flapjack

end Flapjack.Compiler.Backend.WordUnreach
