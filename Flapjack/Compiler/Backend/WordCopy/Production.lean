import Flapjack.Compiler.Backend.WordCopy.ProductionDecoderDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramCodec
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.RiscV.Allocator
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap

namespace Flapjack.RiscV
open Compiler.Backend

/-! Fixed-width production routing through the reviewed copyProp definition.
There is no independent HOL declaration for this carrier adapter. Input codec
rejection preserves the broader executable extension; on the source image,
the actual decoder result is returned using a proved availability obligation.
There is no output fallback or supplied successful-decoder premise. -/

end Flapjack.RiscV
