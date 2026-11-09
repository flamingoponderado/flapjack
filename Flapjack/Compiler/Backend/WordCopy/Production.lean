module

public import Flapjack.Compiler.Backend.WordCopy.ProductionDecoderDomain
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAProgramCodec
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.RiscV.Allocator
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap

@[expose] public section

namespace Flapjack.RiscV
open Compiler.Backend

/-! Fixed-width production routing through the reviewed copyProp definition.
There is no independent HOL declaration for this carrier adapter. Input codec
rejection preserves the broader executable extension; on the source image,
the actual decoder result is returned using a proved availability obligation.
There is no output fallback or supplied successful-decoder premise. -/

end Flapjack.RiscV
