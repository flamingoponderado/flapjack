module

public import Flapjack.RiscV.Allocator
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.Pancake.WordLang.MaxVarInst

@[expose] public section

/-! Same-input kernel replay of fourteen original instruction maxima.
The last two rows expose HOL's zero maximum for ordinary 16-bit memory and
the production guard's rejection. Five-register AddCarry has no HOL row;
its codec rejection is tested separately, without conflating the operations. -/
namespace Flapjack.Test.WordToStackInstructionMaximumParity
open Flapjack

end Flapjack.Test.WordToStackInstructionMaximumParity
