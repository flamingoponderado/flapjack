module

public import Flapjack.RiscV.Allocator
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

@[expose] public section

/-! Kernel replay of fresh original colouring equations, plus full-domain
and guard sentinels. HOL has no production memory guard or five-register
AddCarry; those Flapjack-only boundaries are tested explicitly. -/
namespace Flapjack.Test.WordToStackColourDomainParity
open Flapjack

private def colour (name : Nat) := name + 10
end Flapjack.Test.WordToStackColourDomainParity
