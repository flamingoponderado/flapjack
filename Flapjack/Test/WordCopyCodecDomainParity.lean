module

public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

@[expose] public section

/-! Same-input kernel replay of original copy-propagation observations, plus
Flapjack-only five-register AddCarry and nested codec rejection sentinels. -/
namespace Flapjack.Test.WordCopyCodecDomainParity
open Flapjack RiscV
end Flapjack.Test.WordCopyCodecDomainParity
