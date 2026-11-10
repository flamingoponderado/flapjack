module

public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

/-! Kernel applications at the actual BitVec caller boundary. These are
carrier/guard certificates; native program-max correspondence and compiler
simulation remain separate obligations. Original executable output is checked
by the source-to-RISC-V corpus, rather than a second Lean implementation. -/
namespace Flapjack.Test.RetainedAllocatorColour
open Flapjack Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc

end Flapjack.Test.RetainedAllocatorColour
