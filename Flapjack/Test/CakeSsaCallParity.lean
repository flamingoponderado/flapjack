module

public import Flapjack.RiscV.Allocator
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

/-! Direct Cake parity for the returning `Call` equations in
    `cakeml/compiler/backend/word_allocScript.sml:494-535`.  These cases were
    intentionally kept separate from the return-free call guard: Cake refreshes
    the cut set and allocates a fresh return destination before emitting the call.
    The exact expected shape below was obtained from the canonical HOL probe
    `cake_call_probeScript.sml` using `full_ssa_cc_trans`. -/

namespace Flapjack.Test.CakeSsaCallParity

open Flapjack

end Flapjack.Test.CakeSsaCallParity
