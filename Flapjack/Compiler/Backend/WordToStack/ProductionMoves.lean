module

public import Flapjack.Compiler.Backend.WordToStack.NativeMoves
public import Flapjack.Compiler.Backend.MlStringBridge
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.RiscV.Lab

@[expose] public section

/-! Flapjack implementation correspondence for actual move materialization.
There is no HOL declaration for this production AST projection. The existing
macro leaf projection supplies register arithmetic; the shared structural codec
supplies all other leaves. This does not change the executed compiler.
Identity suppression and normalized sequencing differ from literal wMoveAux;
caller-domain and semantic obligations remain before whole-route replacement.
-/
namespace Flapjack.ProductionMoves
open RiscV Compiler.Backend Compiler.Backend.StackLang Compiler.Encoders.Asm

/-- Canonical image of the actual Skip-eliminating join. This normalization
is explicitly named; it is not HOL wMoveAux's literal constructor tree. -/
def join {width : Nat} [NeZero width] (first second : HolProg width) : HolProg width :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

end Flapjack.ProductionMoves
