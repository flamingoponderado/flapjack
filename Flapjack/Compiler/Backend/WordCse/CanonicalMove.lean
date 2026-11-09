module

public import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData

@[expose] public section

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Original parallel-move knowledge update: track sources before checking
destinations, retain only odd/odd pairs, then insert canonical and inverted
bindings tail first. Self-interference and repeated keys retain source behavior. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "canonicalMoveRegs_def"]
def canonicalMoveRegs (data : Knowledge) (moves : List (Nat × Nat)) : Knowledge :=
  let data := registerReads data (moves.map Prod.snd)
  if (moves.map Prod.fst).all (keepData data.toCanonical) then
    let tracked := moves.filter (fun move => move.1 % 2 != 0 && move.2 % 2 != 0)
    let canonical := tracked.map (fun move => (move.1, canonicalRegs data move.2))
    let toCanonical := mapInsert canonical data.toCanonical
    let inverted := canonical.map (fun move => (move.2, move.1))
    let toLatest := mapInsert inverted data.toLatest
    {data with toCanonical := toCanonical, toLatest := toLatest}
  else emptyData

end Flapjack.Compiler.Backend.WordCse
