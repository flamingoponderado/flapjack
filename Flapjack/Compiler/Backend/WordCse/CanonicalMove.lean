import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData

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

/-- Complete actual move-update transport on all five knowledge fields.
Input observation correspondence alone is used; both output maps and guard
branches are derived. This Flapjack API theorem has no independent HOL original
and is not the still-open full CSE evaluation or production routing theorem. -/
theorem canonicalMoveRegs_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (moves : List (Nat × Nat)) :
    KnowledgeRel width (canonicalMoveRegs native moves) (wordCseCanonicalMoveRegs executed moves) := by
  let nativeRead := registerReads native (moves.map Prod.snd)
  let executedRead := wordCseRegisterReads executed (moves.map Prod.snd)
  have reads : KnowledgeRel width nativeRead executedRead :=
    registerReads_transport native executed related _
  have guard : (moves.map Prod.fst).all (keepData nativeRead.toCanonical) =
      moves.all (fun move => wordCseKeepData executedRead move.1) := by
    rw [List.all_map]
    congr 1
    funext move
    exact keepData_transport nativeRead executedRead reads move.1
  have canonical :
      (moves.filter (fun move => move.1 % 2 != 0 && move.2 % 2 != 0)).map
        (fun move => (move.1, canonicalRegs nativeRead move.2)) =
      (moves.filter (fun move => move.1 % 2 != 0 && move.2 % 2 != 0)).map
        (fun move => (move.1, wordCseCanonicalRegs executedRead move.2)) := by
    apply List.map_congr_left
    intro move _
    rw [canonicalRegs_transport nativeRead executedRead reads move.2]
  unfold canonicalMoveRegs wordCseCanonicalMoveRegs
  change KnowledgeRel width
    (if (moves.map Prod.fst).all (keepData nativeRead.toCanonical) then _ else _)
    (if moves.all (fun move => wordCseKeepData executedRead move.1) then _ else _)
  rw [guard]
  split
  · dsimp only
    rw [canonical]
    exact ⟨mapInsert_transport _ _ reads.1 _,
      mapInsert_transport _ _ reads.2.1 _, reads.2.2⟩
  · exact emptyKnowledgeRel width

end Flapjack.Compiler.Backend.WordCse
