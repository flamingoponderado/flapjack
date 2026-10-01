import Flapjack.Compiler.Backend.Parmove.SourceMembership

namespace Flapjack.Compiler.Backend.Parmove

/-- Real sources in the actual lifted/reversed scheduler output originate in
its input moves. Arbitrary moves are allowed, including duplicate destinations. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_SND_parmove"]
theorem memMapSndParmove {α : Type} [DecidableEq α]
    (moves : List (α × α)) (x : α)
    (member : some x ∈ (parmove moves).map Prod.snd) :
    x ∈ moves.map Prod.snd := by
  have output : some x ∈
      (pmov (moves.map (fun move => (some move.1, some move.2)), [], [])).2.2.map Prod.snd := by
    simpa [parmove, List.map_reverse] using member
  have input := memMapSndSndSndPmov
    (moves.map (fun move => (some move.1, some move.2)), [], []) x output
  simpa [List.map_map, Function.comp_def] using input

end Flapjack.Compiler.Backend.Parmove
