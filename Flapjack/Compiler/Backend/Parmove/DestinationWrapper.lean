import Flapjack.Compiler.Backend.Parmove.DestinationMembership

namespace Flapjack.Compiler.Backend.Parmove

/-- Full source public-wrapper real-destination membership. The scratch
register `none` is excluded by the source's `some x` premise; arbitrary input
moves, including duplicate destinations, retain the original one-way result.
No windmill, termination, successful scheduling or output-shape premise occurs. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "MEM_MAP_FST_parmove"]
theorem memMapFstParmove {α : Type} [DecidableEq α] (moves : List (α × α)) (x : α) :
    some x ∈ (parmove moves).map Prod.fst → x ∈ moves.map Prod.fst := by
  intro hx
  have hp := memMapFstSndSndPmov
    (moves.map (fun move => (some move.1, some move.2)), [], []) x
    (by simpa only [parmove, List.map_reverse, List.mem_reverse] using hx)
  simpa only [List.append_nil, List.map_map, Function.comp_def, List.mem_map,
    Option.some.injEq] using hp

end Flapjack.Compiler.Backend.Parmove
