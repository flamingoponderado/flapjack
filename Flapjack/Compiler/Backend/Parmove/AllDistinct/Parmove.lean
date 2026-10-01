import Flapjack.Compiler.Backend.Parmove.AllDistinct.Pmov
import Mathlib.Data.List.Nodup

namespace Flapjack.Compiler.Backend.Parmove

/-- Full HOL wrapper theorem: distinct input destinations imply distinct
real output destinations. Sources may repeat, self-moves and cycles are allowed,
and scratch destinations are filtered exactly as in the original statement. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "ALL_DISTINCT_parmove"]
theorem allDistinctParmove {α : Type} [DecidableEq α] (moves : List (α × α)) :
    (moves.map Prod.fst).Nodup →
      (((parmove moves).map Prod.fst).filter Option.isSome).Nodup := by
  intro distinct
  let lifted : List (Move α) := moves.map (fun move => (some move.1, some move.2))
  have liftedDistinct : (lifted.map Prod.fst).Nodup := by
    simpa [lifted, List.map_map, Function.comp_def] using
      (List.Nodup.map (f := Option.some) (by intro a b h; exact Option.some.inj h) distinct)
  have valid : wf (lifted, [], ([] : List (Move α))) := by
    apply wf_init
    refine ⟨liftedDistinct, ?_, ?_⟩
    · intro move member
      obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp member
      rfl
    · intro move member
      obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp member
      rfl
  have output := allDistinctPmov (lifted, [], ([] : List (Move α)))
    ⟨valid, by simpa only [List.append_nil] using liftedDistinct.filter Option.isSome⟩
  have emitted : (((pmov (lifted, [], [])).2.2.map Prod.fst).filter Option.isSome).Nodup := by
    simp only [List.map_append, List.filter_append, List.nodup_append] at output
    exact output.2.1
  simpa [parmove, lifted, List.map_reverse, List.filter_reverse] using emitted

end Flapjack.Compiler.Backend.Parmove
