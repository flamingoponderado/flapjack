import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign.Append

namespace Flapjack.Compiler.Backend.Parmove

/-- The literal scratch-safety insertion law: inserting a scratch write
`(SOME x, SOME y)` anywhere preserves scratch-safety. Source and destination
option carriers remain independently quantified, as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_insert"]
theorem notUseTempBeforeAssignInsert {destination source : Type}
    (first second : List (Option destination × Option source))
    (x : destination) (y : source) :
    notUseTempBeforeAssign (first ++ second) = true →
      notUseTempBeforeAssign (first ++ [(some x, some y)] ++ second) = true := by
  intro h
  have hf : notUseTempBeforeAssign first = true :=
    ((notUseTempBeforeAssignAppend first second).mp h).1
  have hs : (∀ move ∈ first, move.1.isSome = true) →
      notUseTempBeforeAssign second = true :=
    ((notUseTempBeforeAssignAppend first second).mp h).2
  rw [notUseTempBeforeAssignAppend]
  refine ⟨?_, ?_⟩
  · rw [notUseTempBeforeAssignAppend]
    exact ⟨hf, fun _ => rfl⟩
  · intro hall
    exact hs (fun move hm => hall move (by simp [hm]))

end Flapjack.Compiler.Backend.Parmove
