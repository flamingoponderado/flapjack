import Flapjack.Pancake.Semantics.LoopProps.AssignedVars

/-!
Exact `crep_to_loopProofScript.sml` assigned-variable proof port, placed under
the Lean counterpart for the source proof script.
-/

namespace Flapjack

/-- Exact HOL `assigned_vars_MAPi_Assign`. `mapIdx` renders `MAPi`, and
    `List.range` followed by `map` renders `GENLIST`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml"
  "assigned_vars_MAPi_Assign" (words_as_type_indexed_bitvec)]
theorem holAssignedVarsMapiAssign {width : Nat} [NeZero width]
    (les : List (HolLoopExp width)) (offset : Nat) :
    holLoopAssignedVars
      (loopNestedSeqHOL
        (les.mapIdx (fun index expression =>
          HolLoopProg.assign (index + offset) expression))) =
      (List.range les.length).map (fun index => index + offset) := by
  induction les generalizing offset with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [List.mapIdx_cons, List.length_cons]
      rw [List.range_succ_eq_map]
      simp [loopNestedSeqHOL, holLoopAssignedVars, ih, Nat.add_assoc,
        Nat.add_comm 1 offset]

end Flapjack
