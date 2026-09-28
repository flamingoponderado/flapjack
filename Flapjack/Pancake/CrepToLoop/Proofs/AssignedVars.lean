import Flapjack.Pancake.Semantics.LoopProps.AssignedVars
import Flapjack.Pancake.Semantics.LoopProps

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
      (holLoopNestedSeq
        (les.mapIdx (fun index expression =>
          HolLoopProg.assign (index + offset) expression))) =
      (List.range les.length).map (fun index => index + offset) := by
  induction les generalizing offset with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [List.mapIdx_cons, List.length_cons]
      rw [List.range_succ_eq_map]
      simp [holLoopNestedSeq, holLoopAssignedVars, ih, Nat.add_assoc,
        Nat.add_comm 1 offset]

/-- Exact HOL `survives_MAPi_Assign`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:368-379`): every
    variable survives a nested sequence of the assignments built for
    `offset, …, offset + count - 1`. `mapIdx` renders HOL's `MAPi`, and the
    exact `survivesHOLExact` in `LoopProps.lean` renders HOL `survives`. The
    HOL `bool` conclusion is kept as `= true`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml"
  "survives_MAPi_Assign" (words_as_type_indexed_bitvec)]
theorem holSurvivesMapiAssign {width : Nat} [NeZero width]
    (name : Nat) (les : List (HolLoopExp width)) (offset : Nat) :
    survivesHOLExact name
      (holLoopNestedSeq
        (les.mapIdx (fun index expression =>
          HolLoopProg.assign (index + offset) expression))) = true := by
  induction les generalizing offset with
  | nil => simp [holLoopNestedSeq, survivesHOLExact]
  | cons expression expressions ih =>
      rw [List.mapIdx_cons]
      rw [show (fun (index : Nat) (expression : HolLoopExp width) =>
            HolLoopProg.assign (index + 1 + offset) expression) =
          (fun (index : Nat) (expression : HolLoopExp width) =>
            HolLoopProg.assign (index + (offset + 1)) expression) by
        funext index expression
        congr 1
        omega]
      simp only [holLoopNestedSeq, survivesHOLExact, Bool.true_and]
      rw [ih (offset + 1)]

end Flapjack
