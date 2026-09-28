import Flapjack.Pancake.CrepToLoop.Proofs.AssignedVars
import Flapjack.Pancake.Semantics.LoopProps

namespace Flapjack

/-- Exact HOL `survives_MAPi_Assign` from
    `crep_to_loopProofScript.sml:368-379`. The binders remain in HOL order:
    `n`, then the expression list `les`, then `offset`; HOL's inferred
    `les` type is a list of `loopLang$exp` at the same word dimension used by
    the program. `mapIdx` renders HOL `MAPi`, and the exact `HolLoopProg`
    `nested_seq` carrier is used. The conclusion retains HOL's Boolean
    equation `survives ... = T`, rendered as `= true`, without a length or
    other premise. The only representation qualifier is HOL's positive
    type-indexed word dimension to `BitVec width`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml"
  "survives_MAPi_Assign" (words_as_type_indexed_bitvec)]
theorem holSurvivesMapiAssign {width : Nat} [NeZero width]
    (n : Nat) (les : List (HolLoopExp width)) (offset : Nat) :
    survivesHOLExact n
      (holLoopNestedSeq
        (les.mapIdx (fun index expression =>
          HolLoopProg.assign (index + offset) expression))) = true := by
  induction les generalizing offset with
  | nil => simp [holLoopNestedSeq, survivesHOLExact]
  | cons expression expressions ih =>
      simp only [List.mapIdx_cons]
      simp [holLoopNestedSeq, survivesHOLExact, ih, Nat.add_assoc,
        Nat.add_comm 1 offset]

end Flapjack
