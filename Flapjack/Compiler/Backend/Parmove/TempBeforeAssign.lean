import Flapjack.Compiler.Backend.Parmove

namespace Flapjack.Compiler.Backend.Parmove

/-- Literal ordered predicate clauses. A scratch read is rejected before the
scratch-write clause, and a scratch write accepts immediately without scanning
its tail. Independent source and destination carriers are retained. No well-formedness condition is imposed on the move list. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "not_use_temp_before_assign_def"]
def notUseTempBeforeAssign {destination source : Type} :
    List (Option destination × Option source) → Bool
  | [] => true
  | (_, none) :: _ => false
  | (none, some _) :: _ => true
  | (some _, some _) :: tail => notUseTempBeforeAssign tail

end Flapjack.Compiler.Backend.Parmove
