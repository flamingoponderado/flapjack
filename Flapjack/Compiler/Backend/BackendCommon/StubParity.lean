module

public import Mathlib.Tactic
public import Flapjack.Compiler.Backend.BackendCommon

@[expose] public section

/-!
# Stub-count parity

HOL's recursive `EVEN` predicate on the `backend_common` stub constants. This is
a leaf module because `Even` comes from Mathlib: the `BackendCommon` hub stays
free of Mathlib-reaching imports (see the task-201 note).
-/

namespace Flapjack

/-- HOL `data_num_stubs_EVEN` (`backend_commonScript.sml:144`):
    `EVEN data_num_stubs`, with the three stub constants reducing to `62`. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "data_num_stubs_EVEN"]
theorem dataNumStubsEven : Even dataNumStubs := by
  norm_num [dataNumStubs, wordNumStubs, stackNumStubs]

end Flapjack
