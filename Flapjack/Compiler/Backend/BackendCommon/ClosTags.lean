module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags

@[expose] public section

namespace Flapjack.Compiler.Backend.BackendCommon

/-- The constructor tag used for tuples. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "tuple_tag_def"]
def tupleTag : Nat := 0

/-- The constructor tag used for ordinary closures. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "closure_tag_def"]
def closureTag : Nat := 30

/-- The constructor tag used for partial applications. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "partial_app_tag_def"]
def partialAppTag : Nat := 31

/-- Reserve the two closure tags when moving source constructor tags to BVL. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "clos_tag_shift_def"]
def closTagShift (tag : Nat) : Nat := if tag < 30 then tag else tag + 2

/-- HOL `partial_app_tag_neq_closure_tag`: the partial-application tag is not
the closure tag. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "partial_app_tag_neq_closure_tag"]
theorem partialAppTag_ne_closureTag : partialAppTag ≠ closureTag := by
  decide

/-- HOL `clos_tag_shift_nil_tag`: the nil tag is below the reserved range. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "clos_tag_shift_nil_tag"]
theorem closTagShift_nilTag : closTagShift nilTag = nilTag := by
  decide

/-- HOL `clos_tag_shift_cons_tag`: the cons tag is below the reserved range. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "clos_tag_shift_cons_tag"]
theorem closTagShift_consTag : closTagShift consTag = consTag := by
  decide

/-- HOL `clos_tag_shift_inj`: the shift is injective. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "clos_tag_shift_inj"]
theorem closTagShift_injective (n1 n2 : Nat) (run : closTagShift n1 = closTagShift n2) :
    n1 = n2 := by
  unfold closTagShift at run
  split at run
  · split at run
    · omega
    · omega
  · split at run
    · omega
    · omega

end Flapjack.Compiler.Backend.BackendCommon
