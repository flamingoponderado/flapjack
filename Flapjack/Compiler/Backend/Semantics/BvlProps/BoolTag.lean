module

public import Flapjack.Compiler.Backend.BackendCommon.BoolTags
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
public import Flapjack.HolRef

@[expose] public section

/-!
# Boolean tag and Boolean value injectivity in HOL `bvlProps`

Counterpart of `cakeml/compiler/backend/semantics/bvlPropsScript.sml:176-190`:
`bool_to_tag_11` and `Boolv_11`.
-/

namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Compiler.Backend.BvlSem

/-- The Boolean tag is injective. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "bool_to_tag_11"]
theorem boolToTag_eq_iff (b1 b2 : Bool) : boolToTag b1 = boolToTag b2 ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;> simp [boolToTag, trueTag, falseTag]

/-- The Boolean value encoding is injective. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "Boolv_11"]
theorem boolValue_eq_iff (b1 b2 : Bool) : boolValue b1 = boolValue b2 ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;> simp [boolValue, boolToTag, trueTag, falseTag]

end Flapjack.Compiler.Backend.BvlProps
