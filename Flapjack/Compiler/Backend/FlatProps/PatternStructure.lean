import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Misc.Option.Rel

/-! Structural properties of flat constructors and pattern bindings. -/
namespace Flapjack.Compiler.Backend.FlatProps

/-- Constructor types agree exactly when the optional type components agree. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "ctor_same_type_OPTREL"]
theorem ctorSameType_optionRel {α β : Type} (left right : Option (α × β)) :
    FlatSem.ctorSameType left right ↔
      Flapjack.optionRel (fun x y => x.2 = y.2) left right := by
  cases left <;> cases right <;> simp [FlatSem.ctorSameType, Flapjack.optionRel]

/-- Pattern lists collect each pattern's bindings in reverse pattern order. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pats_bindings_FLAT_MAP"]
theorem patsBindings_flat_reverse_map (patterns : List FlatLang.Pat) :
    FlatLang.patsBindings patterns = (patterns.map FlatLang.patBindings).reverse.flatten := by
  induction patterns with
  | nil => rfl
  | cons pattern rest ih => simp [FlatLang.patsBindings, ih]

end Flapjack.Compiler.Backend.FlatProps
