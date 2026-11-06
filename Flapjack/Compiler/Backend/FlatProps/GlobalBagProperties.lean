import Flapjack.Compiler.Backend.FlatProps.Globals

/-! Properties of the flat global-initialization bag. -/
namespace Flapjack.Compiler.Backend.FlatProps

/-- A union of natural-number bags is empty exactly when both inputs are. -/
theorem unionGlobalBag_eq_empty (left right : GlobalBag) :
    unionGlobalBag left right = emptyGlobalBag ↔ left = emptyGlobalBag ∧ right = emptyGlobalBag := by
  constructor
  · intro empty
    constructor <;> funext key
    · have h := congrFun empty key
      simp only [unionGlobalBag, emptyGlobalBag] at h ⊢
      omega
    · have h := congrFun empty key
      simp only [unionGlobalBag, emptyGlobalBag] at h ⊢
      omega
  · rintro ⟨rfl, rfl⟩
    funext key
    simp [unionGlobalBag, emptyGlobalBag]

/-- An expression list has an empty global bag exactly when every member's
global bag is empty. The expression carriers remain pending HOL review. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "elist_globals_eq_empty"]
theorem elistGlobals_eq_empty (expressions : List FlatLang.Exp) :
    elistGlobals expressions = emptyGlobalBag ↔
      ∀ expression ∈ expressions, setGlobals expression = emptyGlobalBag := by
  induction expressions with
  | nil => simp [elistGlobals]
  | cons first rest ih => simp [elistGlobals, unionGlobalBag_eq_empty, ih]

end Flapjack.Compiler.Backend.FlatProps
