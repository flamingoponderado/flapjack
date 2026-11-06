import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Flat pattern-matching properties. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.AstHOL

/-- A selected row matches with the returned bindings and belongs to the input. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "pmatch_rows_IMP_pmatch"]
theorem pmatchRows_imp_pmatch {C F E : Type} (rows : List (FlatLang.Pat × E))
    (state : FlatSem.State C F) (value : FlatSem.Value)
    (bindings : List (VarN × FlatSem.Value)) (pattern : FlatLang.Pat) (body : E)
    (selected : FlatSem.pmatchRows rows state value = .match (bindings, pattern, body)) :
    FlatSem.pmatch state pattern value [] = .match bindings ∧ (pattern, body) ∈ rows := by
  induction rows with
  | nil => simp [FlatSem.pmatchRows] at selected
  | cons row rest ih =>
    obtain ⟨first, expression⟩ := row
    cases head : FlatSem.pmatch state first value [] with
    | typeError => simp [FlatSem.pmatchRows, head] at selected
    | noMatch =>
      have tail : FlatSem.pmatchRows rest state value = .match (bindings, pattern, body) := by
        simpa [FlatSem.pmatchRows, head] using selected
      obtain ⟨matched, member⟩ := ih tail
      exact ⟨matched, List.mem_cons_of_mem _ member⟩
    | «match» newBindings =>
      cases tail : FlatSem.pmatchRows rest state value <;>
        simp_all [FlatSem.pmatchRows]

end Flapjack.Compiler.Backend.FlatProps
