module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch
public import Flapjack.Misc.ListEl

@[expose] public section
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
local instance : Nonempty FlatLang.Pat := ⟨.pany⟩
/-- Rows with identical pattern projections select the same binding and pattern,
with the selected body taken from the corresponding row. -/
@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "pmatch_rows_same_FST"]
theorem pmatchRows_sameFst {C F E E' : Type} [Nonempty E] [Nonempty E']
    (state : FlatSem.State C F) (value : FlatSem.Value) :
    ∀ (rows : List (FlatLang.Pat × E)) (rows' : List (FlatLang.Pat × E')),
      rows.map Prod.fst = rows'.map Prod.fst →
      match FlatSem.pmatchRows rows state value with
      | .typeError => FlatSem.pmatchRows rows' state value = .typeError
      | .noMatch => FlatSem.pmatchRows rows' state value = .noMatch
      | .match (bindings, pattern, body) => ∃ i, i < rows'.length ∧ holEl i rows = (pattern, body) ∧
          FlatSem.pmatchRows rows' state value = .match (bindings, holEl i rows') := by
  intro rows
  induction rows with
  | nil =>
    intro rows' eq
    cases rows' <;> simp_all [FlatSem.pmatchRows]
  | cons row rows ih =>
    intro rows' eq
    cases rows' with
    | nil => simp at eq
    | cons row' rows' =>
      obtain ⟨pattern, body⟩ := row
      obtain ⟨pattern', body'⟩ := row'
      simp only [List.map_cons, List.cons.injEq] at eq
      obtain ⟨rfl, eq⟩ := eq
      have tail := ih rows' eq
      cases head : FlatSem.pmatch state pattern value [] with
      | typeError => simp [FlatSem.pmatchRows, head]
      | noMatch =>
        simp only [FlatSem.pmatchRows, head]
        cases matchTail : FlatSem.pmatchRows rows state value with
        | typeError =>
          simp only [matchTail] at tail
          simp [tail]
        | noMatch => simpa [matchTail] using tail
        | «match» result =>
          obtain ⟨bindings, pat, b⟩ := result
          simp only [matchTail] at tail
          obtain ⟨i, bound, source, target⟩ := tail
          refine ⟨i + 1, by simpa using bound, ?_, ?_⟩
          · simpa [holEl] using source
          · simpa [holEl] using target
      | «match» bindings =>
        simp only [FlatSem.pmatchRows, head]
        cases matchTail : FlatSem.pmatchRows rows state value with
        | typeError =>
          simp only [matchTail] at tail
          simp [tail]
        | noMatch =>
          simp only [matchTail] at tail
          refine ⟨0, by simp, ?_, ?_⟩ <;> simp [tail, holEl, holHd]
        | «match» result =>
          obtain ⟨tailBindings, pat, b⟩ := result
          simp only [matchTail] at tail
          obtain ⟨i, bound, source, target⟩ := tail
          refine ⟨0, by simp, ?_, ?_⟩ <;> simp [target, holEl, holHd]
end Flapjack.Compiler.Backend.FlatPattern
