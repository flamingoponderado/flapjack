module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Measure

@[expose] public section

/-! Membership bounds for Flapjack's flat-evaluator termination measure. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- A list member has less weight than its containing expression list. -/
theorem expWeight_lt_expsWeight (expressions : List FlatLang.Exp) (expression : FlatLang.Exp)
    (member : expression ∈ expressions) : expWeight expression < expsWeight expressions := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [expsWeight]
    rcases member with rfl | member
    · omega
    · have bound := ih member
      omega

/-- A row body has less weight than its containing pattern-row list. -/
theorem rowsWeight_member (rows : List (FlatLang.Pat × FlatLang.Exp))
    (pattern : FlatLang.Pat) (body : FlatLang.Exp) (member : (pattern, body) ∈ rows) :
    expWeight body < rowsWeight rows := by
  induction rows with
  | nil => simp at member
  | cons row rest ih =>
    obtain ⟨p, e⟩ := row
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp [rowsWeight]
      omega
    · have bound := ih member
      simp [rowsWeight]
      omega

end Flapjack.Compiler.Backend.FlatSem
