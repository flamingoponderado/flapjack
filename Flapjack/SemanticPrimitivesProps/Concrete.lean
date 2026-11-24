module

public import Flapjack.SemanticPrimitivesHOL.Concrete
public import Flapjack.AstHOL.LitOp

@[expose] public section

/-! Characterizations of first-order source values. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

/-- The list fold of concrete-value testing is the universal predicate. HOL's
`EVERY` fold is the Lean `List.all` Boolean fold. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "concrete_v_list"]
theorem concreteValues_eq_all (xs : List Value) : concreteValues xs = xs.all concreteValue := by
  induction xs with
  | nil => simp [concreteValues]
  | cons value rest ih => simp [concreteValues, ih]

/-- The concrete-value cases, in HOL's order. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "concrete_v_simps"]
theorem concreteValue_cases (l : Lit) (b : Bool) (n : Nat) (stmp : Option Stamp)
    (xs : List Value) (id : SemEnv Value) (e : Nat × Nat) (e2 : SemEnv Value)
    (nm : VarN) (x : Flapjack.AstHOL.Exp) (e3 : SemEnv Value)
    (funs : List (VarN × VarN × Flapjack.AstHOL.Exp)) (nm2 : VarN) :
    concreteValue (.litv l) = true ∧ concreteValue (.loc b n) = true ∧
      concreteValue (.conv stmp xs) = xs.all concreteValue ∧
      concreteValue (.vectorv xs) = xs.all concreteValue ∧
      concreteValue (.env id e) = false ∧ concreteValue (.closure e2 nm x) = false ∧
      concreteValue (.recclosure e3 funs nm2) = false := by
  simp [concreteValue, concreteValues_eq_all]

end Flapjack.SemanticPrimitivesProps
