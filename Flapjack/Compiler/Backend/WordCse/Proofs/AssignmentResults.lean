import Flapjack.Compiler.Backend.WordCse.Proofs.InsertEquality
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

namespace Flapjack.Compiler.Backend.WordCse.AssignmentResults
open Flapjack WordSemStateFiniteExact

/-! Flapjack-specific factoring of the assignment-result reasoning repeated
inside the original CSE proofs. These helpers have no separate HOL declaration.
Callers discharge the instruction/value equation from actual native `inst`
clauses; it is never an extra premise of a tagged CSE simulation theorem. -/

theorem setVarValueEqIff {width : Nat} [NeZero width] {C : Type} {F : Type}
    (d : Nat) (v1 v2 : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    setVar d v1 s = setVar d v2 s ↔ v1 = v2 := by
  constructor
  · intro h
    exact (insertEq d v1 v2 s.locals).mp (congrArg (fun st => st.locals) h)
  · intro h
    cases h
    rfl

theorem evaluationAssignmentIff {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (d : Nat) (value : Option (WordLocW width))
    (s : WordSemStateFiniteExact width C F) (w : WordLocW width)
    (hi : inst i s = value.map (fun v => setVar d v s)) :
    evaluate (.inst i) s = (none, setVar d w s) ↔ value = some w := by
  cases value <;> simp [evaluate, hi, setVarValueEqIff]

end Flapjack.Compiler.Backend.WordCse.AssignmentResults
