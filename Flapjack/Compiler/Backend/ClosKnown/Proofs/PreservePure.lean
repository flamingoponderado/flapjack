import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
import Flapjack.Compiler.Backend.ClosOp.Proofs.ReductionInvariants

/-! Purity preservation for the known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.PreservePure
open ClosLang

/-- Purity of the source expression list implies purity of the optimized
expression list. This invariant supports the source traversal induction. -/
def PureInvariant (c : Config) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) : Prop :=
  pureList xs = true → pureList ((knownListTotal c xs env g).1.map Prod.fst) = true

private def exprInvariant (c : Config) (e : Exp) (env : List ValApprox) (g : Spt ValApprox) : Prop :=
  pure e = true → pure (knownExprTotal c e env g).1 = true

/-- The complete traversal preserves pure expressions. -/
theorem knownPureAll (c : Config) (xs : List Exp) (env : List ValApprox) (g : Spt ValApprox) :
    PureInvariant c xs env g := by
  induction c, xs, env, g using knownListTotal.induct
    (motive1 := exprInvariant)
    (motive2 := fun _ _ _ _ _ => True)
  all_goals try simp_all [PureInvariant, exprInvariant, knownListTotal, knownExprTotal, pureList, ClosLang.pure]
  case case8 =>
    rename_i c env g t op xs eas g1 hk a g2 ho ih
    intro input opPure
    have output := ih input
    split <;> simp_all [smartTotal_eq_smartOp, ClosOp.smartPure, ClosLang.pure, pureOp]
  case case12 =>
    rename_i c env g name loc vars arity body e a g1 hb ih
    cases loc <;> simp_all [knownExprTotal, ClosLang.pure]
  case case13 =>
    rename_i c env g names loc vars fns body clos e a g1 hb ih
    cases loc <;> dsimp [clos] at hb <;> simp_all [knownExprTotal, ClosLang.pure]

/-- The source list predicate agrees with pointwise purity. This is
Flapjack infrastructure for the source theorem. -/
theorem pureListIff (xs : List Exp) :
    pureList xs = true ↔ ∀ e ∈ xs, ClosLang.pure e = true := by
  induction xs with
  | nil => simp [pureList]
  | cons x xs ih => simp [pureList, ih]

/-- Known-function optimization preserves purity of every source expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_pure"]
theorem knownPreservesPure (c : Config) (es : List Exp) (env : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c es env g0 = (eas, g) ∧ ∀ e ∈ es, ClosLang.pure e = true) :
    ∀ e ∈ eas.map Prod.fst, ClosLang.pure e = true := by
  have result := knownPureAll c es env g0 ((pureListIff es).mpr h.2)
  rw [h.1] at result
  exact (pureListIff _).mp result

end Flapjack.Compiler.Backend.ClosKnown.PreservePure
