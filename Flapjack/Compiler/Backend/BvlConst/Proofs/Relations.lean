import Flapjack.Compiler.Backend.Semantics.BvlSem.Evaluate
import Flapjack.Compiler.Backend.BvlConst

/-! Relations needed for the constant-propagation semantic simulation.

These definitions follow the original value and environment relations but
are not tagged as HOL ports: the BVL evaluator they quantify over is still
pending source review, and the finite-map state is hidden in that quantifier.
The evaluator correspondence and representation qualification remain open.
-/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Relate one propagated expression to its source and transformed values. -/
noncomputable def valueRel (C F : Type) (expression : Bvl.Exp)
    (source target : Value) (_sourceEnv targetEnv : List Value) : Prop :=
  match expression with
  | .var index => targetEnv[index]? = some source
  | .op _ _ => source = target ∧
      ∀ (state : State C F) env, evaluate [expression] env state = (.val [source], state)
  | _ => False

/-- Relate environments using the optional constant-propagation annotations.
Unannotated suffixes must be identical, even after the annotation list ends. -/
noncomputable def envRel (C F : Type) : List (Option Bvl.Exp) → List Value → List Value → Prop
  | [], source, target => source = target
  | none :: rest, x :: source, y :: target =>
      x = y ∧ envRel C F rest source target
  | some expression :: rest, x :: source, y :: target =>
      valueRel C F expression x y (x :: source) (y :: target) ∧
        envRel C F rest source target
  | _, _, _ => False

/-- Related environments have equal length. This is untagged because its
relation inherits the unreviewed BVL evaluator and state representation. -/
theorem envRel_length (C F : Type) (annotations : List (Option Bvl.Exp))
    (source target : List Value) (related : envRel C F annotations source target) :
    target.length = source.length := by
  induction annotations generalizing source target with
  | nil => simpa [envRel] using congrArg List.length related.symm
  | cons annotation rest ih =>
    cases source with
    | nil => cases annotation <;> cases target <;> simp [envRel] at related
    | cons x source =>
      cases target with
      | nil => cases annotation <;> simp [envRel] at related
      | cons y target =>
        cases annotation <;> simp only [envRel] at related <;>
          simpa using congrArg Nat.succ (ih source target related.2)

/-- An annotated lookup yields the relation at the corresponding environment
suffixes. This follows the original lookup lemma but is untagged for the
same evaluator and state-representation review gap as `envRel`. -/
theorem envRel_lookup_some (C F : Type) (annotations : List (Option Bvl.Exp))
    (source target : List Value) (expression : Bvl.Exp) (index : Nat)
    (related : envRel C F annotations source target)
    (lookup : annotations[index]? = some (some expression)) :
    valueRel C F expression
      (@Flapjack.holEl Value ⟨unitValue⟩ index source)
      (@Flapjack.holEl Value ⟨unitValue⟩ index target)
      (source.drop index) (target.drop index) := by
  induction annotations generalizing source target index with
  | nil => simp at lookup
  | cons annotation rest ih =>
    cases source with
    | nil => cases annotation <;> cases target <;> simp [envRel] at related
    | cons x source =>
      cases target with
      | nil => cases annotation <;> simp [envRel] at related
      | cons y target =>
        cases index with
        | zero =>
          cases annotation with
          | none => simp at lookup
          | some a =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
            subst a
            simpa [envRel, Flapjack.holEl, Flapjack.holHd] using related.1
        | succ index =>
          cases annotation <;> simp only [envRel] at related <;>
            simp only [List.getElem?_cons_succ] at lookup <;>
            simpa [Flapjack.holEl] using ih source target index related.2 lookup

/-- Missing or empty annotations leave the selected values equal, including
the shared HOL out-of-range value. This is untagged pending the evaluator and
state-representation review recorded above. -/
theorem envRel_lookup_none (C F : Type) (annotations : List (Option Bvl.Exp))
    (source target : List Value) (index : Nat)
    (related : envRel C F annotations source target)
    (lookup : annotations[index]? = none ∨ annotations[index]? = some none) :
    @Flapjack.holEl Value ⟨unitValue⟩ index target =
      @Flapjack.holEl Value ⟨unitValue⟩ index source := by
  induction annotations generalizing source target index with
  | nil =>
    simp only [envRel] at related
    subst target
    rfl
  | cons annotation rest ih =>
    cases source with
    | nil => cases annotation <;> cases target <;> simp [envRel] at related
    | cons x source =>
      cases target with
      | nil => cases annotation <;> simp [envRel] at related
      | cons y target =>
        cases index with
        | zero =>
          cases annotation with
          | none => simpa [envRel, Flapjack.holEl, Flapjack.holHd] using related.1.symm
          | some a => simp at lookup
        | succ index =>
          cases annotation <;> simp only [envRel] at related <;>
            simp only [List.getElem?_cons_succ] at lookup <;>
            simpa [Flapjack.holEl] using ih source target index related.2 lookup

/-- Deleting a variable preserves every non-type-error singleton result.
This source-shaped lemma remains untagged while the BVL evaluator and its
finite-map state representation are under review. -/
theorem evaluate_deleteVar_error {C F : Type} (expression : Bvl.Exp)
    (state final : State C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value) (env : List Value)
    (run : evaluate [expression] env state = (.err error, final))
    (notTypeError : error ≠ .abort .typeError) :
    evaluate [BvlConst.deleteVar expression] env state = (.err error, final) := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none =>
      simp [evaluate, lookup] at run
      exact False.elim (notTypeError run.1.symm)
    | some value => simp [evaluate, lookup] at run
  | _ => simpa [BvlConst.deleteVar] using run

end Flapjack.Compiler.Backend.BvlConst.Proofs
