module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.HolRef

@[expose] public section

/-! Result-shape and length properties of the clocked closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL

namespace EvaluateShapePort
/-- Canonical closure-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateShapePort

/-- Successful evaluations return one value per expression, and successful
closure applications return a singleton. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_LENGTH" 606
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_LENGTH {C F : Type} :
    (∀ (p1 : List ClosLang.Exp) (p1' : List ClosSem.Value) (p2 : ClosSem.State C F),
      (match ClosSem.evaluate p1 p1' p2 with
       | (.val res, _) => p1.length = res.length
       | (.err _, _) => True)) ∧
    (∀ (v0 : Option Nat) (v1 : ClosSem.Value) (v2 : List ClosSem.Value)
      (v3 : ClosSem.State C F),
      (match ClosSem.evaluateApp v0 v1 v2 v3 with
       | (.val res, _) => res.length = 1
       | (.err _, _) => True)) := by
  constructor
  · intro p1 p1' p2
    cases run : ClosSem.evaluate p1 p1' p2 with
    | mk result next =>
      cases result with
      | val res => exact (ClosSem.evaluate_length.1 p1 p1' p2 next res run).symm
      | err error => trivial
  · intro v0 v1 v2 v3
    cases run : ClosSem.evaluateApp v0 v1 v2 v3 with
    | mk result next =>
      cases result with
      | val res => exact ClosSem.evaluate_length.2 v0 v1 v2 v3 next res run
      | err error => trivial

/-- A successful closure application returns a singleton value list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_IMP_LENGTH"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_imp_length {C F : Type} (x1 : Option Nat) (x2 : ClosSem.Value)
    (x3 : List ClosSem.Value) (x4 : ClosSem.State C F) (res : List ClosSem.Value)
    (s1 : ClosSem.State C F)
    (run : ClosSem.evaluateApp x1 x2 x3 x4 = (.val res, s1)) : res.length = 1 :=
  ClosSem.evaluate_length.2 x1 x2 x3 x4 s1 res run

/-- A successful evaluation returns as many values as expressions. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_length_imp"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_length_imp {C F : Type} (es : List ClosLang.Exp)
    (env : List ClosSem.Value) (s1 : ClosSem.State C F) (vs : List ClosSem.Value)
    (s2 : ClosSem.State C F)
    (run : ClosSem.evaluate es env s1 = (.val vs, s2)) : es.length = vs.length :=
  (ClosSem.evaluate_length.1 es env s1 s2 vs run).symm

/-- A successful closure application returns exactly one value. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_app_length_imp"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApp_length_imp {C F : Type} (l : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s : ClosSem.State C F) (vs : List ClosSem.Value)
    (s2 : ClosSem.State C F)
    (run : ClosSem.evaluateApp l f args s = (.val vs, s2)) : vs.length = 1 :=
  ClosSem.evaluate_length.2 l f args s s2 vs run

/-- Evaluation of an append sequences its left side first, propagating errors. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_append"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_append {C F : Type} (es1 es2 : List ClosLang.Exp)
    (env : List ClosSem.Value) (s : ClosSem.State C F) :
    ClosSem.evaluate (es1 ++ es2) env s =
      match ClosSem.evaluate es1 env s with
      | (.val vs1, s') =>
        match ClosSem.evaluate es2 env s' with
        | (.val vs2, s'') => (.val (vs1 ++ vs2), s'')
        | (.err e, s'') => (.err e, s'')
      | (.err e, s') => (.err e, s') :=
  evaluateAppend es1 es2 env s

/-- An evaluation returns the empty value list exactly for the empty expression
list with an unchanged state. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_eq_nil"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_eq_nil {C F : Type} (es : List ClosLang.Exp) (env : List ClosSem.Value)
    (s0 : ClosSem.State C F) (s : ClosSem.State C F) :
    ClosSem.evaluate es env s0 = (.val [], s) ↔ s0 = s ∧ es = [] := by
  constructor
  · intro run
    have len := ClosSem.evaluate_length.1 es env s0 s [] run
    have empty : es = [] := List.eq_nil_of_length_eq_zero len.symm
    subst es
    have same : s0 = s := by
      have pair :
          ((.val [] : Result (List ClosSem.Value) ClosSem.Value), s0) =
            ((.val [] : Result (List ClosSem.Value) ClosSem.Value), s) := by
        simpa [ClosSem.evaluate] using run
      exact congrArg Prod.snd pair
    exact ⟨same, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp [ClosSem.evaluate]

end Flapjack.Compiler.Backend.ClosProps
