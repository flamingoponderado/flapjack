import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Source closure label and application-arity predicates. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosLang

mutual
/-- The source application-arity predicate on one expression. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "obeys_max_app_def" 3542]
def obeysMaxApp (m : Nat) : Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => obeysMaxApp m a ∧ obeysMaxApp m b ∧ obeysMaxApp m c
  | .let _ bindings body => obeysMaxAppList m bindings ∧ obeysMaxApp m body
  | .raise _ body | .tick _ body | .fn _ _ _ _ body => obeysMaxApp m body
  | .handle _ a b => obeysMaxApp m a ∧ obeysMaxApp m b
  | .call _ _ _ args | .op _ _ args => obeysMaxAppList m args
  | .app _ _ fn args => args.length ≤ m ∧ obeysMaxApp m fn ∧ obeysMaxAppList m args
  | .letrec _ _ _ bindings body => obeysMaxAppFuns m bindings ∧ obeysMaxApp m body
termination_by exp => sizeOf exp

/-- Source EVERY over expression lists; Flapjack structural infrastructure. -/
def obeysMaxAppList (m : Nat) : List Exp → Prop
  | [] => True
  | e :: es => obeysMaxApp m e ∧ obeysMaxAppList m es
termination_by es => sizeOf es

/-- Source EVERY over mapped recursive bodies; Flapjack structural infrastructure. -/
def obeysMaxAppFuns (m : Nat) : List (Nat × Exp) → Prop
  | [] => True
  | (_, body) :: rest => obeysMaxApp m body ∧ obeysMaxAppFuns m rest
termination_by fs => sizeOf fs
end

mutual
/-- The source predicate excluding label operations. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "no_Labels_def" 3566]
def noLabels : Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => noLabels a ∧ noLabels b ∧ noLabels c
  | .let _ bindings body => noLabelsList bindings ∧ noLabels body
  | .raise _ body | .tick _ body | .fn _ _ _ _ body => noLabels body
  | .handle _ a b => noLabels a ∧ noLabels b
  | .call _ _ _ args => noLabelsList args
  | .op _ op args => (∀ n, op ≠ .label n) ∧ noLabelsList args
  | .app _ _ fn args => noLabels fn ∧ noLabelsList args
  | .letrec _ _ _ bindings body => noLabelsFuns bindings ∧ noLabels body
termination_by exp => sizeOf exp

/-- Source EVERY over expression lists; Flapjack structural infrastructure. -/
def noLabelsList : List Exp → Prop
  | [] => True
  | e :: es => noLabels e ∧ noLabelsList es
termination_by es => sizeOf es

/-- Source EVERY over mapped recursive bodies; Flapjack structural infrastructure. -/
def noLabelsFuns : List (Nat × Exp) → Prop
  | [] => True
  | (_, body) :: rest => noLabels body ∧ noLabelsFuns rest
termination_by fs => sizeOf fs
end

/-- Flapjack infrastructure connecting the source EVERY traversal to membership. -/
theorem obeysMaxAppList_iff (m : Nat) (xs : List Exp) :
    obeysMaxAppList m xs ↔ ∀ e ∈ xs, obeysMaxApp m e := by
  induction xs with
  | nil => simp [obeysMaxAppList]
  | cons x xs ih => simp [obeysMaxAppList, ih]

/-- Flapjack infrastructure connecting mapped recursive bodies to source EVERY. -/
theorem obeysMaxAppFuns_eq_map (m : Nat) (fs : List (Nat × Exp)) :
    obeysMaxAppFuns m fs ↔ obeysMaxAppList m (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [obeysMaxAppFuns, obeysMaxAppList]
  | cons p fs ih => cases p; simp [obeysMaxAppFuns, obeysMaxAppList, ih]

/-- Flapjack infrastructure connecting the source EVERY traversal to membership. -/
theorem noLabelsList_iff (xs : List Exp) : noLabelsList xs ↔ ∀ e ∈ xs, noLabels e := by
  induction xs with
  | nil => simp [noLabelsList]
  | cons x xs ih => simp [noLabelsList, ih]

/-- Flapjack infrastructure connecting mapped recursive bodies to source EVERY. -/
theorem noLabelsFuns_eq_map (fs : List (Nat × Exp)) :
    noLabelsFuns fs ↔ noLabelsList (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [noLabelsFuns, noLabelsList]
  | cons p fs ih => cases p; simp [noLabelsFuns, noLabelsList, ih]

end Flapjack.Compiler.Backend.ClosProps
