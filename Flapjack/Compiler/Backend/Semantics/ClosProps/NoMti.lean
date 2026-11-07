import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Closure-language syntax admitted before multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosProps

mutual
/-- The original pre-multi-argument syntax invariant. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "no_mti_def"]
def noMti : ClosLang.Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => noMti a ∧ noMti b ∧ noMti c
  | .let _ bindings body => noMtiList bindings ∧ noMti body
  | .raise _ body | .tick _ body => noMti body
  | .handle _ a b => noMti a ∧ noMti b
  | .call .. => False
  | .app _ loc fn args => args.length = 1 ∧ loc = none ∧ noMtiList args ∧ noMti fn
  | .fn _ loc vars count body => count = 1 ∧ loc = none ∧ vars = none ∧ noMti body
  | .letrec _ loc vars bindings body =>
      noMti body ∧ loc = none ∧ vars = none ∧ noMtiFuns bindings
  | .op _ _ args => noMtiList args
termination_by exp => sizeOf exp

/-- List helper for HOL EVERY no_mti. -/
def noMtiList : List ClosLang.Exp → Prop
  | [] => True
  | e :: es => noMti e ∧ noMtiList es
termination_by es => sizeOf es

/-- List helper for the original letrec arity and body predicate. -/
def noMtiFuns : List (Nat × ClosLang.Exp) → Prop
  | [] => True
  | (arity, body) :: rest => arity = 1 ∧ noMti body ∧ noMtiFuns rest
termination_by fs => sizeOf fs
end

/-- The structural helper is the original EVERY over expressions. -/
theorem noMtiList_iff (xs : List ClosLang.Exp) :
    noMtiList xs ↔ ∀ e ∈ xs, noMti e := by
  induction xs with
  | nil => simp [noMtiList]
  | cons x xs ih => simp [noMtiList, ih]

/-- The letrec helper is the original EVERY over arities and function bodies. -/
theorem noMtiFuns_iff (fs : List (Nat × ClosLang.Exp)) :
    noMtiFuns fs ↔ ∀ f ∈ fs, f.1 = 1 ∧ noMti f.2 := by
  induction fs with
  | nil => simp [noMtiFuns]
  | cons f fs ih =>
    obtain ⟨arity, body⟩ := f
    simp [noMtiFuns, ih, and_assoc]

end Flapjack.Compiler.Backend.ClosProps
