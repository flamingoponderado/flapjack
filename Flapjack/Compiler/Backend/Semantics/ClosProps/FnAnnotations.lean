import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic

/-! Closure function-location and free-variable annotation predicates. -/
namespace Flapjack.Compiler.Backend.ClosProps

mutual
/-- Flapjack helper for the singleton cases of the function-location
predicate. -/
def fnLocationSomeExp : ClosLang.Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => fnLocationSomeExp a ∧ fnLocationSomeExp b ∧ fnLocationSomeExp c
  | .let _ bindings body => fnLocationSomeExp body ∧ everyFnLocationSome bindings
  | .raise _ body | .tick _ body => fnLocationSomeExp body
  | .handle _ a b => fnLocationSomeExp a ∧ fnLocationSomeExp b
  | .call _ _ _ args | .op _ _ args => everyFnLocationSome args
  | .app _ _ fn args => fnLocationSomeExp fn ∧ everyFnLocationSome args
  | .fn _ loc _ _ body => loc.isSome ∧ fnLocationSomeExp body
  | .letrec _ loc _ bindings body => loc.isSome ∧ fnLocationSomeFuns bindings ∧ fnLocationSomeExp body
termination_by exp => sizeOf exp

/-- Every function and recursive group has a present code location. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "every_Fn_SOME_def"]
def everyFnLocationSome : List ClosLang.Exp → Prop
  | [] => True
  | e :: es => fnLocationSomeExp e ∧ everyFnLocationSome es
termination_by es => sizeOf es

/-- Flapjack helper for the original predicate over mapped recursive bodies. -/
def fnLocationSomeFuns : List (Nat × ClosLang.Exp) → Prop
  | [] => True
  | (_, body) :: rest => fnLocationSomeExp body ∧ fnLocationSomeFuns rest
termination_by fs => sizeOf fs
end

/-- Flapjack infrastructure: the recursive-group helper equals the
predicate applied to the source's mapped function bodies. -/
theorem fnLocationSomeFuns_eq_map (fs : List (Nat × ClosLang.Exp)) :
    fnLocationSomeFuns fs ↔ everyFnLocationSome (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [fnLocationSomeFuns, everyFnLocationSome]
  | cons f fs ih =>
    obtain ⟨arity, body⟩ := f
    simp [fnLocationSomeFuns, everyFnLocationSome, ih]

mutual
/-- Flapjack helper for the singleton cases of the free-variable annotation
predicate. -/
def fnVarsSomeExp : ClosLang.Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => fnVarsSomeExp a ∧ fnVarsSomeExp b ∧ fnVarsSomeExp c
  | .let _ bindings body => fnVarsSomeExp body ∧ everyFnVarsSome bindings
  | .raise _ body | .tick _ body => fnVarsSomeExp body
  | .handle _ a b => fnVarsSomeExp a ∧ fnVarsSomeExp b
  | .call _ _ _ args | .op _ _ args => everyFnVarsSome args
  | .app _ _ fn args => fnVarsSomeExp fn ∧ everyFnVarsSome args
  | .fn _ _ vars _ body => vars.isSome ∧ fnVarsSomeExp body
  | .letrec _ _ vars bindings body => vars.isSome ∧ fnVarsSomeFuns bindings ∧ fnVarsSomeExp body
termination_by exp => sizeOf exp

/-- Every function and recursive group has a present captured-variable list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "every_Fn_vs_SOME_def"]
def everyFnVarsSome : List ClosLang.Exp → Prop
  | [] => True
  | e :: es => fnVarsSomeExp e ∧ everyFnVarsSome es
termination_by es => sizeOf es

/-- Flapjack helper for the original predicate over mapped recursive bodies. -/
def fnVarsSomeFuns : List (Nat × ClosLang.Exp) → Prop
  | [] => True
  | (_, body) :: rest => fnVarsSomeExp body ∧ fnVarsSomeFuns rest
termination_by fs => sizeOf fs
end

/-- Flapjack infrastructure: the recursive-group helper equals the
predicate applied to the source's mapped function bodies. -/
theorem fnVarsSomeFuns_eq_map (fs : List (Nat × ClosLang.Exp)) :
    fnVarsSomeFuns fs ↔ everyFnVarsSome (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [fnVarsSomeFuns, everyFnVarsSome]
  | cons f fs ih =>
    obtain ⟨arity, body⟩ := f
    simp [fnVarsSomeFuns, everyFnVarsSome, ih]

end Flapjack.Compiler.Backend.ClosProps
