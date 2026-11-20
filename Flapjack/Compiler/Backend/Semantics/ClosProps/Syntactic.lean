module

public import Flapjack.Compiler.Backend.ClosLang.Syntax

@[expose] public section

/-! Closure-language application and free-variable annotation properties. -/
namespace Flapjack.Compiler.Backend.ClosProps

mutual
/-- Flapjack helper for the singleton clauses of the application predicate. -/
def containsAppSomeExp (maxApp : Nat) : ClosLang.Exp → Prop
  | .var .. => False
  | .ifThenElse _ a b c => containsAppSomeExp maxApp a ∨ containsAppSomeExp maxApp b ∨ containsAppSomeExp maxApp c
  | .let _ bindings body => containsAppSomeExp maxApp body ∨ containsAppSome maxApp bindings
  | .raise _ body | .tick _ body | .fn _ _ _ _ body => containsAppSomeExp maxApp body
  | .handle _ a b => containsAppSomeExp maxApp a ∨ containsAppSomeExp maxApp b
  | .call _ _ _ args => containsAppSome maxApp args
  | .app _ loc fn args => loc.isSome ∨ maxApp < args.length ∨ containsAppSomeExp maxApp fn ∨ containsAppSome maxApp args
  | .letrec _ _ _ bindings body => containsAppSomeFuns maxApp bindings ∨ containsAppSomeExp maxApp body
  | .op _ (.thunkOp .forceThunk) args => maxApp < 1 ∨ containsAppSome maxApp args
  | .op _ _ args => containsAppSome maxApp args
termination_by exp => sizeOf exp

/-- Applications with known locations, excessive arity, or a force beyond
the configured maximum; this matches the original list-valued predicate. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "contains_App_SOME_def"]
def containsAppSome (maxApp : Nat) : List ClosLang.Exp → Prop
  | [] => False
  | e :: es => containsAppSomeExp maxApp e ∨ containsAppSome maxApp es
termination_by es => sizeOf es

/-- Flapjack helper for mapped recursive-function bodies. -/
def containsAppSomeFuns (maxApp : Nat) : List (Nat × ClosLang.Exp) → Prop
  | [] => False
  | (_, body) :: rest => containsAppSomeExp maxApp body ∨ containsAppSomeFuns maxApp rest
termination_by fs => sizeOf fs
end

/-- The function helper is the source's mapped body list. -/
theorem containsAppSomeFuns_eq_map (maxApp : Nat) (fs : List (Nat × ClosLang.Exp)) :
    containsAppSomeFuns maxApp fs = containsAppSome maxApp (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [containsAppSomeFuns, containsAppSome]
  | cons f fs ih =>
    obtain ⟨arity, body⟩ := f
    simp [containsAppSomeFuns, containsAppSome, ih]

mutual
/-- Flapjack helper for the singleton annotation clauses. -/
def fnVarsNoneExp : ClosLang.Exp → Prop
  | .var .. => True
  | .ifThenElse _ a b c => fnVarsNoneExp a ∧ fnVarsNoneExp b ∧ fnVarsNoneExp c
  | .let _ bindings body => fnVarsNoneExp body ∧ everyFnVarsNone bindings
  | .raise _ body | .tick _ body => fnVarsNoneExp body
  | .handle _ a b => fnVarsNoneExp a ∧ fnVarsNoneExp b
  | .call _ _ _ args | .op _ _ args => everyFnVarsNone args
  | .app _ _ fn args => fnVarsNoneExp fn ∧ everyFnVarsNone args
  | .fn _ _ vars _ body => vars = none ∧ fnVarsNoneExp body
  | .letrec _ _ vars bindings body => vars = none ∧ fnVarsNoneFuns bindings ∧ fnVarsNoneExp body
termination_by exp => sizeOf exp

/-- Every function and recursive binding has no captured-variable annotation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "every_Fn_vs_NONE_def"]
def everyFnVarsNone : List ClosLang.Exp → Prop
  | [] => True
  | e :: es => fnVarsNoneExp e ∧ everyFnVarsNone es
termination_by es => sizeOf es

/-- Flapjack helper for mapped recursive-function bodies. -/
def fnVarsNoneFuns : List (Nat × ClosLang.Exp) → Prop
  | [] => True
  | (_, body) :: rest => fnVarsNoneExp body ∧ fnVarsNoneFuns rest
termination_by fs => sizeOf fs
end

/-- Absent captured-variable annotations hold exactly for each singleton. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "every_Fn_vs_NONE_EVERY"]
theorem everyFnVarsNone_every (xs : List ClosLang.Exp) :
    everyFnVarsNone xs ↔ ∀ e ∈ xs, everyFnVarsNone [e] := by
  induction xs with
  | nil => simp [everyFnVarsNone]
  | cons e es ih => simp [everyFnVarsNone, ih]

/-- The function helper is the source's mapped body list. -/
theorem fnVarsNoneFuns_eq_map (fs : List (Nat × ClosLang.Exp)) :
    fnVarsNoneFuns fs ↔ everyFnVarsNone (fs.map Prod.snd) := by
  induction fs with
  | nil => simp [fnVarsNoneFuns, everyFnVarsNone]
  | cons f fs ih =>
    obtain ⟨arity, body⟩ := f
    simp [fnVarsNoneFuns, everyFnVarsNone, ih]

/-- The application predicate holds exactly for some element's singleton form. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "contains_App_SOME_EXISTS"]
theorem containsAppSome_exists (ls : List ClosLang.Exp) (maxApp : Nat) :
    containsAppSome maxApp ls ↔ ∃ x ∈ ls, containsAppSome maxApp [x] := by
  induction ls with
  | nil => simp [containsAppSome]
  | cons e es ih => simp [containsAppSome, ih]

/-- The absent-annotation predicate splits over list concatenation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "every_Fn_vs_NONE_APPEND"]
theorem everyFnVarsNone_append (l1 l2 : List ClosLang.Exp) :
    everyFnVarsNone (l1 ++ l2) ↔ everyFnVarsNone l1 ∧ everyFnVarsNone l2 := by
  induction l1 with
  | nil => simp [everyFnVarsNone]
  | cons e es ih => simp [everyFnVarsNone, ih, and_assoc]

/-- The absent-annotation predicate holds for any prefix of the list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "IMP_every_Fn_vs_NONE_TAKE"]
theorem everyFnVarsNone_take (ls : List ClosLang.Exp) (n : Nat) :
    everyFnVarsNone ls → everyFnVarsNone (ls.take n) := by
  induction ls generalizing n with
  | nil =>
    intro _
    simp [everyFnVarsNone]
  | cons e es ih =>
    intro h
    cases n with
    | zero => simp [everyFnVarsNone]
    | succ n =>
      simp only [List.take_succ_cons, everyFnVarsNone] at h ⊢
      exact ⟨h.1, ih n h.2⟩

end Flapjack.Compiler.Backend.ClosProps
