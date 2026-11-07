import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Free de Bruijn variables in closure-language expressions. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosLang

mutual

/-- Free-variable membership in one expression. This structural helper
implements the singleton cases of the source list predicate. -/
def freeVarExp (n : Nat) : Exp → Prop
  | .var _ v => n = v
  | .ifThenElse _ x y z => freeVarExp n x ∨ freeVarExp n y ∨ freeVarExp n z
  | .let _ xs body => freeVars n xs ∨ freeVarExp (n + xs.length) body
  | .raise _ body | .tick _ body => freeVarExp n body
  | .op _ _ xs | .call _ _ _ xs => freeVars n xs
  | .app _ _ function args => freeVarExp n function ∨ freeVars n args
  | .fn _ _ _ arity body => freeVarExp (n + arity) body
  | .letrec _ _ _ fns body =>
      freeVarFuns n fns.length fns ∨ freeVarExp (n + fns.length) body
  | .handle _ body handler => freeVarExp n body ∨ freeVarExp (n + 1) handler

/-- The original closure-language free-variable predicate on expression lists. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_def"]
def freeVars (n : Nat) : List Exp → Prop
  | [] => False
  | e :: es => freeVarExp n e ∨ freeVars n es

/-- Free variables of mutually recursive function bodies, retaining the
number of functions as the shift for every body. -/
def freeVarFuns (n count : Nat) : List (Nat × Exp) → Prop
  | [] => False
  | (arity, body) :: fns => freeVarExp (n + arity + count) body ∨ freeVarFuns n count fns

end

/-- The singleton form of the source free-variable predicate. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv1_def"]
def freeVar (n : Nat) (e : Exp) : Prop := freeVars n [e]

/-- The singleton traversal agrees with the expression helper. -/
theorem freeVars_singleton (n : Nat) (e : Exp) : freeVars n [e] ↔ freeVarExp n e := by
  simp [freeVars]

/-- The recursive-group helper has the source predicate's existential form. -/
theorem freeVarFuns_exists (n count : Nat) (fns : List (Nat × Exp)) :
    freeVarFuns n count fns ↔
      ∃ entry ∈ fns, freeVarExp (n + entry.1 + count) entry.2 := by
  induction fns with
  | nil => simp [freeVarFuns]
  | cons fn fns ih =>
    obtain ⟨arity, body⟩ := fn
    simp [freeVarFuns, ih]

end Flapjack.Compiler.Backend.ClosProps
