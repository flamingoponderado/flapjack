module

public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Misc.ListEl

@[expose] public section

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

/-- The recursive-group helper has the source predicate's existential form. -/
theorem freeVarFuns_exists (n count : Nat) (fns : List (Nat × Exp)) :
    freeVarFuns n count fns ↔
      ∃ entry ∈ fns, freeVarExp (n + entry.1 + count) entry.2 := by
  induction fns with
  | nil => simp [freeVarFuns]
  | cons fn fns ih =>
    obtain ⟨arity, body⟩ := fn
    simp [freeVarFuns, ih]

/-- No variable is free in the empty expression list. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_nil"]
theorem freeVars_nil (v : Nat) : freeVars v [] ↔ False := by
  simp [freeVars]

/-- The list predicate on a singleton is the expression predicate. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv1_intro"]
theorem freeVars_singleton (v : Nat) (e : Exp) : freeVars v [e] ↔ freeVar v e := by
  simp [freeVar]

/-- The list predicate on a cons cell is the head predicate or the tail. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_cons"]
theorem freeVars_cons (v : Nat) (x : Exp) (xs : List Exp) :
    freeVars v (x :: xs) ↔ freeVar v x ∨ freeVars v xs := by
  simp [freeVar, freeVars]

/-- The list predicate holds exactly for some element's singleton form. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_exists"]
theorem freeVars_exists (ls : List Exp) (v : Nat) :
    freeVars v ls ↔ ∃ x ∈ ls, freeVar v x := by
  induction ls with
  | nil => simp [freeVars]
  | cons e es ih => simp [freeVars, freeVar, ih]

/-- The list predicate on a replicated expression is the head predicate. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_REPLICATE"]
theorem freeVars_replicate (n : Nat) (m : Nat) (e : Exp) :
    freeVars n (List.replicate m e) ↔ 0 < m ∧ freeVar n e := by
  induction m with
  | zero => simp [freeVars]
  | succ m ih => simp [List.replicate, freeVars, freeVar, ih]

/-- The list predicate on a mapped-with-index list holds for some index. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "fv_MAPi"
  (total_function_inhabitants := [α])]
theorem freeVars_mapIdx {α : Type} [Nonempty α] (l : List α) (x : Nat)
    (f : Nat → α → Exp) :
    freeVars x (l.mapIdx f) ↔ ∃ n, n < l.length ∧ freeVars x [f n (holEl n l)] := by
  induction l generalizing f with
  | nil => simp [freeVars]
  | cons a as ih =>
    have step := ih (fun i => f (i + 1))
    rw [List.mapIdx_cons, freeVars, step]
    constructor
    · intro h
      rcases h with h | ⟨n, hn, h⟩
      · exact ⟨0, by simp, by simpa [freeVars, freeVar, holEl, holHd] using h⟩
      · refine ⟨n + 1, by simp [hn], ?_⟩
        simpa [holEl] using h
    · rintro ⟨n, hn, h⟩
      cases n with
      | zero => exact Or.inl (by simpa [freeVars, freeVar, holEl, holHd] using h)
      | succ n =>
        refine Or.inr ⟨n, ?_, ?_⟩
        · simp at hn ⊢
          omega
        · simpa [holEl] using h

end Flapjack.Compiler.Backend.ClosProps
