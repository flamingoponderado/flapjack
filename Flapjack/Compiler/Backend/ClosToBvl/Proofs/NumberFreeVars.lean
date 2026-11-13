module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.ClosureApplication
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars

@[expose] public section

/-! Free-variable preservation by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps ClosNumber

/-- Flapjack infrastructure: the numbered recursive bundle keeps its length. -/
private theorem funsLength (fs : List (Nat × ClosLang.Exp)) (n : Nat) :
    (renumberFuns n fs).2.length = fs.length := by
  simp [renumberFuns_eq_numberedBodies, renumberList_length]

mutual
/-- Flapjack infrastructure: numbering preserves free variables of one expression. -/
private theorem exprFree (e : ClosLang.Exp) (n v : Nat) :
    freeVarExp v (renumber n e).2 ↔ freeVarExp v e := by
  cases e with
  | var t x => simp [renumber, freeVarExp]
  | ifThenElse t a b c =>
    simp [renumber, freeVarExp, exprFree a, exprFree b, exprFree c]
  | «let» t xs body =>
    simp [renumber, freeVarExp, listFree xs, renumberList_length, exprFree body]
  | raise t body | tick t body => simp [renumber, freeVarExp, exprFree body]
  | handle t body handler => simp [renumber, freeVarExp, exprFree body, exprFree handler]
  | call t ticks dest args | op t _ args => simp [renumber, freeVarExp, listFree args]
  | app t loc body args => simp [renumber, freeVarExp, exprFree body, listFree args]
  | fn name loc vars arity body => simp [renumber, freeVarExp, exprFree body]
  | letrec names loc vars fs body =>
    simp [renumber, freeVarExp, funsLength, funsFree fs, exprFree body]
termination_by sizeOf e

/-- Flapjack infrastructure: the list case needed by the mutual numbering proof. -/
private theorem listFree (es : List ClosLang.Exp) (n v : Nat) :
    freeVars v (renumberList n es).2 ↔ freeVars v es := by
  cases es with
  | nil => simp [renumberList, freeVars]
  | cons first rest => simp [renumberList, freeVars, exprFree first, listFree rest]
termination_by sizeOf es

/-- Flapjack infrastructure: recursive-function bodies retain their free variables. -/
private theorem funsFree (fs : List (Nat × ClosLang.Exp)) (n count v : Nat) :
    freeVarFuns v count (renumberFuns n fs).2 ↔ freeVarFuns v count fs := by
  cases fs with
  | nil => simp [renumberFuns, freeVarFuns]
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    simp [renumberFuns, freeVarFuns, exprFree body, funsFree rest]
termination_by sizeOf fs
decreasing_by all_goals (subst_vars; simp_wf; omega)
end

/-- Flapjack infrastructure: assemble the original list relation pointwise. -/
private theorem listRel (es : List ClosLang.Exp) (n : Nat) :
    List.Forall₂ (fun a b => ∀ v, freeVar v a ↔ freeVar v b) (renumberList n es).2 es := by
  induction es generalizing n with
  | nil => simp [renumberList]
  | cons e es ih =>
    simp only [renumberList]
    cases he : renumber n e with
    | mk next out =>
      cases hr : renumberList next es with
      | mk last outs =>
        simp only [List.forall₂_cons]
        constructor
        · intro v
          have h := exprFree e n v
          simpa [freeVar, freeVars, he] using h
        · simpa [hr] using ih next

/-- Numbering preserves every free variable in corresponding expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_fv1"]
theorem renumberCodeLocs_freeVar {α : Type} :
    (∀ (n : Nat) (es : List ClosLang.Exp) (_unused : α),
      List.Forall₂ (fun a b => ∀ v, freeVar v a ↔ freeVar v b) (renumberList n es).2 es) ∧
    (∀ (n : Nat) (e : ClosLang.Exp) (v : Nat), freeVar v (renumber n e).2 ↔ freeVar v e) := by
  constructor
  · intro n es unused
    exact listRel es n
  · intro n e v
    simpa [freeVar, freeVars] using exprFree e n v

/-- A returned numbered list has the same free-variable predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_list_fv"]
theorem renumberList_freeVars (n : Nat) (es : List ClosLang.Exp) (k : Nat)
    (es' : List ClosLang.Exp) (x : Nat)
    (run : renumberList n es = (k, es')) : freeVars x es' ↔ freeVars x es := by
  simpa [run] using listFree es n x
end Flapjack.Compiler.Backend.ClosToBvl
