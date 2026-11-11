module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubInvariants
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars
@[expose] public section

/-! Free-variable preservation by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

private def FVSub (x y : Exp) : Prop := ∀ n, freeVarExp n y → freeVarExp n x

private theorem listFV {xs ys : List Exp} (rel : List.Forall₂ FVSub xs ys)
    (n : Nat) (h : freeVars n ys) : freeVars n xs := by
  induction rel with
  | nil => simp [freeVars] at h
  | cons head tail ih =>
    simp only [freeVars] at h ⊢
    rcases h with h | h
    · exact Or.inl (head n h)
    · exact Or.inr (ih h)

private theorem fvAppend (n : Nat) (xs ys : List Exp) :
    freeVars n (xs ++ ys) ↔ freeVars n xs ∨ freeVars n ys := by
  induction xs with
  | nil => simp [freeVars]
  | cons x xs ih => simp [freeVars, ih, or_assoc]

private theorem stubFunsFree (n count : Nat) (tr : BackendCommon.Tra) (i loc : Nat)
    (fns : List (Nat × Exp)) : ¬ freeVarFuns n count (callsListSource tr i loc fns) := by
  induction fns generalizing i loc with
  | nil => simp [callsListSource, freeVarFuns]
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    simp only [callsListSource, freeVarFuns, freeVarExp, not_or]
    constructor
    · intro h
      have bound := (freeVars_variables (n + arity + count) arity tr 1).mp h
      omega
    · exact ih (i + 1) (loc + 2)

private theorem fvFunsZip {fns : List (Nat × Exp)} {bodies : List Exp}
    (related : List.Forall₂ FVSub (fns.map Prod.snd) bodies) (n count : Nat)
    (h : freeVarFuns n count ((fns.map Prod.fst).zip bodies)) : freeVarFuns n count fns := by
  induction fns generalizing bodies with
  | nil => simp [freeVarFuns] at h
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    cases related with
    | cons first tail =>
      simp only [List.map_cons, List.zip_cons_cons, freeVarFuns] at h ⊢
      rcases h with head | tailFree
      · exact Or.inl (first _ head)
      · exact Or.inr (ih tail tailFree)

mutual
private theorem fvExpr (e : Exp) (s : State) : FVSub e (callsSing e s).1 := by
  cases e with
  | var tr n => simp [callsSing, FVSub]
  | raise tr e | tick tr e =>
    have ih := fvExpr e s
    cases run : callsSing e s with
    | mk out next => simpa [callsSing, run, FVSub, freeVarExp] using ih
  | ifThenElse tr x y z =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        cases hz : callsSing z sy with
        | mk oz sz =>
          have h₁ := fvExpr x s
          have h₂ := fvExpr y sx
          have h₃ := fvExpr z sy
          simp only [hx] at h₁
          simp only [hy] at h₂
          simp only [hz] at h₃
          simp only [callsSing, hx, hy, hz, FVSub, freeVarExp]
          intro n h
          rcases h with h | h | h
          · exact Or.inl (h₁ n h)
          · exact Or.inr (Or.inl (h₂ n h))
          · exact Or.inr (Or.inr (h₃ n h))
  | «let» tr xs body =>
    cases hx : callsSingList xs s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := fvList xs s
        have h₂ := fvExpr body sx
        have len := callsSingList_length xs s
        simp only [hx] at h₁ len
        simp only [hy] at h₂
        simp only [callsSing, hx, hy, FVSub, freeVarExp]
        intro n h
        rcases h with h | h
        · exact Or.inl (listFV h₁ n h)
        · exact Or.inr (h₂ (n + xs.length) (by simpa [len] using h))
  | handle tr x y =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        have h₁ := fvExpr x s
        have h₂ := fvExpr y sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simp only [callsSing, hx, hy, FVSub, freeVarExp]
        intro n h
        rcases h with h | h
        · exact Or.inl (h₁ n h)
        · exact Or.inr (h₂ (n + 1) h)
  | call tr ticks dest args | op tr dest args =>
    have ih := fvList args s
    cases run : callsSingList args s with
    | mk out next =>
      simp only [run] at ih
      simp only [callsSing, run, FVSub, freeVarExp]
      exact fun n h => listFV ih n h
  | app tr loc x xs =>
    cases hx : callsSingList xs s with
    | mk ox sx =>
      cases hy : callsSing x sx with
      | mk oy sy =>
        have h₁ := fvList xs s
        have h₂ := fvExpr x sx
        have len := callsSingList_length xs s
        simp only [hx] at h₁ len
        simp only [hy] at h₂
        cases loc with
        | none =>
          simp only [callsSing, hx, hy, FVSub, freeVarExp]
          intro n h
          rcases h with h | h
          · exact Or.inl (h₂ n h)
          · exact Or.inr (listFV h₁ n h)
        | some loc =>
          simp only [callsSing, hx, hy]
          split
          · split
            · simp only [FVSub, freeVarExp]
              intro n h
              exact Or.inr (listFV h₁ n h)
            · simp only [FVSub, freeVarExp]
              intro n h
              rcases h with bindings | generated
              · rw [fvAppend] at bindings
                rcases bindings with args | function
                · exact Or.inr (listFV h₁ n args)
                · simp only [freeVars, or_false] at function
                  exact Or.inl (h₂ n function)
              · have bound := (freeVars_variables (n + (ox ++ [oy]).length) ox.length .none 2).mp generated
                simp only [List.length_append, List.length_singleton] at bound
                omega
          · simp only [FVSub, freeVarExp]
            intro n h
            rcases h with h | h
            · exact Or.inl (h₂ n h)
            · exact Or.inr (listFV h₁ n h)
  | fn name loc vars arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    cases hf : callsSing body fresh with
    | mk out st =>
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · simp only [FVSub, freeVarExp]
        intro n h
        have bound := (freeVars_variables (n + arity) arity .none 1).mp h
        omega
      · have ih := fvExpr body s
        cases run : callsSing body s with
        | mk out next =>
          simp only [run] at ih ⊢
          simp only [FVSub, freeVarExp]
          exact fun n h => ih (n + arity) h
  | letrec names loc vars fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length s
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · let emitted := codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st
        have ih := fvExpr body emitted
        cases hb : callsSing body emitted with
        | mk out final =>
          simp only [hb] at ih
          change FVSub (.letrec names loc vars fns body)
            (.letrec names loc vars (callsListSource .none 1 (loc.getD 0) fns) out)
          simp only [FVSub, freeVarExp]
          intro n h
          have len := length_callsList .none 1 (loc.getD 0) fns
          rw [len] at h
          rcases h with impossible | bodyFree
          · exact (stubFunsFree n fns.length .none 1 (loc.getD 0) fns impossible).elim
          · exact Or.inr (ih (n + fns.length) bodyFree)
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihF := fvList (fns.map Prod.snd) s
          simp only [hg] at ihF ⊢
          cases hb : callsSing body st with
          | mk out final =>
            have ihBody := fvExpr body st
            simp only [hb] at ihBody ⊢
            simp only [FVSub, freeVarExp]
            intro n h
            have len := ihF.length_eq
            simp only [List.length_map] at len
            simp only [List.length_zip, List.length_map, ← len, Nat.min_self] at h
            rcases h with funsFree | bodyFree
            · exact Or.inl (fvFunsZip ihF n fns.length funsFree)
            · exact Or.inr (ihBody (n + fns.length) bodyFree)
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem fvList (es : List Exp) (s : State) :
    List.Forall₂ FVSub es (callsSingList es s).1 := by
  cases es with
  | nil => simp [callsSingList]
  | cons e es =>
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h₁ := fvExpr e s
        have h₂ := fvList es mid
        simp only [he] at h₁
        simp only [hs] at h₂
        simpa [callsSingList, he, hs] using List.Forall₂.cons h₁ h₂
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- Each transformed expression has no new free variables. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_fv1_subset"]
theorem calls_freeVar_subset (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) :
    List.Forall₂ (fun x y => Set.Subset {v | freeVar v y} {v | freeVar v x}) xs ys := by
  have rel := fvList xs g0
  change callsSingList xs g0 = (ys, g) at h
  rw [h] at rel
  apply rel.imp
  intro x y subset n free
  simpa [freeVar, freeVars] using subset n (by simpa [freeVar, freeVars] using free)

/-- A free variable of transformed expressions was free in the input. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_fv_imp"]
theorem calls_freeVars_imp (xs : List Exp) (g0 : State) (ys : List Exp) (g : State) (v : Nat)
    (h : calls xs g0 = (ys, g) ∧ freeVars v ys) : freeVars v xs := by
  have rel := fvList xs g0
  have run : callsSingList xs g0 = (ys, g) := h.1
  rw [run] at rel
  exact listFV rel v h.2

end Flapjack.Compiler.Backend.ClosCall
