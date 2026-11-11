module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeTotal
public import Flapjack.Compiler.Backend.ClosCall.Free
public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FreeVars
public import Flapjack.Compiler.Backend.DbVars.Proofs.Lookup
public import Mathlib.Tactic

@[expose] public section

/-! Free-variable agreement for the executable direct-call analysis. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps DbVars

/-- Pointwise agreement on a list preserves existence over that list. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "IMP_EXISTS_IFF"]
theorem impExistsIff {A : Type} (P Q : A → Prop) (xs : List A)
    (agree : ∀ x ∈ xs, P x ↔ Q x) :
    (∃ x, x ∈ xs ∧ P x) ↔ ∃ x, x ∈ xs ∧ Q x := by
  exact exists_congr fun x => and_congr_right (agree x)

private theorem freeFuns_agreement (fuel count : Nat)
    (agree : ∀ (e result : Exp) (vars : DbVarSet), freeFuel fuel e = some (result, vars) →
      ∀ n, (freeVarExp n e ↔ hasVar n vars = true) ∧
        (freeVarExp n result ↔ hasVar n vars = true))
    (fns : List (Nat × Exp)) (results : List ((Nat × Exp) × DbVarSet))
    (run : fns.mapM (fun (arity, body) => do
      let (body', vars) ← freeFuel fuel body
      pure ((arity, body'), DbVarSet.shift (arity + count) vars)) = some results) :
    results.length = fns.length ∧ ∀ n,
      (freeVarFuns n count fns ↔ hasVar n (listMkUnion (results.map Prod.snd)) = true) ∧
      (freeVarFuns n count (results.map Prod.fst) ↔
        hasVar n (listMkUnion (results.map Prod.snd)) = true) := by
  induction fns generalizing results with
  | nil =>
    change some [] = some results at run
    simp only [Option.some.injEq] at run
    subst results
    simp [freeVarFuns, listMkUnion, hasVar]
  | cons fn fns ih =>
    obtain ⟨arity, body⟩ := fn
    simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
      Option.some.injEq] at run
    obtain ⟨_, ⟨⟨body', vars⟩, hb, rfl⟩, rest, hr, rfl⟩ := run
    obtain ⟨length, restAgree⟩ := ih rest hr
    constructor
    · simpa only [List.length_cons] using congrArg Nat.succ length
    · intro n
      obtain ⟨bodySource, bodyTarget⟩ := agree body body' vars hb (n + arity + count)
      obtain ⟨restSource, restTarget⟩ := restAgree n
      simp only [freeVarFuns, List.map_cons, listMkUnion, hasVar_mkUnion,
        hasVar, Bool.or_eq_true, ← Nat.add_assoc]
      exact ⟨or_congr bodySource restSource, or_congr bodyTarget restTarget⟩

mutual
/-- On success, free-variable analysis computes membership for both the
original expression and the annotated result. HOL's analysis is total;
the success premise records the executable traversal's fuel. -/
private theorem freeFuel_freeVars (fuel : Nat) (e result : Exp) (vars : DbVarSet)
    (run : freeFuel fuel e = some (result, vars)) :
    ∀ n, (freeVarExp n e ↔ hasVar n vars = true) ∧
      (freeVarExp n result ↔ hasVar n vars = true) := by
  cases fuel with
  | zero => simp [freeFuel] at run
  | succ fuel =>
    cases e with
    | var tr v =>
      simp [freeFuel] at run
      obtain ⟨rfl, rfl⟩ := run
      intro n
      simp [freeVarExp, hasVar]
    | ifThenElse tr x y z =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', a⟩, hx, ⟨y', b⟩, hy, ⟨z', c⟩, hz, rfl, rfl⟩ := run
      intro n
      obtain ⟨xs, xt⟩ := freeFuel_freeVars fuel x x' a hx n
      obtain ⟨ys, yt⟩ := freeFuel_freeVars fuel y y' b hy n
      obtain ⟨zs, zt⟩ := freeFuel_freeVars fuel z z' c hz n
      simp only [freeVarExp, hasVar_mkUnion, Bool.or_eq_true]
      exact ⟨or_congr xs (or_congr ys zs), or_congr xt (or_congr yt zt)⟩
    | «let» tr xs body =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', a⟩, hx, ⟨body', b⟩, hb, rfl, rfl⟩ := run
      intro n
      obtain ⟨xsSource, xsTarget⟩ := freeListFuel_freeVars fuel xs xs' a hx n
      have len := freeListFuel_length fuel xs xs' a hx
      obtain ⟨bodySource, bodyTarget⟩ := freeFuel_freeVars fuel body body' b hb (n + xs.length)
      simp only [freeVarExp, hasVar_mkUnion, hasVar, Bool.or_eq_true]
      rw [len]
      exact ⟨or_congr xsSource bodySource, or_congr xsTarget bodyTarget⟩
    | raise tr x | tick tr x =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', a⟩, hx, rfl, rfl⟩ := run
      intro n
      exact freeFuel_freeVars fuel x x' a hx n
    | handle tr x y =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', a⟩, hx, ⟨y', b⟩, hy, rfl, rfl⟩ := run
      intro n
      obtain ⟨xs, xt⟩ := freeFuel_freeVars fuel x x' a hx n
      obtain ⟨ys, yt⟩ := freeFuel_freeVars fuel y y' b hy (n + 1)
      simp only [freeVarExp, hasVar_mkUnion, hasVar, Bool.or_eq_true]
      exact ⟨or_congr xs ys, or_congr xt yt⟩
    | call tr ticks dest xs | op tr dest xs =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', a⟩, hx, rfl, rfl⟩ := run
      intro n
      exact freeListFuel_freeVars fuel xs xs' a hx n
    | app tr loc x xs =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', a⟩, hx, ⟨xs', b⟩, hs, rfl, rfl⟩ := run
      intro n
      obtain ⟨xSource, xTarget⟩ := freeFuel_freeVars fuel x x' a hx n
      obtain ⟨xsSource, xsTarget⟩ := freeListFuel_freeVars fuel xs xs' b hs n
      simp only [freeVarExp, hasVar_mkUnion, Bool.or_eq_true]
      exact ⟨or_congr xSource xsSource, or_congr xTarget xsTarget⟩
    | fn name loc ws arity body =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', a⟩, hb, rfl, rfl⟩ := run
      intro n
      exact freeFuel_freeVars fuel body body' a hb (n + arity)
    | letrec names loc ws fns body =>
      simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨results, hf, ⟨body', bodyVars⟩, hb, rfl, rfl⟩ := run
      have group := freeFuns_agreement fuel fns.length
        (fun e result vars h => freeFuel_freeVars fuel e result vars h) fns results hf
      intro n
      obtain ⟨groupSource, groupTarget⟩ := group.2 n
      obtain ⟨bodySource, bodyTarget⟩ := freeFuel_freeVars fuel body body' bodyVars hb (n + fns.length)
      simp only [freeVarExp, List.length_map, group.1, hasVar_mkUnion, hasVar, Bool.or_eq_true]
      exact ⟨or_congr groupSource bodySource, or_congr groupTarget bodyTarget⟩
termination_by fuel

/-- The list traversal computes the same free variables before and after
annotation. -/
private theorem freeListFuel_freeVars (fuel : Nat) (es result : List Exp) (vars : DbVarSet)
    (run : freeListFuel fuel es = some (result, vars)) :
    ∀ n, (freeVars n es ↔ hasVar n vars = true) ∧
      (freeVars n result ↔ hasVar n vars = true) := by
  cases es with
  | nil =>
    cases fuel <;> simp [freeListFuel] at run <;> obtain ⟨rfl, rfl⟩ := run <;>
      intro n <;> simp [freeVars, hasVar]
  | cons e es =>
    cases fuel with
    | zero => simp [freeListFuel] at run
    | succ fuel =>
      simp only [freeListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', a⟩, he, ⟨es', b⟩, hs, rfl, rfl⟩ := run
      intro n
      obtain ⟨eSource, eTarget⟩ := freeFuel_freeVars fuel e e' a he n
      obtain ⟨esSource, esTarget⟩ := freeListFuel_freeVars fuel es es' b hs n
      simp only [freeVars, hasVar_mkUnion, Bool.or_eq_true]
      exact ⟨or_congr eSource esSource, or_congr eTarget esTarget⟩
termination_by fuel
end

/-- The source free-variable traversal preserves membership and computes its
exact variable set. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "free_thm"]
theorem freeThm (expressions : List Exp) :
    let (output, vars) := free expressions
    ∀ n, (freeVars n output ↔ hasVar n vars = true) ∧
      (freeVars n expressions ↔ hasVar n vars = true) := by
  obtain ⟨⟨output, vars⟩, run⟩ :=
    freeListFuel_succeeds (listBudget expressions + 1) expressions (Nat.lt_succ_self _)
  have sourceEq : (output, vars) = free expressions :=
    (ClosKnown.freeFuel_correct _).2 expressions output vars run
  rw [← sourceEq]
  intro n
  have agreement := freeListFuel_freeVars _ expressions output vars run n
  exact ⟨agreement.2, agreement.1⟩


/-- The production retry wrapper retains free-variable agreement. -/
private theorem freeBounded_freeVars (fuel : Nat) (e result : Exp) (vars : DbVarSet)
    (run : freeBounded fuel e = some (result, vars)) :
    ∀ n, (freeVarExp n e ↔ hasVar n vars = true) ∧
      (freeVarExp n result ↔ hasVar n vars = true) := by
  unfold freeBounded at run
  cases first : freeFuel fuel e with
  | some output =>
    simp only [first, Option.some.injEq] at run
    subst output
    exact freeFuel_freeVars fuel e result vars first
  | none =>
    simp only [first] at run
    exact freeFuel_freeVars _ e result vars run

private theorem materializedEmpty_iff (vars : DbVarSet) :
    (sptToAList (dbToSet vars)).isEmpty = true ↔ ∀ n, hasVar n vars = false := by
  have listEmpty : (sptToAList (dbToSet vars)).isEmpty = true ↔ varsToList vars = [] := by
    simp [varsToList]
  rw [listEmpty]
  constructor
  · intro empty n
    have notMember : n ∉ varsToList vars := by simp [empty]
    have notLive : ¬ hasVar n vars = true := fun live => notMember ((memVarsToList n vars).mpr live)
    cases h : hasVar n vars <;> simp_all
  · intro noLive
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n member
    have live := (memVarsToList n vars).mp member
    rw [noLive n] at live
    contradiction

/-- The executable closedness check succeeds exactly when its input has no
free variables. -/
private theorem closedFuel_iff_noFreeVars (fuel : Nat) (e : Exp) :
    closedFuel fuel e = some true ↔ ∀ n, ¬ freeVarExp n e := by
  obtain ⟨⟨result, vars⟩, run⟩ := freeBounded_succeeds fuel e
  have agreement := freeBounded_freeVars fuel e result vars run
  simp only [closedFuel, run, Bind.bind, Option.bind, Pure.pure, Option.some.injEq, materializedEmpty_iff]
  constructor
  · intro empty n free
    have live := (agreement n).1.mp free
    rw [empty n] at live
    contradiction
  · intro noFree n
    have noLive : ¬ hasVar n vars = true := fun live => noFree n ((agreement n).1.mpr live)
    cases h : hasVar n vars <;> simp_all

/-- A closure is reported closed precisely when its body has no free
variable beyond its argument prefix. -/
private theorem closedFuel_fn (fuel : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    closedFuel fuel (.fn name loc vars arity body) = some true ↔
      ∀ n, freeVarExp n body → n < arity := by
  rw [closedFuel_iff_noFreeVars]
  simp only [freeVarExp]
  constructor
  · intro noFree n free
    by_contra notLess
    have bound : arity ≤ n := by omega
    have eq : n - arity + arity = n := by omega
    exact noFree (n - arity) (by simpa only [eq] using free)
  · intro bound n free
    have := bound (n + arity) free
    omega

/-- A source function is closed exactly when its body's free variables lie
inside its argument prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "closed_Fn_fv"]
theorem closedFn_fv (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    closed (.fn name loc vars arity body) = true ↔
      ∀ n, freeVars n [body] → n < arity := by
  have bridge := ClosKnown.closedFuel_correct 0 (.fn name loc vars arity body)
  have result := closedFuel_fn 0 name loc vars arity body
  rw [bridge] at result
  simpa [closed, freeVars] using result

/-- Source closedness is characterized by the body's computed variable set. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "closed_Fn"]
theorem closedFn (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    closed (.fn name loc vars arity body) = true ↔
      ∀ n, hasVar n (free [body]).2 = true → n < arity := by
  rw [closedFn_fv]
  have correct := freeThm [body]
  cases result : free [body] with
  | mk output live =>
    rw [result] at correct
    constructor <;> intro h n member
    · exact h n ((correct n).2.mpr member)
    · exact h n ((correct n).2.mp member)

end Flapjack.Compiler.Backend.ClosCall
