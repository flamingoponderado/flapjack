module

public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free
public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect
public import Flapjack.Misc.Sptree.Wf

@[expose] public section

/-! Agreement of the checked free-variable traversal with the source. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang DbVars ClosCall

private theorem freeFunsFuel_correct (fuel count : Nat)
    (ih : ∀ e out vars, freeFuel fuel e = some (out, vars) → (out, vars) = freeExpHOL e)
    (fns : List (Nat × Exp)) (results : List ((Nat × Exp) × DbVarSet))
    (run : fns.mapM (fun (arity, body) => do
      let (body', vars) ← freeFuel fuel body
      pure ((arity, body'), DbVarSet.shift (arity + count) vars)) = some results) :
    results = freeFunsHOL count fns := by
  induction fns generalizing results with
  | nil => simpa [freeFunsHOL] using run.symm
  | cons fn fns tailIH =>
    obtain ⟨arity, body⟩ := fn
    simp only [List.mapM_cons, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
      Option.some.injEq] at run
    obtain ⟨_, ⟨⟨body', vars⟩, hb, rfl⟩, rest, hr, rfl⟩ := run
    have head := ih body body' vars hb
    have tail := tailIH rest hr
    simp only [freeFunsHOL]
    rw [← head, ← tail]

/-- The checked expression and list traversals return exactly the source
annotations and variable-set tree whenever they succeed. -/
theorem freeFuel_correct (fuel : Nat) :
    (∀ e out vars, freeFuel fuel e = some (out, vars) → (out, vars) = freeExpHOL e) ∧
    (∀ es out vars, freeListFuel fuel es = some (out, vars) → (out, vars) = freeHOL es) := by
  induction fuel with
  | zero =>
    constructor
    · intro e out vars run; simp [freeFuel] at run
    · intro es out vars run
      cases es with
      | nil => simpa [freeListFuel, freeHOL] using run.symm
      | cons e es => simp [freeListFuel] at run
  | succ fuel ih =>
    rcases ih with ⟨exprIH, listIH⟩
    constructor
    · intro e out vars run
      cases e with
      | var tr index => simpa [freeFuel, freeExpHOL] using run.symm
      | ifThenElse tr x y z =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨x', a⟩, hx, ⟨y', b⟩, hy, ⟨z', c⟩, hz, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← exprIH x x' a hx, ← exprIH y y' b hy, ← exprIH z z' c hz]
      | «let» tr xs body =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨xs', a⟩, hx, ⟨body', b⟩, hb, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← listIH xs xs' a hx, ← exprIH body body' b hb]
        simp [freeListFuel_length fuel xs xs' a hx]
      | raise tr x | tick tr x =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨x', a⟩, hx, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← exprIH x x' a hx]
      | handle tr x y =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨x', a⟩, hx, ⟨y', b⟩, hy, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← exprIH x x' a hx, ← exprIH y y' b hy]
      | call tr ticks dest xs | op tr dest xs =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨xs', a⟩, hx, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← listIH xs xs' a hx]
      | app tr loc x xs =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨x', a⟩, hx, ⟨xs', b⟩, hs, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← exprIH x x' a hx, ← listIH xs xs' b hs]
      | fn name loc ws arity body =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨body', a⟩, hb, rfl, rfl⟩ := run
        simp only [freeExpHOL]
        rw [← exprIH body body' a hb]
      | letrec names loc ws fns body =>
        simp only [freeFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨results, hf, ⟨body', bodyVars⟩, hb, rfl, rfl⟩ := run
        have group := freeFunsFuel_correct fuel fns.length exprIH fns results hf
        simp only [freeExpHOL]
        rw [← group, ← exprIH body body' bodyVars hb]
    · intro es out vars run
      cases es with
      | nil => simpa [freeListFuel, freeHOL] using run.symm
      | cons e es =>
        simp only [freeListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨e', a⟩, he, ⟨es', b⟩, hs, rfl, rfl⟩ := run
        simp only [freeHOL]
        rw [← exprIH e e' a he, ← listIH es es' b hs]

/-- The checked retry always returns the source single-expression result. -/
theorem freeBounded_correct (fuel : Nat) (e : Exp) :
    freeBounded fuel e = some (freeExpHOL e) := by
  obtain ⟨⟨out, vars⟩, run⟩ := freeBounded_succeeds fuel e
  have agreement : (out, vars) = freeExpHOL e := by
    unfold freeBounded at run
    cases first : freeFuel fuel e with
    | some result =>
      simp only [first, Option.some.injEq] at run
      subst result
      exact (freeFuel_correct fuel).1 e out vars first
    | none =>
      simp only [first] at run
      exact (freeFuel_correct _).1 e out vars run
  simpa [agreement] using run

private theorem dbToSetAcc_wf (vars : DbVarSet) :
    ∀ n tree, sptWf tree = true → sptWf (dbToSetAcc n vars tree) = true := by
  induction vars with
  | empty => intro n tree wf; simpa [dbToSetAcc] using wf
  | var index =>
    intro n tree wf
    simp only [dbToSetAcc]
    split
    · exact wf
    · exact sptWfInsert _ _ _ wf
  | shift amount vars ih =>
    intro n tree wf
    exact ih (n + amount) tree wf
  | union left right leftIH rightIH =>
    intro n tree wf
    exact leftIH n _ (rightIH n tree wf)

private theorem dbToSet_empty_agrees (vars : DbVarSet) :
    sptIsEmpty (dbToSet vars) = (sptToAList (dbToSet vars)).isEmpty := by
  have wf : sptWf (dbToSet vars) = true := dbToSetAcc_wf vars 0 .ln (by simp [sptWf])
  cases empty : sptIsEmpty (dbToSet vars) with
  | true =>
    have treeEmpty : dbToSet vars = .ln := by
      cases h : dbToSet vars <;> simp_all [sptIsEmpty]
    simp [treeEmpty]
  | false =>
    obtain ⟨key, value, lookup⟩ := sptWf_exists_key (dbToSet vars) wf empty
    cases rows : sptToAList (dbToSet vars) with
    | nil =>
      have bridge := sptLookup_sptFromAList_sptToAList key (dbToSet vars)
      simp [rows, sptFromAList] at bridge
      rw [← bridge] at lookup
      contradiction
    | cons row rows => rfl

/-- The direct-call closedness check returns the source known-pass result. -/
theorem closedFuel_correct (fuel : Nat) (e : Exp) :
    closedFuel fuel e = some (closedHOL e) := by
  have free := freeBounded_correct fuel e
  cases result : freeExpHOL e with
  | mk out vars =>
    simp only [result] at free
    have empty := dbToSet_empty_agrees vars
    have unionEmpty : mkUnion vars .empty = vars := by cases vars <;> rfl
    simp [closedFuel, free, closedHOL, freeHOL, result, unionEmpty, empty]

end Flapjack.Compiler.Backend.ClosKnown
