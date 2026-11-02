import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect
import Flapjack.Compiler.Backend.ClosCall.Proofs.Length

/-! Closedness of mutually recursive groups in the executed direct-call pass. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

/-- The fold used by direct-call conversion to decide whether every
transformed recursive body is closed with respect to its arguments. -/
def groupClosedFuel (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp) : Option Bool :=
  (fns.zip bodies).foldlM (fun all pair => do
    if !all then pure false else
      closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2)) true

private theorem closedFold_false (fuel : Nat) (pairs : List ((Nat × Exp) × Exp)) :
    pairs.foldlM (fun all pair => do
      if !all then pure false else
        closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2)) false = some false := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨⟨arity, old⟩, body⟩ := pair
    simpa using ih

private theorem closedFold_succeeds (fuel : Nat) (pairs : List ((Nat × Exp) × Exp)) (initial : Bool) :
    ∃ result, pairs.foldlM (fun all pair => do
      if !all then pure false else
        closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2))
      initial = some result := by
  induction pairs generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons pair rest ih =>
    obtain ⟨⟨arity, old⟩, body⟩ := pair
    cases initial with
    | false => exact ⟨false, by simpa using closedFold_false fuel (((arity, old), body) :: rest)⟩
    | true =>
      obtain ⟨value, check⟩ := closedFuel_succeeds fuel
        (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body)
      obtain ⟨result, done⟩ := ih value
      exact ⟨result, by simpa [check] using done⟩

/-- The recursive-group closedness fold cannot exhaust the retry budget. -/
theorem groupClosedFuel_succeeds (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp) :
    ∃ result, groupClosedFuel fuel fns bodies = some result :=
  closedFold_succeeds fuel (fns.zip bodies) true

/-- When the lists have equal length, the executable group check accepts
exactly when each transformed body has no free variable beyond its arity. -/
theorem groupClosedFuel_iff (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp)
    (lengths : fns.length = bodies.length) :
    groupClosedFuel fuel fns bodies = some true ↔
      List.Forall₂ (fun fn body => ∀ n, freeVarExp n body → n < fn.1) fns bodies := by
  induction fns generalizing bodies with
  | nil =>
    cases bodies with
    | nil => simp [groupClosedFuel]
    | cons body bodies => simp at lengths
  | cons fn fns ih =>
    obtain ⟨arity, old⟩ := fn
    cases bodies with
    | nil => simp at lengths
    | cons body bodies =>
      have restLength : fns.length = bodies.length := Nat.succ.inj lengths
      simp only [groupClosedFuel, List.zip_cons_cons, List.foldlM_cons, Bind.bind,
        Pure.pure] at *
      cases check : closedFuel fuel
          (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) with
      | none =>
        obtain ⟨result, success⟩ := closedFuel_succeeds fuel
          (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body)
        simp [check] at success
      | some value =>
        cases value with
        | false =>
          have notClosed : ¬ (∀ n, freeVarExp n body → n < arity) := by
            intro closed
            have success := (closedFuel_fn fuel (Flapjack.Basis.Pure.MlString.ofString "")
              none none arity body).mpr closed
            rw [check] at success
            contradiction
          have stopped := closedFold_false fuel (fns.zip bodies)
          simp only [Pure.pure] at stopped
          simp only [List.forall₂_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
          rw [stopped]
          simp [notClosed]
        | true =>
          have closed := (closedFuel_fn fuel (Flapjack.Basis.Pure.MlString.ofString "")
            none none arity body).mp check
          simp only [List.forall₂_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
          constructor
          · intro h
            exact ⟨closed, (ih bodies restLength).mp h⟩
          · rintro ⟨_, h⟩
            exact (ih bodies restLength).mpr h

/-- If converted recursive bodies are closed at their arities, the executed
pass selects the code-extraction branch and emits the direct-call stubs. -/
theorem callsFuel_letrec_closedBranch (fuel : Nat)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat)
    (vars : Option (List Nat)) (fns : List (Nat × Exp)) (body : Exp)
    (initial afterBodies final : State) (bodies : List Exp) (body' : Exp)
    (bodyRun : callsListFuel fuel (fns.map Prod.snd)
      (insertEach (loc.getD 0) fns.length initial) = some (bodies, afterBodies))
    (closed : List.Forall₂ (fun fn e => ∀ n, freeVarExp n e → n < fn.1) fns bodies)
    (continuation : callsFuel fuel body
      (codeList (loc.getD 0) ((fns.map Prod.fst).zip bodies) afterBodies) = some (body', final)) :
    callsFuel (fuel + 1) (.letrec names loc vars fns body) initial =
      some (.letrec names loc vars (callsList (loc.getD 0) fns) body', final) := by
  have length : fns.length = bodies.length := by
    have h := callsListFuel_length fuel (fns.map Prod.snd)
      (insertEach (loc.getD 0) fns.length initial) afterBodies bodies bodyRun
    simpa using h.symm
  have check := (groupClosedFuel_iff fuel fns bodies length).mpr closed
  unfold groupClosedFuel at check
  simp at check
  simp [callsFuel, bodyRun, check, continuation]

/-- If a transformed recursive body is not closed at its arity, the
executed pass retries the group from the original state and retains closures. -/
theorem callsFuel_letrec_openBranch (fuel : Nat)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat)
    (vars : Option (List Nat)) (fns : List (Nat × Exp)) (body : Exp)
    (initial afterProbe afterRetry final : State) (probeBodies retryBodies : List Exp) (body' : Exp)
    (probe : callsListFuel fuel (fns.map Prod.snd)
      (insertEach (loc.getD 0) fns.length initial) = some (probeBodies, afterProbe))
    (notClosed : ¬List.Forall₂ (fun fn e => ∀ n, freeVarExp n e → n < fn.1) fns probeBodies)
    (retry : callsListFuel fuel (fns.map Prod.snd) initial = some (retryBodies, afterRetry))
    (continuation : callsFuel fuel body afterRetry = some (body', final)) :
    callsFuel (fuel + 1) (.letrec names loc vars fns body) initial =
      some (.letrec names loc vars ((fns.map Prod.fst).zip retryBodies) body', final) := by
  have length : fns.length = probeBodies.length := by
    have h := callsListFuel_length fuel (fns.map Prod.snd)
      (insertEach (loc.getD 0) fns.length initial) afterProbe probeBodies probe
    simpa using h.symm
  obtain ⟨result, check⟩ := groupClosedFuel_succeeds fuel fns probeBodies
  have resultFalse : result = false := by
    cases result with
    | false => rfl
    | true => exact False.elim (notClosed ((groupClosedFuel_iff fuel fns probeBodies length).mp check))
  subst result
  unfold groupClosedFuel at check
  simp at check
  simp [callsFuel, probe, check, retry, continuation]

end Flapjack.Compiler.Backend.ClosCall
