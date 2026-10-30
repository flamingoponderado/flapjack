import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeTotal

/-! Structural sufficiency for direct-call conversion. These results are
Flapjack infrastructure, not HOL pass-correctness ports. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang DbVars

private theorem bodies_budget (fns : List (Nat × Exp)) :
    listBudget (fns.map Prod.snd) = funsBudget fns := by
  induction fns with
  | nil => simp [listBudget, funsBudget]
  | cons p ps ih =>
    obtain ⟨arity, body⟩ := p
    simp [listBudget, funsBudget, ih]

private theorem closedFold_succeeds (fuel : Nat) (xs : List ((Nat × Exp) × Exp)) (initial : Bool) :
    ∃ result, xs.foldlM (fun all ((arity, _), code) => do
      if !all then pure false else closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity code)) initial = some result := by
  induction xs generalizing initial with
  | nil => exact ⟨_, rfl⟩
  | cons p ps ih =>
    obtain ⟨⟨arity, old⟩, code⟩ := p
    cases initial with
    | false =>
      obtain ⟨result, hr⟩ := ih false
      exact ⟨result, by simpa using hr⟩
    | true =>
      obtain ⟨value, hv⟩ := closedFuel_succeeds fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity code)
      obtain ⟨result, hr⟩ := ih value
      exact ⟨result, by simpa [hv] using hr⟩

mutual
/-- Direct-call conversion succeeds under a structural traversal bound. -/
theorem callsFuel_succeeds (fuel : Nat) (e : Exp) (state : State) (bound : expBudget e < fuel) :
    ∃ result, callsFuel fuel e state = some result := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases e with
    | var t v => exact ⟨_, rfl⟩
    | ifThenElse t x y z =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      have bz : expBudget z < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', s1⟩, hx⟩ := callsFuel_succeeds fuel x state bx
      obtain ⟨⟨y', s2⟩, hy⟩ := callsFuel_succeeds fuel y s1 by'
      obtain ⟨⟨z', s3⟩, hz⟩ := callsFuel_succeeds fuel z s2 bz
      exact ⟨_, by simp [callsFuel, hx, hy, hz]; rfl⟩
    | «let» t xs body =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, s1⟩, hy⟩ := callsListFuel_succeeds fuel xs state bx
      obtain ⟨⟨body', s2⟩, hb⟩ := callsFuel_succeeds fuel body s1 bb
      exact ⟨_, by simp [callsFuel, hy, hb]; rfl⟩
    | raise t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', s1⟩, hx⟩ := callsFuel_succeeds fuel x state bx
      exact ⟨_, by simp [callsFuel, hx]; rfl⟩
    | tick t x =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', s1⟩, hx⟩ := callsFuel_succeeds fuel x state bx
      exact ⟨_, by simp [callsFuel, hx]; rfl⟩
    | handle t x y =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have by' : expBudget y < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨x', s1⟩, hx⟩ := callsFuel_succeeds fuel x state bx
      obtain ⟨⟨y', s2⟩, hy⟩ := callsFuel_succeeds fuel y s1 by'
      exact ⟨_, by simp [callsFuel, hx, hy]; rfl⟩
    | op t op xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, s1⟩, hy⟩ := callsListFuel_succeeds fuel xs state bx
      exact ⟨_, by simp [callsFuel, hy]; rfl⟩
    | call t ticks dest xs =>
      have bx : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, s1⟩, hy⟩ := callsListFuel_succeeds fuel xs state bx
      exact ⟨_, by simp [callsFuel, hy]; rfl⟩
    | app t loc x xs =>
      have bx : expBudget x < fuel := by simp_all [expBudget] <;> omega
      have bs : listBudget xs < fuel := by simp_all [expBudget] <;> omega
      obtain ⟨⟨ys, s1⟩, hy⟩ := callsListFuel_succeeds fuel xs state bs
      obtain ⟨⟨x', s2⟩, hx⟩ := callsFuel_succeeds fuel x s1 bx
      cases loc with
      | none => exact ⟨_, by simp [callsFuel, hy, hx]; rfl⟩
      | some loc =>
        cases known : (sptLookup loc s2.1).isSome <;> cases pure : ClosLang.pure x <;>
          exact ⟨_, by simp [callsFuel, hy, hx, known, pure]; rfl⟩
    | fn name loc ws arity body =>
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      let n := loc.getD 0
      obtain ⟨⟨body', newState⟩, hn⟩ := callsFuel_succeeds fuel body (insertEach n 1 state) bb
      obtain ⟨closed, hc⟩ := closedFuel_succeeds fuel (.fn name loc ws arity body')
      obtain ⟨⟨body'', oldState⟩, ho⟩ := callsFuel_succeeds fuel body state bb
      cases closed <;> exact ⟨_, by simp [callsFuel, n, hn, hc, ho]; rfl⟩
    | letrec names loc ws fns body =>
      have bf : funsBudget fns < fuel := by simp_all [expBudget] <;> omega
      have bb : expBudget body < fuel := by simp_all [expBudget] <;> omega
      have bodiesBound : listBudget (fns.map Prod.snd) < fuel := by rw [bodies_budget]; exact bf
      let n := loc.getD 0
      obtain ⟨⟨bodies, newState⟩, hn⟩ := callsListFuel_succeeds fuel (fns.map Prod.snd)
        (insertEach n fns.length state) bodiesBound
      obtain ⟨closed, hc⟩ := closedFold_succeeds fuel (fns.zip bodies) true
      simp at hc
      obtain ⟨⟨body1, state1⟩, hb1⟩ := callsFuel_succeeds fuel body
        (codeList n ((fns.map Prod.fst).zip bodies) newState) bb
      obtain ⟨⟨bodies2, state2⟩, hn2⟩ := callsListFuel_succeeds fuel (fns.map Prod.snd) state bodiesBound
      obtain ⟨⟨body2, state3⟩, hb2⟩ := callsFuel_succeeds fuel body state2 bb
      cases closed <;> exact ⟨_, by simp [callsFuel, n, hn, hc, hb1, hn2, hb2]; rfl⟩
termination_by fuel

/-- Direct-call conversion of a list succeeds under its structural bound. -/
theorem callsListFuel_succeeds (fuel : Nat) (es : List Exp) (state : State)
    (bound : listBudget es < fuel) : ∃ result, callsListFuel fuel es state = some result := by
  cases es with
  | nil => cases fuel <;> exact ⟨_, rfl⟩
  | cons x xs =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bx : expBudget x < fuel := by simp_all [listBudget] <;> omega
      have bxs : listBudget xs < fuel := by simp_all [listBudget] <;> omega
      obtain ⟨⟨x', s1⟩, hx⟩ := callsFuel_succeeds fuel x state bx
      obtain ⟨⟨xs', s2⟩, hxs⟩ := callsListFuel_succeeds fuel xs s1 bxs
      exact ⟨_, by simp [callsListFuel, hx, hxs]; rfl⟩
termination_by fuel
end

/-- Retrying the direct-call list traversal cannot exhaust fuel. -/
theorem callsListBounded_succeeds (fuel : Nat) (es : List Exp) (state : State) :
    ∃ result, callsListBounded fuel es state = some result := by
  cases h : callsListFuel fuel es state with
  | some result => exact ⟨result, by simp [callsListBounded, h]⟩
  | none =>
    have bound : listBudget es < max fuel (listBudget es + 1) := by omega
    obtain ⟨result, done⟩ := callsListFuel_succeeds (max fuel (listBudget es + 1)) es state bound
    exact ⟨result, by simp [callsListBounded, h, done]⟩

/-- Retrying preserves every previously successful list traversal result. -/
theorem callsListBounded_eq_of_success (fuel : Nat) (es : List Exp) (state : State)
    (result : List Exp × State) (success : callsListFuel fuel es state = some result) :
    callsListBounded fuel es state = some result := by
  simp [callsListBounded, success]

/-- Whole-program direct-call conversion cannot fail from traversal fuel. -/
theorem compileFuel_succeeds (fuel : Nat) (enabled : Bool) (es : List Exp) :
    ∃ result, compileFuel fuel enabled es = some result := by
  cases enabled with
  | false => exact ⟨_, rfl⟩
  | true =>
    obtain ⟨result, h⟩ := callsListBounded_succeeds fuel es (.ln, [])
    exact ⟨result, by simpa [compileFuel] using h⟩

end Flapjack.Compiler.Backend.ClosCall
