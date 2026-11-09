module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList

@[expose] public section

/-! Preservation of previously generated direct-call code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- Generating auxiliary code retains the previous code as a suffix. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_list_IS_SUFFIX"]
theorem codeListSource_suffix {A B C : Type} (loc : Nat) (fns : List (A × B))
    (state : C × List (Nat × A × B)) : state.2 <:+ (codeListSource loc fns state).2 := by
  induction fns generalizing loc state with
  | nil => simp [codeListSource]
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    obtain ⟨known, code⟩ := state
    change code <:+ (codeListSource (loc + 2) rest
      (known, (loc + 1, arity, body) :: code)).2
    exact (List.suffix_cons (loc + 1, arity, body) code).trans
      (ih (loc + 2) (known, (loc + 1, arity, body) :: code))

/-- The executable code-list generator retains the previous code. -/
theorem codeList_suffix (loc : Nat) (fns : List (Nat × Exp)) (state : State) :
    state.2 <:+ (codeList loc fns state).2 := by
  rw [codeList_eq_source]
  exact codeListSource_suffix loc fns state

mutual
/-- Successful direct-call conversion preserves previously emitted code. -/
theorem callsFuel_suffix (fuel : Nat) (e : Exp) (initial final : State) (out : Exp)
    (run : callsFuel fuel e initial = some (out, final)) : initial.2 <:+ final.2 := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var tr n => simp [callsFuel] at run; obtain ⟨_, rfl⟩ := run; simp
    | ifThenElse tr x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, _, rfl⟩ := run
      exact (callsFuel_suffix fuel x initial s1 x' hx).trans
        ((callsFuel_suffix fuel y s1 s2 y' hy).trans (callsFuel_suffix fuel z s2 s3 z' hz))
    | «let» tr xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, _, rfl⟩ := run
      exact (callsListFuel_suffix fuel xs initial s1 xs' hx).trans
        (callsFuel_suffix fuel body s1 s2 body' hb)
    | raise tr x | tick tr x =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, _, rfl⟩ := run
      exact callsFuel_suffix fuel x initial s1 x' hx
    | handle tr x y =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, _, rfl⟩ := run
      exact (callsFuel_suffix fuel x initial s1 x' hx).trans
        (callsFuel_suffix fuel y s1 s2 y' hy)
    | call tr ticks dest xs | op tr dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, _, rfl⟩ := run
      exact callsListFuel_suffix fuel xs initial s1 xs' hx
    | app tr loc x xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨x', s2⟩, hy, rest⟩ := run
      have endState : s2 = final := by
        cases loc <;> simp only at rest
        all_goals repeat' split at rest
        all_goals simp_all only [Option.some.injEq, Prod.mk.injEq]
      subst final
      exact (callsListFuel_suffix fuel xs initial s1 xs' hx).trans
        (callsFuel_suffix fuel x s1 s2 x' hy)
    | fn name loc ws arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', _, rfl⟩ := rest
        exact callsFuel_suffix fuel body initial s2 body'' hb'
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        have before := callsFuel_suffix fuel body (insertEach (loc.getD 0) 1 initial) s1 body' hb
        simp only [insertEach] at before
        exact before.trans (List.suffix_cons _ _)
    | letrec names loc ws fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, _, rfl⟩ := rest
        exact (callsListFuel_suffix fuel (fns.map Prod.snd) initial s2 bodies' hb').trans
          (callsFuel_suffix fuel body s2 s3 body' he)
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq,
          Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, _, rfl⟩ := rest
        have before := callsListFuel_suffix fuel (fns.map Prod.snd)
          (insertEach (loc.getD 0) fns.length initial) s1 bodies hb
        simp only [insertEach] at before
        exact before.trans ((codeList_suffix _ _ _).trans
          (callsFuel_suffix fuel body _ s2 body' he))
termination_by fuel

/-- The list traversal also retains the incoming code as a suffix. -/
theorem callsListFuel_suffix (fuel : Nat) (es : List Exp) (initial final : State)
    (out : List Exp) (run : callsListFuel fuel es initial = some (out, final)) :
    initial.2 <:+ final.2 := by
  cases es with
  | nil => simp [callsListFuel] at run; obtain ⟨_, rfl⟩ := run; simp
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, _, rfl⟩ := run
      exact (callsFuel_suffix fuel e initial s1 e' he).trans
        (callsListFuel_suffix fuel es s1 s2 es' hs)
termination_by fuel
end

/-- The production retry wrapper preserves prior code for either successful
fuel budget. -/
theorem callsListBounded_suffix (fuel : Nat) (es : List Exp) (initial final : State)
    (out : List Exp) (run : callsListBounded fuel es initial = some (out, final)) :
    initial.2 <:+ final.2 := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | some result =>
    simp only [first, Option.some.injEq] at run
    subst result
    exact callsListFuel_suffix fuel es initial final out first
  | none =>
    simp only [first] at run
    exact callsListFuel_suffix _ es initial final out run

end Flapjack.Compiler.Backend.ClosCall
