import Flapjack.Compiler.Backend.ClosCall.Proofs.Total

/-! Purity preservation by the executable direct-call traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

/-- A successful direct-call traversal preserves purity of expressions and
expression lists. This Lean-side bounded traversal result is not a standalone
HOL theorem; the source `calls_pure` uses the unbounded list traversal. -/
theorem callsFuel_purity : ∀ fuel : Nat,
    (∀ e initial out final, ClosLang.pure e = true → callsFuel fuel e initial = some (out, final) →
      ClosLang.pure out = true) ∧
    (∀ es initial out final, ClosLang.pureList es = true → callsListFuel fuel es initial = some (out, final) →
      ClosLang.pureList out = true) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro e initial out final pure run
      simp [callsFuel] at run
    · intro es initial out final pure run
      cases es with
      | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; rfl
      | cons e es => simp [callsListFuel] at run
  | succ fuel ih =>
    constructor
    · intro e initial out final pure run
      cases e with
      | var trace index =>
        simp [callsFuel] at run
        obtain ⟨rfl, rfl⟩ := run
        rfl
      | ifThenElse trace x y z =>
        simp only [ClosLang.pure, Bool.and_eq_true] at pure
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨x', s1⟩, rx, ⟨y', s2⟩, ry, ⟨z', s3⟩, rz, rfl, rfl⟩ := run
        simp [ClosLang.pure, ih.1 x initial x' s1 pure.1.1 rx,
          ih.1 y s1 y' s2 pure.1.2 ry, ih.1 z s2 z' s3 pure.2 rz]
      | «let» trace xs body =>
        simp only [ClosLang.pure, Bool.and_eq_true] at pure
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨xs', s1⟩, rx, ⟨body', s2⟩, rb, rfl, rfl⟩ := run
        simp [ClosLang.pure, ih.2 xs initial xs' s1 pure.1 rx, ih.1 body s1 body' s2 pure.2 rb]
      | raise trace body => simp [ClosLang.pure] at pure
      | tick trace body => simp [ClosLang.pure] at pure
      | call trace ticks dest args => simp [ClosLang.pure] at pure
      | app trace loc fn args => simp [ClosLang.pure] at pure
      | handle trace body handler =>
        simp only [ClosLang.pure] at pure
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨body', s1⟩, rb, ⟨handler', s2⟩, rh, rfl, rfl⟩ := run
        simpa [ClosLang.pure] using ih.1 body initial body' s1 pure rb
      | op trace op args =>
        simp only [ClosLang.pure, Bool.and_eq_true] at pure
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨args', s1⟩, ra, rfl, rfl⟩ := run
        simp [ClosLang.pure, ih.2 args initial args' s1 pure.1 ra, pure.2]
      | fn name loc vs arity body =>
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
        obtain ⟨⟨body', next⟩, rb, closed, rc, rest⟩ := run
        cases closed <;> simp_all [ClosLang.pure, Option.bind_eq_some_iff]
        · obtain ⟨target, _, rfl⟩ := rest
          rfl
        · obtain ⟨rfl, _⟩ := rest
          rfl
      | letrec names loc vs fns body =>
        simp only [ClosLang.pure] at pure
        simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
        obtain ⟨⟨bodies, next⟩, rb, closed, rc, rest⟩ := run
        cases closed <;> simp_all [Option.bind_eq_some_iff]
        · obtain ⟨bodies', known, entries, _, body', bodyRun, rfl⟩ := rest
          simpa [ClosLang.pure] using ih.1 body known entries body' final.1 final.2 pure (by simpa using bodyRun)
        · obtain ⟨body', bodyRun, rfl⟩ := rest
          simpa [ClosLang.pure] using ih.1 body _ _ body' final.1 final.2 pure (by simpa [codeList] using bodyRun)
    · intro es initial out final pure run
      cases es with
      | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; rfl
      | cons e es =>
        simp only [ClosLang.pureList, Bool.and_eq_true] at pure
        simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
          Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨e', s1⟩, re, ⟨es', s2⟩, rs, rfl, rfl⟩ := run
        simp [ClosLang.pureList, ih.1 e initial e' s1 pure.1 re, ih.2 es s1 es' s2 pure.2 rs]

/-- The production retry wrapper preserves expression-list purity. This
Lean-side bounded result is not a standalone HOL declaration. -/
theorem callsListBounded_purity (fuel : Nat) (es out : List Exp) (initial final : State)
    (pure : ClosLang.pureList es = true) (run : callsListBounded fuel es initial = some (out, final)) :
    ClosLang.pureList out = true := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | none =>
    simp only [first] at run
    exact (callsFuel_purity _).2 es initial out final pure run
  | some result =>
    cases result with
    | mk expressions next =>
      simp only [first, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      exact (callsFuel_purity fuel).2 es initial expressions next pure first

end Flapjack.Compiler.Backend.ClosCall
