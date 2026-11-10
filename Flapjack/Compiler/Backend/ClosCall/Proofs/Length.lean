module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList

@[expose] public section

/-! Length preservation for the executable direct-call list traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- A successful fuel-bounded traversal produces one expression per input.
This is Flapjack infrastructure: HOL's list traversal is total. -/
theorem callsListFuel_length (fuel : Nat) (es : List Exp) (initial final : State)
    (out : List Exp) (run : callsListFuel fuel es initial = some (out, final)) :
    out.length = es.length := by
  induction fuel generalizing es initial final out with
  | zero =>
    cases es with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; rfl
    | cons e es => simp [callsListFuel] at run
  | succ fuel ih =>
    cases es with
    | nil => simp [callsListFuel] at run; obtain ⟨rfl, _⟩ := run; rfl
    | cons e es =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, _, ⟨es', s2⟩, hs, rfl, _⟩ := run
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih es s1 s2 es' hs)

/-- In a mutually recursive group, pairing converted bodies with their
original arities retains the original number of auxiliary functions. -/
theorem convertedFunctions_length (fuel : Nat) (fns : List (Nat × Exp))
    (initial final : State) (bodies : List Exp)
    (run : callsListFuel fuel (fns.map Prod.snd) initial = some (bodies, final)) :
    ((fns.map Prod.fst).zip bodies).length = fns.length := by
  have length := callsListFuel_length fuel (fns.map Prod.snd) initial final bodies run
  simp only [List.length_map] at length
  simp [List.length_zip, length]

/-- The auxiliary-label range for a converted recursive group has precisely
the size of the input function group. -/
theorem convertedFunctions_labels (fuel loc : Nat) (fns : List (Nat × Exp))
    (initial final : State) (bodies : List Exp)
    (run : callsListFuel fuel (fns.map Prod.snd) initial = some (bodies, final)) :
    (codeList loc ((fns.map Prod.fst).zip bodies) final).2.map Prod.fst =
      ((List.range fns.length).map (fun i => loc + i * 2 + 1)).reverse ++
        final.2.map Prod.fst := by
  rw [codeList_labels, convertedFunctions_length fuel fns initial final bodies run]

end Flapjack.Compiler.Backend.ClosCall
