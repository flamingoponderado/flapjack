import Flapjack.Compiler.Backend.RegAlloc.Exceptions

namespace Flapjack.Translator.Monadic.MonadBase

private def ok (s : Nat) : Exc Nat Nat × Nat := (.success 3, s + 1)
private def bad (s : Nat) : Exc Nat Nat × Nat := (.failure 7, s + 2)
private def next (x s : Nat) : Exc Nat Nat × Nat := (.success (x + s), s + 10)

example : bind ok next 4 = (.success 8, 15) := rfl
example : bind bad next 4 = (.failure 7, 6) := rfl
example : ignoreBind ok (next 20) 4 = (.success 25, 15) := rfl
example : ignoreBind bad (next 20) 4 = (.failure 7, 6) := rfl
example : ret (exception := Nat) 3 4 = (.success 3, 4) := rfl
example : run ok 4 = .success 3 := rfl
example : run bad 4 = .failure 7 := rfl
example : arrayAlloc (exception := Nat) (fun xs (_ : List Nat) => xs) 3 7 [9] =
    (.success (), [7, 7, 7]) := rfl
example : arrayAlloc (exception := Nat) (fun xs (_ : List Nat) => xs) 0 7 [9] =
    (.success (), []) := rfl

-- Universal fixtures ensure all four carriers remain independent.
example {S V R E : Type} (s next : S) (error : E) (f : V → M S R E) :
    bind (fun _ => (.failure error, next)) f s = (.failure error, next) := rfl
example {S V E : Type} (s : S) (x : V) : run (ret (exception := E) x) s = .success x := rfl
example : Flapjack.RegAlloc.StateException.Fail [0, 255] ≠ .Subscript := by decide
example : Flapjack.RegAlloc.StateException.Fail [0, 255] ≠ .Fail [255, 0] := by decide

end Flapjack.Translator.Monadic.MonadBase
