import Flapjack.Translator.Monadic.MonadBase.Arrays
import Flapjack.Compiler.Backend.RegAlloc.StExMap
namespace Flapjack.Test.MonadArraysParity
open Translator.Monadic.MonadBase RegAlloc
-- Replay of the eleven original monad_arrays_probe rows (HOL `FST` getter and
-- `\a s. (a, SND s)` setter on a list-and-flag state). Finite observations only.
abbrev St := List Nat × Bool
def getA : St → List Nat := Prod.fst
def setA (a : List Nat) (s : St) : St := (a, s.2)
example : msub (0 : Nat) 1 [5, 6, 7] = .success 6 := by decide +kernel
example : msub (0 : Nat) 3 [5, 6, 7] = .failure 0 := by decide +kernel
example : mupdate (0 : Nat) 9 1 [5, 6, 7] = .success [5, 9, 7] := by decide +kernel
example : mupdate (0 : Nat) 9 3 [5, 6, 7] = .failure 0 := by decide +kernel
example : (arrayLength (exception := Nat) getA ([1, 2], true)) = (.success 2, ([1, 2], true)) :=
  rfl
example : arraySub getA (0 : Nat) 1 ([1, 2], true) = (.success 2, ([1, 2], true)) := by
  decide +kernel
example : arraySub getA (0 : Nat) 2 ([1, 2], true) = (.failure 0, ([1, 2], true)) := by
  decide +kernel
example : arrayUpdate getA setA (0 : Nat) 1 9 ([1, 2], true) = (.success (), ([1, 9], true)) := by
  decide +kernel
example : arrayUpdate getA setA (0 : Nat) 5 9 ([1, 2], true) = (.failure 0, ([1, 2], true)) := by
  decide +kernel
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (x + 1) : Exc Nat Nat), s + 1))
    [1, 2, 3] 0 = (.success [2, 3, 4], 3) := by decide +kernel
example : stExMap (fun (x : Nat) (s : Nat) =>
    if x = 2 then ((.failure 7 : Exc Nat Nat), s + 10) else (.success x, s + 1))
    [1, 2, 3] 0 = (.failure 7, 11) := by decide +kernel
end Flapjack.Test.MonadArraysParity
