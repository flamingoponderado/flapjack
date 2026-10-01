import Mathlib.Logic.Function.Iterate
import Flapjack.Compiler.Encoders.AsmProps.Assertions

/-! Sixteen direct original asmProps observations, including a Bool state
and independent Nat-state/Bool-intermediate iterations. Regressions do not prove HOL-to-Lean equivalence. -/
namespace Flapjack.Test.AsmPropsAssertionsParity
open Flapjack.Compiler.Encoders.AsmProps

private def next (k s : Nat) := 10 * s + k
private def even (s : Nat) : Bool := decide (s % 2 = 0)
private def fi (k : Nat) (b : Bool) : Nat := if b then k else k + 10
private def f (b : Bool) : Nat := if b then 1 else 2
private def relation (s : Nat) (b : Bool) : Prop := b = even s

example : asserts 0 (fun k s : Nat => s + k + 1) 0 (fun _ => False) (· = 1) := by rfl
example : ¬ asserts 0 (fun k s : Nat => s + k + 1) 0 (fun _ => True) (· = 0) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : asserts 3 next 1 (· ≤ 1321) (· = 13210) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : ¬ asserts 3 next 1 (· < 1321) (· = 13210) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : (List.range 3).foldr next 13 = 13210 := by decide +kernel
example : [0, 1, 2].map (fun k =>
    (((List.range (k + 1)).map (3 - ·)).reverse).foldr next 1) = [13, 132, 1321] := by decide +kernel
example : asserts 3 (fun k s => if k ≤ 3 then next k s else 0) 1
    (· ≤ 2000) (· = 13210) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : asserts 2 (fun (_ : Nat) (s : Bool) => !s) true (fun _ => True) (· = false) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : asserts2 0 fi even 0 (fun _ _ => False) := by trivial
example : asserts2 2 fi even 0 relation := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : ¬ asserts2 2 fi even 0 (fun s _ => s < 2) := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : asserts2 2 (fun k b => if k ≤ 2 then fi k b else 99) even 0 relation := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : (0, even 0) = (0, true) := by decide +kernel
example : asserts2 4 (fun _ => f) even 0 relation := by (dsimp [asserts, asserts2, relation]; decide +kernel)
example : [0, 1, 2, 3].map (fun j =>
    let s := (f ∘ even)^[j] 0
    (s, even s)) = [(0, true), (1, false), (2, true), (1, false)] := by decide +kernel
example : ¬ asserts2 1 fi even 0 (fun _ b => b = false) := by (dsimp [asserts, asserts2, relation]; decide +kernel)

def runChecks : IO Bool := do
  IO.println "PASS original generic ASM assertions (16 kernel rows)"
  pure true

end Flapjack.Test.AsmPropsAssertionsParity
