import Flapjack.Compiler.Encoders.AsmProps.Assertions.Iteration

/-! Non-vacuous applications of all six full original assertion theorems.
Inputs agree with the direct original ASM assertion observations. -/
namespace Flapjack.Test.AsmPropsAssertionsIterationParity
open Flapjack.Compiler.Encoders.AsmProps

private def next (k s : Nat) := 10 * s + k
private def even (s : Nat) : Bool := decide (s % 2 = 0)
private def fi (k : Nat) (b : Bool) : Nat := if b then k else k + 10
private def f (b : Bool) : Nat := if b then 1 else 2
private def relation (s : Nat) (b : Bool) : Prop := b = even s

-- Non-vacuous applications of each complete source theorem.
example : (List.range 3).foldr next (next 3 1) = 13210 :=
  asserts_foldr_countList 3 next 1 (· ≤ 1321) (· = 13210) (by (dsimp [asserts, asserts2, relation]; decide +kernel))

example : ((((List.range 3).map (3 - ·)).reverse).foldr next 1) ≤ 1321 :=
  asserts_foldr_countList_less 2 3 next 1 (· ≤ 1321) (· = 13210)
    ⟨by (dsimp [asserts, asserts2, relation]; decide +kernel), by decide⟩

example : asserts 3 (fun k s => if k ≤ 3 then next k s else 0) 1
    (· ≤ 2000) (· = 13210) := by
  apply asserts_weaken 3 next _ 1 (· ≤ 1321) (· ≤ 2000) (· = 13210)
  · intro k hk
    constructor
    · funext s; simp [hk]
    · intro hp; exact Nat.le_trans hp (by decide)
  · (dsimp [asserts, asserts2, relation]; decide +kernel)

example : asserts2 2 (fun k b => if k ≤ 2 then fi k b else 99) even 0 relation := by
  apply asserts2_changeInterfer 2 fi _ even 0 relation
  constructor
  · (dsimp [asserts, asserts2, relation]; decide +kernel)
  · intro k hk; funext b; simp [hk]

example : relation 0 (even 0) :=
  asserts2_first 2 fi even 0 relation ⟨by decide, by (dsimp [asserts, asserts2, relation]; decide +kernel)⟩

example : relation ((f ∘ even)^[2] 0) (even ((f ∘ even)^[2] 0)) :=
  asserts2_every 4 0 2 f even relation ⟨by (dsimp [asserts, asserts2, relation]; decide +kernel), by decide⟩

def runChecks : IO Bool := do
  IO.println "PASS original generic ASM assertion iteration (6 full theorem applications)"
  pure true

end Flapjack.Test.AsmPropsAssertionsIterationParity
