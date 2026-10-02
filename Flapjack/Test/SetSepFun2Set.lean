import Flapjack.Misc.SetSep

namespace Flapjack.Test.SetSepFun2Set
open Flapjack.SetSep

-- Kernel counterparts of the independent original generic-carrier rows.
example : fun2Set ((fun n : Nat => n == 0), fun n => n = 0 ∨ n = 1) (0, true) := by
  simp [fun2SetThm]
example : fun2Set ((fun n : Nat => n == 0), fun n => n = 0 ∨ n = 1) (1, false) := by
  simp [fun2SetThm]
example : ¬ fun2Set ((fun n : Nat => n == 0), fun n => n = 0 ∨ n = 1) (1, true) := by
  simp [fun2SetThm]
example : ¬ fun2Set ((fun n : Nat => n == 0), fun n => n = 0 ∨ n = 1) (2, false) := by
  simp [fun2SetThm]
example : ¬ fun2Set ((fun n : Nat => n + 1), fun _ => False) (0, 1) := by
  simp [fun2SetThm]
example : fun2Set ((fun b : Bool => if b then 7 else 11), fun b => b = true ∨ b = false)
    (true, 7) := by simp [fun2SetThm]
example : fun2Set ((fun b : Bool => if b then 7 else 11), fun b => b = true ∨ b = false)
    (false, 11) := by simp [fun2SetThm]
example : fun2Set ((fun b : Bool => (3, b)), fun b => b = true ∨ b = false)
    (false, (3, false)) := by simp [fun2SetThm]
example : fun2Set ((fun _ : Nat => 0), fun n => n = 1 ∨ n = 2) (2, 0) := by
  simp [fun2SetThm]

-- The full theorem also applies to infinite domains and independently typed
-- values; the finite probes are not a finiteness premise of the declaration.
example (f : Nat → Bool) (address : Nat) : fun2Set (f, fun _ => True) (address, f address) :=
  (fun2SetThm f _ address _).2 ⟨rfl, trivial⟩

end Flapjack.Test.SetSepFun2Set
