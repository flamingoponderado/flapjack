import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! Replays successful and failing callback observations from the pinned HOL
backend-oracle probe. -/
open Flapjack.Compiler.Backend.BackendProps

#guard stateCc (fun (s p : Nat) => (s + 1, p + 2))
    (fun (c p : Nat) => some (p, true, c + 3)) (4, 5) 6 ==
  some (8, true, 5, 8)

#guard stateCc (fun (s p : Nat) => (s + 1, p + 2))
    (fun (_ _ : Nat) => (none : Option (Nat × Bool × Nat))) (4, 5) 6 ==
  none
