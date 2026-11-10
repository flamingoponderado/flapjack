module

public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

-- Checks below run compiled code from these modules.
public meta import Flapjack.Compiler.Backend.BackendProps.StateCompiler
@[expose] public section

/-! Replays successful and failing callback observations from the pinned HOL
backend-oracle probe. -/
open Flapjack.Compiler.Backend.BackendProps

#guard stateCc (fun (s p : Nat) => (s + 1, p + 2))
    (fun (c p : Nat) => some (p, true, c + 3)) (4, 5) 6 ==
  some (8, true, 5, 8)

#guard stateCc (fun (s p : Nat) => (s + 1, p + 2))
    (fun (_ _ : Nat) => (none : Option (Nat × Bool × Nat))) (4, 5) 6 ==
  none

-- Captured by backend_props_state_oracle_probe.out.
#guard (stateOracStates (fun (s p : Nat) => (2 * s + p, s + p)) 3 (fun n => n + 1) 3,
    stateCoProgs (fun (s p : Nat) => (2 * s + p, s + p)) 3 (fun n => n + 1) 2,
    addStateCo (fun (s p : Nat) => (2 * s + p, s + p)) 3 (fun xs i => xs i + 10) (fun n => n + 1) 2) ==
  (35, 19, 16, 29)
