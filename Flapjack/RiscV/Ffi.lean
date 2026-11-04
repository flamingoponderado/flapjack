import Flapjack.RiscV.Calls
import Flapjack.RiscV.Backend

/-!
FFI service tables for Word programs: each foreign function name maps to its
numeric service identifier.
-/

namespace Flapjack.RiscV

structure WordFfiContext where
  services : List (FunName × Nat)

def lookupWordFfiService (function : FunName) :
    List (FunName × Nat) → Option Nat
  | [] => none
  | (candidate, service) :: services =>
      if function == candidate then some service
      else lookupWordFfiService function services

def lookupWordFfiIndex (function : FunName) :
    List (FunName × Nat) → Option Nat
  | [] => none
  | (candidate, _) :: services =>
      if function == candidate then some 0
      else (lookupWordFfiIndex function services).map (· + 1)

theorem lookupWordFfiService_shape :
    lookupWordFfiService "sum" [("sum", 7), ("other", 8)] = some 7 := by
  rfl

/-- Call targets together with the FFI service table. -/
structure WordCallFfiContext (width : Nat) [NeZero width] where
  targets : List (Nat × Word width × List Nat × List Nat)
  services : List (FunName × Nat)

end Flapjack.RiscV
