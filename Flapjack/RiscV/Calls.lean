module

public import Flapjack.RiscV.Backend

@[expose] public section

/-!
Call-target tables for Word programs: each target records a function label,
its entry address, and its parameter and return registers.
-/

namespace Flapjack.RiscV

structure WordCallContext (width : Nat) [NeZero width] where
  targets : List (Nat × Word width × List Nat × List Nat)

def lookupWordCallTarget [NeZero width] (label : Nat) :
    List (Nat × Word width × List Nat × List Nat) →
      Option (Word width × List Nat × List Nat)
  | [] => none
  | (candidate, entry, parameters, returns) :: targets =>
      if label == candidate then some (entry, parameters, returns)
      else lookupWordCallTarget label targets

end Flapjack.RiscV
