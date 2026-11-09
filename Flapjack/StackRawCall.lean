module

public import Flapjack.Stack

@[expose] public section

namespace Flapjack

def stackRawCallFrameLookup : Nat → List (Nat × Nat) → Option Nat
  | _, [] => none
  | label, (candidate, words) :: entries =>
      if label = candidate then some words
      else stackRawCallFrameLookup label entries

end Flapjack
