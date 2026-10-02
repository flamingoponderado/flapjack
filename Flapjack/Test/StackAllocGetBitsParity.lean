import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas

/-!
# `stack_allocProof` `get_bits`: original-oracle rows

Kernel replay of `scripts/hol-probes/stack_alloc_get_bits_probe.out`.
-/

namespace Flapjack.Test.StackAllocGetBitsParity

open Flapjack.StackSem Flapjack.Compiler.Backend.StackAlloc

-- get_bits_11=[T; T; F]
example : getBits (11 : BitVec 8) = [true, true, false] := by
  simp [getBits, bitLength_eq]; decide
-- get_bits_1=[]
example : getBits (1 : BitVec 8) = [] := by
  simp [getBits, bitLength_eq]
-- get_bits_0=[]
example : getBits (0 : BitVec 8) = [] := by
  simp [getBits, bitLength_eq]
-- get_bits_msb_64=[T; F; T; F; ...] (63 bits)
example : getBits (0x8000000000000005 : BitVec 64) =
    [true, false, true] ++ List.replicate 60 false := by
  rw [← getBits_intro (by decide)]
  decide

def runChecks : IO Bool := do
  IO.println "PASS stack_allocProof get_bits matches four original HOL rows"
  pure true

end Flapjack.Test.StackAllocGetBitsParity
