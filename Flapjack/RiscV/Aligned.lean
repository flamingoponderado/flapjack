namespace Flapjack.RiscV.L3

/-- The original HOL `aligned p w` premise of the evaluated memory-load step
theorems: the low `p` bits of the address word are clear, i.e. the word is equal
to itself masked with the complement of `2 ^ p - 1`.  This is Flapjack-only
infrastructure (no separate HOL theorem) mirroring HOL's `alignmentTheory`
predicate, kept outside the pinned `RiscV/L3/{Defs,Step}` rendering closure. -/
def aligned (p : Nat) {w : Nat} (x : BitVec w) : Prop :=
  x &&& ~~~(BitVec.ofNat w (2 ^ p - 1)) = x

end Flapjack.RiscV.L3
