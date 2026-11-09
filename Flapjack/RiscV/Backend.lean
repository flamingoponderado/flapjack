module

public import Flapjack.Word
public import Flapjack.RiscV.Model
public import Flapjack.RiscV.RegisterMap

@[expose] public section

/-!
The first executable Word-to-RISC-V instruction-selection slice.

This is intentionally a partial compiler. It covers the Word fragment made of
`skip`, assignments, sequencing, equality/order/bit-test conditionals,
constants, register reads, binary arithmetic, shifts, and selected memory
operations. Zero conditions use the architectural x0 register; nonzero
immediate conditions materialize their operand in the reserved x31 scratch
register. Bit tests use either `AND` or `ANDI` and branch on the resulting
temporary. The option-valued interface makes the current boundary explicit
while the remaining Word instructions are ported.
-/

namespace Flapjack.RiscV

/-! Constructor equation for the Cake constant boundary.  Keep this named
    equation beside the definition so correctness clients can rewrite through
    the checked list-valued API without unfolding unrelated instruction cases. -/

def wordMoveRegisterDestinations (moves : List (Nat × Nat)) : List Nat :=
  moves.map (fun move => move.1)

def wordMoveRegisterRemoveDestination (destination : Nat) :
    List (Nat × Nat) → List (Nat × Nat) :=
  List.filter (fun move => move.1 != destination)

def wordMoveRegisterReady (destinations : List Nat) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | move :: moves =>
      if move.1 = move.2 ∨ move.2 ∉ destinations then
        some move
      else
        wordMoveRegisterReady destinations moves
termination_by moves => sizeOf moves
decreasing_by all_goals decreasing_trivial

/-! Variant for a function whose entry may equal the caller continuation in a
    compact linked test image.  It executes the first entry instruction before
    delegating to `executeCodeUntil`, so the initial state is never mistaken
    for an already-returned computation. -/

def rotateRight [NeZero width] (value : Word width) (amount : Nat) : Word width :=
  BitVec.ushiftRight value (amount % width) |||
    BitVec.shiftLeft value ((width - amount % width) % width)

/-! Function-level equations expose the same checked constant boundary through
    the return carrier used by theorem-facing function compilation. -/

theorem shiftAmount_ofNat_of_lt [NeZero width] {amount : Nat} (h : amount < width) :
    shiftAmount (BitVec.ofNat width amount) = amount := by
  unfold shiftAmount
  rw [BitVec.toNat_ofNat]
  have hpow : width ≤ 2 ^ width := by
    have haux : ∀ n : Nat, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          cases n with
          | zero => simp
          | succ n =>
              rw [Nat.pow_succ]
              calc
                n + 2 ≤ (n + 1) * 2 := by omega
                _ ≤ 2 ^ (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
    exact haux width
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h hpow), Nat.mod_eq_of_lt h]

end Flapjack.RiscV
