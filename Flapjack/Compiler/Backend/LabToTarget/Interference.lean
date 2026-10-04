import Flapjack.Compiler.Backend.Semantics.TargetProps.Interference

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shiftInterfer_zero {width : Nat} [NeZero width] {state projection : Type}
    : (shiftInterfer 0 : MachineConfig width state projection →
        MachineConfig width state projection) = id := by
  funext config
  have horacle : holShiftSeq 0 config.nextInterfer = config.nextInterfer := by
    funext index
    simp [holShiftSeq]
  change { config with nextInterfer := holShiftSeq 0 config.nextInterfer } = config
  rw [horacle]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem shiftInterfer_twice {width : Nat} [NeZero width] {state projection : Type}
    (l' l : Nat) (config : MachineConfig width state projection) :
    shiftInterfer l' (shiftInterfer l config) = shiftInterfer (l + l') config := by
  rw [shiftInterfer_intro, Nat.add_comm]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ffiEntryPcsDisjoint_shorter {width : Nat} [NeZero width] {state projection : Type}
    (config : MachineConfig width state projection) (s : AsmState width) (l1 l2 : Nat) :
    ffiEntryPcsDisjoint config s l1 ∧ l2 ≤ l1 → ffiEntryPcsDisjoint config s l2 := by
  rintro ⟨hdisjoint, hle⟩ address ⟨hmem, n, hn, heq⟩
  exact hdisjoint address ⟨hmem, n, Nat.lt_of_lt_of_le hn hle, heq⟩

end Flapjack.Compiler.Backend.LabToTarget
