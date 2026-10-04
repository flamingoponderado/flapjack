import Flapjack.Compiler.Backend.Semantics.TargetProps.FindNextInterference

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source305: increasing the clock limit preserves every successful
result, including the returned configuration and FFI state. No validity or
bounds hypothesis is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findNextInterferenceMono {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (k : Nat) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (res : InterferenceApp width S × MachineConfig width S Q × HolFfiState σ)
    (i : Nat) (h : findNextInterference mc ffi k ms = some res) :
    findNextInterference mc ffi (k + i) ms = some res := by
  induction k generalizing mc ffi ms with
  | zero => simp [findNextInterference] at h
  | succ k ih =>
    have hi : k + 1 + i = (k + i) + 1 := by omega
    rw [hi]
    simp only [findNextInterference] at h ⊢
    split at h
    · rename_i hn
      rw [if_pos hn]
      split at h
      · rename_i he
        rw [if_pos he]
        split at h
        · rename_i hg
          rw [if_pos hg]
          exact ih _ _ _ h
        · cases h
      · cases h
    · rename_i hn
      rw [if_neg hn]
      exact h

/-- Literal source319: successful searches at any two clock limits return the
same whole application/configuration/FFI tuple. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findNextInterferenceUnique {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (k1 k2 : Nat)
    (res1 res2 : InterferenceApp width S × MachineConfig width S Q × HolFfiState σ)
    (h : findNextInterference mc ffi k1 ms = some res1 ∧
      findNextInterference mc ffi k2 ms = some res2) : res1 = res2 := by
  have h1 := findNextInterferenceMono k1 mc ffi ms res1 k2 h.1
  have h2 := findNextInterferenceMono k2 mc ffi ms res2 k1 h.2
  rw [Nat.add_comm k2 k1] at h2
  exact Option.some.inj (h1.symm.trans h2)

end Flapjack.Compiler.Backend.Semantics.TargetProps
