import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceSequence

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source383: Initial whole next-interference result equality gives full sequence equality for every n; no additional context premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem interferenceAppSeqEq {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc1 mc2 : MachineConfig width S Q)
    (ffi1 ffi2 : HolFfiState σ) (ms1 ms2 : S)
    (h : nextInterference mc1 ffi1 ms1 = nextInterference mc2 ffi2 ms2) :
    ∀ n, interferenceAppSeq mc1 ffi1 ms1 n = interferenceAppSeq mc2 ffi2 ms2 n := by
  intro n
  cases n <;> simp only [interferenceAppSeq, h]

/-- Literal source391: Exact successful first result gives every successor suffix at returned configuration, FFI and appPost; no changed clock or oracle. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem interferenceAppSeqTail {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (app : InterferenceApp width S) (mc' : MachineConfig width S Q)
    (ffi' : HolFfiState σ) (h : nextInterference mc ffi ms = some (app, mc', ffi')) :
    ∀ n, interferenceAppSeq mc ffi ms (n + 1) =
      interferenceAppSeq mc' ffi' (appPost app) n := by
  intro n
  simp only [interferenceAppSeq, h]

/-- Literal source399: Arbitrary predicate count at m is at most count at m+i for all i,m; no presence or success assumption. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem interferenceCountMono {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) :
    ∀ i m, interferenceCount P mc ffi ms m ≤ interferenceCount P mc ffi ms (m + i) := by
  intro i m
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.add_succ, interferenceCount]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

end Flapjack.Compiler.Backend.Semantics.TargetProps
