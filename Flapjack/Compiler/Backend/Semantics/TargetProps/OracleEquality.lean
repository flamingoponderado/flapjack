import Flapjack.Compiler.Backend.Semantics.TargetProps.SequenceLaws
import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source599: initial next-interference equality implies all predicate counts are equal. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem interferenceCountEq {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc1 mc2 : MachineConfig width S Q) (ffi1 ffi2 : HolFfiState σ) (ms1 ms2 : S)
    (h : nextInterference mc1 ffi1 ms1 = nextInterference mc2 ffi2 ms2) :
    ∀ n, interferenceCount P mc1 ffi1 ms1 n = interferenceCount P mc2 ffi2 ms2 n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [interferenceCount, interferenceCount, ih,
      interferenceAppSeqEq mc1 mc2 ffi1 ffi2 ms1 ms2 h n]

/-- Literal source609: the original four conjuncts imply equality of all four complete oracle functions. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem constructedOraclesEq {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc1 mc2 : MachineConfig width S Q)
    (ffi1 ffi2 : HolFfiState σ) (ms1 ms2 : S)
    (h : nextInterference mc1 ffi1 ms1 = nextInterference mc2 ffi2 ms2 ∧
      mc1.target = mc2.target ∧ mc1.calleeSavedRegs = mc2.calleeSavedRegs ∧
      mc1.ptrReg = mc2.ptrReg) :
    targetIoRegs mc1 ffi1 ms1 = targetIoRegs mc2 ffi2 ms2 ∧
    targetIoFpRegs mc1 ffi1 ms1 = targetIoFpRegs mc2 ffi2 ms2 ∧
    targetCcRegs mc1 ffi1 ms1 = targetCcRegs mc2 ffi2 ms2 ∧
    targetCcFpRegs mc1 ffi1 ms1 = targetCcFpRegs mc2 ffi2 ms2 := by
  have hs := interferenceAppSeqEq mc1 mc2 ffi1 ffi2 ms1 ms2 h.1
  have hc := fun P => interferenceCountEq P mc1 mc2 ffi1 ffi2 ms1 ms2 h.1
  have hp : ∀ P k, interferencePos P mc1 ffi1 ms1 k = interferencePos P mc2 ffi2 ms2 k := by
    intro P k
    unfold interferencePos
    congr 1
    funext n
    rw [hc P n, hs n]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext k name r
    simp only [targetIoRegs, hp, hs, h.2.1, h.2.2.1]
  · funext k i
    simp only [targetIoFpRegs, hp, hs, h.2.1]
  · funext k r
    simp only [targetCcRegs, hp, hs, h.2.1, h.2.2.1, h.2.2.2]
  · funext k i
    simp only [targetCcFpRegs, hp, hs, h.2.1]

end Flapjack.Compiler.Backend.Semantics.TargetProps
