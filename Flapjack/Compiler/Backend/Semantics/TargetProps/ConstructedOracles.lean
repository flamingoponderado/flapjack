import Flapjack.Compiler.Backend.Semantics.TargetProps.PositionTail
import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles
import Flapjack.Compiler.Backend.Semantics.TargetProps.SearchConst

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source527: the complete six-conjunct constructed FFI oracle step. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem constructedOraclesFfiStep {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q)
    (ffi : HolFfiState σ) (ms : S) (index : Nat) (bytes : List (BitVec 8)) (pre post : S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (k r i : Nat) (name : HolFfiName)
    (h : nextInterference mc ffi ms = some (.ffiApp index bytes pre post, mc', ffi')) :
    targetIoRegs mc ffi ms 0 name r =
      (if r ∈ mc.calleeSavedRegs ∨ ¬ r < mc.target.config.regCount ∨ r ∈ mc.target.config.avoidRegs then none else some (mc.target.getReg post r)) ∧
    targetIoFpRegs mc ffi ms 0 i = mc.target.getFpReg post i ∧
    targetIoRegs mc ffi ms (k + 1) name r = targetIoRegs mc' ffi' post k name r ∧
    targetIoFpRegs mc ffi ms (k + 1) i = targetIoFpRegs mc' ffi' post k i ∧
    targetCcRegs mc ffi ms k r = targetCcRegs mc' ffi' post k r ∧
    targetCcFpRegs mc ffi ms k i = targetCcFpRegs mc' ffi' post k i := by
  have hconst := nextInterferenceConst mc ffi ms (.ffiApp index bytes pre post) mc' ffi' h
  have hz := interferencePosHead (fun app => isFfiApp app = true)
    mc ffi ms (.ffiApp index bytes pre post) mc' ffi' ⟨h, by simp [isFfiApp]⟩
  have hh := interferencePosTailHit (fun app => isFfiApp app = true)
    mc ffi ms (.ffiApp index bytes pre post) mc' ffi' k ⟨h, by simp [isFfiApp]⟩
  have hm := interferencePosTailMiss (fun app => ¬ isFfiApp app = true)
    mc ffi ms (.ffiApp index bytes pre post) mc' ffi' k ⟨h, by simp [isFfiApp]⟩
  have hs := interferenceAppSeqTail mc ffi ms (.ffiApp index bytes pre post) mc' ffi' h
  have hzero : interferenceAppSeq mc ffi ms 0 = some (.ffiApp index bytes pre post, mc', ffi') := h
  simp only [appPost] at hz hh hm hs
  simp at hz hh hm
  cases hi : interferencePos (fun app => isFfiApp app = true) mc' ffi' post k <;>
    cases hc : interferencePos (fun app => ¬ isFfiApp app = true) mc' ffi' post k <;>
    simp at hc <;>
    simp [targetIoRegs, targetIoFpRegs, targetCcRegs, targetCcFpRegs,
      hz, hh, hm, hzero, hi, hc, hs, hconst.1, hconst.2.1, hconst.2.2]

/-- Literal source563: the complete six-conjunct constructed cache oracle step. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem constructedOraclesCcStep {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q)
    (ffi : HolFfiState σ) (ms : S) (a1 a2 : BitVec width) (pre post : S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (k r i : Nat) (name : HolFfiName)
    (h : nextInterference mc ffi ms = some (.ccApp a1 a2 pre post, mc', ffi')) :
    targetCcRegs mc ffi ms 0 r =
      (if r ∈ mc.calleeSavedRegs ∨ r = mc.ptrReg ∨ ¬ r < mc.target.config.regCount ∨ r ∈ mc.target.config.avoidRegs then none else some (mc.target.getReg post r)) ∧
    targetCcFpRegs mc ffi ms 0 i = mc.target.getFpReg post i ∧
    targetCcRegs mc ffi ms (k + 1) r = targetCcRegs mc' ffi' post k r ∧
    targetCcFpRegs mc ffi ms (k + 1) i = targetCcFpRegs mc' ffi' post k i ∧
    targetIoRegs mc ffi ms k name r = targetIoRegs mc' ffi' post k name r ∧
    targetIoFpRegs mc ffi ms k i = targetIoFpRegs mc' ffi' post k i := by
  have hconst := nextInterferenceConst mc ffi ms (.ccApp a1 a2 pre post) mc' ffi' h
  have hz := interferencePosHead (fun app => ¬ isFfiApp app = true)
    mc ffi ms (.ccApp a1 a2 pre post) mc' ffi' ⟨h, by simp [isFfiApp]⟩
  have hh := interferencePosTailHit (fun app => ¬ isFfiApp app = true)
    mc ffi ms (.ccApp a1 a2 pre post) mc' ffi' k ⟨h, by simp [isFfiApp]⟩
  have hm := interferencePosTailMiss (fun app => isFfiApp app = true)
    mc ffi ms (.ccApp a1 a2 pre post) mc' ffi' k ⟨h, by simp [isFfiApp]⟩
  have hs := interferenceAppSeqTail mc ffi ms (.ccApp a1 a2 pre post) mc' ffi' h
  have hzero : interferenceAppSeq mc ffi ms 0 = some (.ccApp a1 a2 pre post, mc', ffi') := h
  simp only [appPost] at hz hh hm hs
  simp at hz hh hm
  cases hi : interferencePos (fun app => isFfiApp app = true) mc' ffi' post k <;>
    cases hc : interferencePos (fun app => ¬ isFfiApp app = true) mc' ffi' post k <;>
    simp at hc <;>
    simp [targetIoRegs, targetIoFpRegs, targetCcRegs, targetCcFpRegs,
      hz, hh, hm, hzero, hi, hc, hs, hconst.1, hconst.2.1, hconst.2.2]

end Flapjack.Compiler.Backend.Semantics.TargetProps
