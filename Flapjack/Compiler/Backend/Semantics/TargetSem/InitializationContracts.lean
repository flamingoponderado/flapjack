import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Misc.FindIndex

namespace Flapjack
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc

/-- Full original start-PC contract: all four domain exclusions, both
address equations, bit alignment, the existential MMIO boundary, every
external-prefix search/exclusion and shared-suffix exclusion, and the final
length equality. Every EL occurs under the original suffix bound; the original
length equality makes that bound an entry-PC bound. No past-end default is
observed or chosen, and no extra outer bound is introduced. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "start_pc_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def startPcOk {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) : Prop :=
  ¬ mc.progAddresses mc.haltPc ∧
  ¬ mc.progAddresses mc.ccachePc ∧
  ¬ mc.sharedAddresses mc.haltPc ∧
  ¬ mc.sharedAddresses mc.ccachePc ∧
  pc - BitVec.ofNat width ffiOffset = mc.haltPc ∧
  pc - BitVec.ofNat width (2 * ffiOffset) = mc.ccachePc ∧
  (1 &&& pc) = 0 ∧
  ∃ i, mmioPcsMinIndex mc.ffiNames = some i ∧
    (∀ index, index < i →
      ¬ mc.progAddresses (pc - BitVec.ofNat width ((3 + index) * ffiOffset)) ∧
      ¬ mc.sharedAddresses (pc - BitVec.ofNat width ((3 + index) * ffiOffset)) ∧
      pc - BitVec.ofNat width ((3 + index) * ffiOffset) ≠ mc.haltPc ∧
      pc - BitVec.ofNat width ((3 + index) * ffiOffset) ≠ mc.ccachePc ∧
      findIndex (pc - BitVec.ofNat width ((3 + index) * ffiOffset))
        mc.ffiEntryPcs 0 = some index) ∧
    (∀ index, index < mc.ffiNames.length ∧ i ≤ index →
      mc.haltPc ≠ holEl index mc.ffiEntryPcs ∧
      mc.ccachePc ≠ holEl index mc.ffiEntryPcs) ∧
    mc.ffiNames.length = mc.ffiEntryPcs.length

/-- Flapjack infrastructure exposing the original contract's length clause;
there is no separate HOL declaration being ported. -/
theorem startPcOk_lengths {width : Nat} [NeZero width] {S Q : Type}
    {mc : MachineConfig width S Q} {pc : BitVec width} (h : startPcOk mc pc) :
    mc.ffiNames.length = mc.ffiEntryPcs.length := by
  obtain ⟨_, _, _, _, _, _, _, i, _, _, _, hl⟩ := h
  exact hl

/-- Flapjack infrastructure discharging the actual entry-PC bound from the
source name bound and source length equality, without strengthening the tag. -/
theorem startPcOk_entryBound {width : Nat} [NeZero width] {S Q : Type}
    {mc : MachineConfig width S Q} {pc : BitVec width} (h : startPcOk mc pc)
    {index : Nat} (hi : index < mc.ffiNames.length) : index < mc.ffiEntryPcs.length := by
  simpa only [startPcOk_lengths h] using hi

end Flapjack
