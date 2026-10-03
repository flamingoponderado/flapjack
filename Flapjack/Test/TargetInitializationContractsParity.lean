import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts

namespace Flapjack.Test.TargetInitializationContractsParity
open Flapjack

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) (h : startPcOk mc pc)
    (index : Nat) (hi : index < mc.ffiNames.length) :
    holEl index mc.ffiEntryPcs = mc.ffiEntryPcs[index]'(startPcOk_entryBound h hi) :=
  holEl_eq_getElem index mc.ffiEntryPcs (startPcOk_entryBound h hi)

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) (h : startPcOk mc pc) :
    ∃ i, mmioPcsMinIndex mc.ffiNames = some i ∧
      ∀ index (hi : index < mc.ffiNames.length), i ≤ index →
        mc.haltPc ≠ mc.ffiEntryPcs[index]'(startPcOk_entryBound h hi) ∧
        mc.ccachePc ≠ mc.ffiEntryPcs[index]'(startPcOk_entryBound h hi) := by
  have hc := h
  obtain ⟨_, _, _, _, _, _, _, i, hm, _, hs, _⟩ := hc
  refine ⟨i, hm, ?_⟩
  intro index hi hge
  simpa only [holEl_eq_getElem index mc.ffiEntryPcs (startPcOk_entryBound h hi)]
    using hs index ⟨hi, hge⟩

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width)
    (bad : mc.ffiNames.length ≠ mc.ffiEntryPcs.length) : ¬ startPcOk mc pc :=
  fun h => bad (startPcOk_lengths h)

end Flapjack.Test.TargetInitializationContractsParity
