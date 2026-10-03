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

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (ms : S) (bytes : List (BitVec 8))
    (space : Nat) (t : AsmState width) (m : BitVec width → WordLocW width)
    (dm sdm : BitVec width → Bool)
    (h : goodInitState mc ms bytes space t m dm sdm) (index : Nat)
    (hi : index < mc.ffiNames.length) :
    holEl index mc.ffiEntryPcs =
      mc.ffiEntryPcs[index]'(goodInitState_entryBound h hi) :=
  holEl_eq_getElem index mc.ffiEntryPcs (goodInitState_entryBound h hi)

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (ms : S) (bytes : List (BitVec 8))
    (space : Nat) (t : AsmState width) (m : BitVec width → WordLocW width)
    (dm sdm : BitVec width → Bool)
    (h : goodInitState mc ms bytes space t m dm sdm) (a : BitVec width)
    (secId label : Nat) : m (holByteAlign a) ≠ .loc secId label := by
  obtain ⟨w, hw⟩ := goodInitState_wordMemory h a
  simp [hw]

example {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (ms : S) (bytes : List (BitVec 8))
    (space : Nat) (t : AsmState width) (m : BitVec width → WordLocW width)
    (dm sdm : BitVec width → Bool)
    (bad : 2 ^ width ≤ space + bytes.length) :
    ¬ goodInitState mc ms bytes space t m dm sdm := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs⟩ := h
  omega

end Flapjack.Test.TargetInitializationContractsParity
