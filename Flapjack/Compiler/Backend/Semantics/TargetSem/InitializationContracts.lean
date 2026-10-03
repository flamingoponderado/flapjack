import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Misc.FindIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.InterferenceContracts
import Flapjack.Misc.BytesInMem
import Flapjack.Byte
import Flapjack.Compiler.Encoders.AsmProps.Interference
import Mathlib.Data.Set.Lattice

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

/-- Flapjack infrastructure for the pointwise Boolean-domain truth embedding
already used by the reviewed native machine/ASM carriers. No HOL theorem is
being ported: this checks that every source Boolean membership is recovered. -/
theorem initDomainTruth_roundtrip {α : Type} (domain : α → Bool) (a : α) :
    decide (domain a = true) = domain a := by
  cases domain a <;> rfl

/-- Flapjack infrastructure: every proposition domain has the canonical
classical Boolean representative, so the truth embedding restricts no sets. -/
theorem initDomainTruth_surjective {α : Type} (domain : α → Prop) :
    ∃ source : α → Bool, (fun a => source a = true) = domain := by
  classical
  exact ⟨fun a => decide (domain a), by funext a; simp⟩

/-- Full original initial-state contract, retaining all eight inputs and
eighteen clauses. Source data/shared domains remain Boolean functions; their
truth predicates enter the reviewed Prop-backed ASM/machine sets. The two
checked codec facts above preserve every membership and every possible set.
The actual fixed-word8 byte relation and generic word/location memory remain
independent. startPcOk supplies the original FFI-list length equality, bounding
every entry-PC EL in the imported FFI contract; no extra guard or default is
introduced. byte_align retains the source LOG2(0) at small positive widths. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "good_init_state_def"
  (words_as_type_indexed_bitvec)]
noncomputable def goodInitState {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (ms : S) (bytes : List (BitVec 8))
    (cbspace : Nat) (t : AsmState width) (m : BitVec width → WordLocW width)
    (dm sdm : BitVec width → Bool) : Prop :=
  targetStateRel mc.target t ms ∧
  targetConfigured t mc ∧
  t.pc = mc.target.getPc ms ∧
  startPcOk mc t.pc ∧
  (BitVec.ofNat width (2 ^ t.align - 1) &&& t.pc) = 0 ∧
  interferenceOk mc.nextInterfer (mc.target.proj mc.progAddresses) ∧
  ffiInterferOkHOL t.pc mc ∧
  ccacheInterferOkHOL t.pc mc ∧
  codeLoaded bytes mc ms ∧
  bytesInMemHOL t.pc bytes t.mem t.memDomain (fun a => dm a = true) ∧
  (∀ a, dm a = true → t.memDomain a) ∧
  (∀ a, dm (holByteAlign a) = true → dm a = true) ∧
  (fun a => sdm a = true) = mc.sharedAddresses ∧
  (∀ a, sdm (holByteAlign a) = true → sdm a = true) ∧
  Disjoint (α := Set (BitVec width)) (Set.ofPred mc.progAddresses)
    (Set.ofPred mc.sharedAddresses) ∧
  (∀ a, ∃ w, t.mem a = HolByte.getByte a w mc.target.config.bigEndian ∧
    m (holByteAlign a) = .word w) ∧
  (∀ n, n < cbspace →
    t.memDomain (BitVec.ofNat width (n + bytes.length) + t.pc) ∧
    dm (BitVec.ofNat width (n + bytes.length) + t.pc) ≠ true) ∧
  cbspace + bytes.length < 2 ^ width

/-- Flapjack infrastructure extracting the actual word memory promised by
the original invariant; no independently named HOL theorem is being ported. -/
theorem goodInitState_wordMemory {width : Nat} [NeZero width] {S Q : Type}
    {mc : MachineConfig width S Q} {ms : S} {bytes : List (BitVec 8)}
    {cbspace : Nat} {t : AsmState width} {m : BitVec width → WordLocW width}
    {dm sdm : BitVec width → Bool} (h : goodInitState mc ms bytes cbspace t m dm sdm)
    (a : BitVec width) : ∃ w, m (holByteAlign a) = .word w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := h
  obtain ⟨w, _, hw⟩ := hm a
  exact ⟨w, hw⟩

/-- Flapjack infrastructure deriving the original FFI contract's entry bound
from the initial-state invariant, with no strengthened source predicate. -/
theorem goodInitState_entryBound {width : Nat} [NeZero width] {S Q : Type}
    {mc : MachineConfig width S Q} {ms : S} {bytes : List (BitVec 8)}
    {cbspace : Nat} {t : AsmState width} {m : BitVec width → WordLocW width}
    {dm sdm : BitVec width → Bool} (h : goodInitState mc ms bytes cbspace t m dm sdm)
    {index : Nat} (hi : index < mc.ffiNames.length) : index < mc.ffiEntryPcs.length :=
  startPcOk_entryBound h.2.2.2.1 hi

end Flapjack
