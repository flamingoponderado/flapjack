import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.Semantics.TargetProps.RegisterOracles
import Flapjack.Compiler.Backend.Semantics.TargetProps.OracleEquality
import Flapjack.Compiler.Backend.Semantics.TargetProps.ConstructedOracles
import Flapjack.Compiler.Backend.Semantics.TargetProps.NextInterference
import Flapjack.Compiler.Backend.Semantics.TargetProps.NextCases
import Flapjack.Compiler.Backend.Semantics.TargetProps.Interference
import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine

set_option autoImplicit false

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Full source positional oracle tie. All four whole native oracle functions
are equated with the actual machine-run constructors. Machine/projection,
compiler configuration and FFI host stay independently generic Type0 carriers;
fixed word64 FP residues and optional positive-width words remain literal. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_def"
  (words_as_type_indexed_bitvec)]
noncomputable def oracleTie {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  s.ioRegs = targetIoRegs mc s.ffi ms ∧ s.ioFpRegs = targetIoFpRegs mc s.ffi ms ∧
  s.ccRegs = targetCcRegs mc s.ffi ms ∧ s.ccFpRegs = targetCcFpRegs mc s.ffi ms

/-- Complete original shifted-search law; equality of constructed oracles is
proved from the actual search results and unchanged configuration fields. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_shift_interfer" (words_as_type_indexed_bitvec)]
theorem oracleTie_shiftInterfer {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms1 ms2 : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F) (l : Nat)
    (h : oracleTie mc ms1 s ∧ ∀ k, findNextInterference mc s.ffi (k + l) ms1 =
      findNextInterference (shiftInterfer l mc) s.ffi k ms2) :
    oracleTie (shiftInterfer l mc) ms2 s := by
  have hn := nextInterferenceShift mc (shiftInterfer l mc) s.ffi s.ffi ms1 ms2 l h.2
  have ho := constructedOraclesEq mc (shiftInterfer l mc) s.ffi s.ffi ms1 ms2
    ⟨hn, rfl, rfl, rfl⟩
  exact ⟨h.1.1.trans ho.1, h.1.2.1.trans ho.2.1,
    h.1.2.2.1.trans ho.2.2.1, h.1.2.2.2.trans ho.2.2.2⟩

/-- Full original source state step, retaining precisely the four unchanged
oracle functions and unchanged FFI state alongside the shifted searches. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_step" (words_as_type_indexed_bitvec)]
theorem oracleTie_step {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms1 ms2 : S)
    (s1 s2 : Flapjack.Compiler.Backend.LabSem.State width C F) (l : Nat)
    (h : oracleTie mc ms1 s1 ∧
      (∀ k, findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) s1.ffi k ms2) ∧
      s2.ioRegs = s1.ioRegs ∧ s2.ioFpRegs = s1.ioFpRegs ∧
      s2.ccRegs = s1.ccRegs ∧ s2.ccFpRegs = s1.ccFpRegs ∧ s2.ffi = s1.ffi) :
    oracleTie (shiftInterfer l mc) ms2 s2 := by
  have ht := oracleTie_shiftInterfer mc ms1 ms2 s1 l ⟨h.1, h.2.1⟩
  simpa only [oracleTie, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2] using ht

/-- All six full original ffi residue/head/tail conclusions, constructed
from the actual next-interference result; no residue is a premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_ffi_step" (words_as_type_indexed_bitvec)]
theorem oracleTie_ffiStep {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (index : Nat) (bytes : List (BitVec 8)) (pre post : S) (mc' : MachineConfig width S Q) (ffi' : HolFfiState F)
    (h : oracleTie mc ms s ∧
      nextInterference mc s.ffi ms = some (.ffiApp index bytes pre post, mc', ffi')) :
    (∀ name r, s.ioRegs 0 name r =
      if r ∈ mc.calleeSavedRegs ∨ ¬ r < mc.target.config.regCount ∨
        r ∈ mc.target.config.avoidRegs then none else some (mc.target.getReg post r)) ∧
    (∀ i, s.ioFpRegs 0 i = mc.target.getFpReg post i) ∧
    targetIoRegs mc' ffi' post = holShiftSeq 1 s.ioRegs ∧
    targetIoFpRegs mc' ffi' post = holShiftSeq 1 s.ioFpRegs ∧
    targetCcRegs mc' ffi' post = s.ccRegs ∧
    targetCcFpRegs mc' ffi' post = s.ccFpRegs := by
  have hc := constructedOraclesFfiStep mc s.ffi ms index bytes pre post mc' ffi'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name r
    simpa only [h.1.1] using (hc 0 r 0 name h.2).1
  · intro i
    simpa only [h.1.2.1] using (hc 0 0 i (.sharedMem .mappedRead) h.2).2.1
  · funext k name r
    simpa only [h.1.1, holShiftSeq] using (hc k r 0 name h.2).2.2.1.symm
  · funext k i
    simpa only [h.1.2.1, holShiftSeq] using
      (hc k 0 i (.sharedMem .mappedRead) h.2).2.2.2.1.symm
  · funext k r
    simpa only [h.1.2.2.1] using (hc k r 0 (.sharedMem .mappedRead) h.2).2.2.2.2.1.symm
  · funext k i
    simpa only [h.1.2.2.2] using
      (hc k 0 i (.sharedMem .mappedRead) h.2).2.2.2.2.2.symm

/-- All six full original cache residue/head/tail conclusions, constructed
from the actual next-interference result; no residue is a premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_ccache_step" (words_as_type_indexed_bitvec)]
theorem oracleTie_cacheStep {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (a1 a2 : BitVec width) (pre post : S) (mc' : MachineConfig width S Q) (ffi' : HolFfiState F)
    (h : oracleTie mc ms s ∧
      nextInterference mc s.ffi ms = some (.ccApp a1 a2 pre post, mc', ffi')) :
    (∀ r, s.ccRegs 0 r =
      if r ∈ mc.calleeSavedRegs ∨ r = mc.ptrReg ∨ ¬ r < mc.target.config.regCount ∨
        r ∈ mc.target.config.avoidRegs then none else some (mc.target.getReg post r)) ∧
    (∀ i, s.ccFpRegs 0 i = mc.target.getFpReg post i) ∧
    targetCcRegs mc' ffi' post = holShiftSeq 1 s.ccRegs ∧
    targetCcFpRegs mc' ffi' post = holShiftSeq 1 s.ccFpRegs ∧
    targetIoRegs mc' ffi' post = s.ioRegs ∧
    targetIoFpRegs mc' ffi' post = s.ioFpRegs := by
  have hc := constructedOraclesCcStep mc s.ffi ms a1 a2 pre post mc' ffi'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    simpa only [h.1.2.2.1] using (hc 0 r 0 (.sharedMem .mappedRead) h.2).1
  · intro i
    simpa only [h.1.2.2.2] using (hc 0 0 i (.sharedMem .mappedRead) h.2).2.1
  · funext k r
    simpa only [h.1.2.2.1, holShiftSeq] using (hc k r 0 (.sharedMem .mappedRead) h.2).2.2.1.symm
  · funext k i
    simpa only [h.1.2.2.2, holShiftSeq] using
      (hc k 0 i (.sharedMem .mappedRead) h.2).2.2.2.1.symm
  · funext k name r
    simpa only [h.1.1] using (hc k r 0 name h.2).2.2.2.2.1.symm
  · funext k i
    simpa only [h.1.2.1] using
      (hc k 0 i (.sharedMem .mappedRead) h.2).2.2.2.2.2.symm

/-- Complete original ffi next-state tie, including all four actual updated
oracle functions and the returned FFI state. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_ffi_next" (words_as_type_indexed_bitvec)]
theorem oracleTie_ffiNext {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s1 s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (index : Nat) (bytes : List (BitVec 8)) (pre post : S) (mc' : MachineConfig width S Q) (ffi' : HolFfiState F)
    (h : oracleTie mc ms s1 ∧
      nextInterference mc s1.ffi ms = some (.ffiApp index bytes pre post, mc', ffi') ∧
      s2.ioRegs = holShiftSeq 1 s1.ioRegs ∧
      s2.ioFpRegs = holShiftSeq 1 s1.ioFpRegs ∧
      s2.ccRegs = s1.ccRegs ∧ s2.ccFpRegs = s1.ccFpRegs ∧ s2.ffi = ffi') :
    oracleTie mc' post s2 := by
  have hp := oracleTie_ffiStep mc ms s1 index bytes pre post mc' ffi' ⟨h.1, h.2.1⟩
  simp only [oracleTie, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2]
  exact ⟨hp.2.2.1.symm, hp.2.2.2.1.symm, hp.2.2.2.2.1.symm, hp.2.2.2.2.2.symm⟩

/-- Complete original cache next-state tie, including all four actual updated
oracle functions and the returned FFI state. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_ccache_next" (words_as_type_indexed_bitvec)]
theorem oracleTie_cacheNext {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s1 s2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (a1 a2 : BitVec width) (pre post : S) (mc' : MachineConfig width S Q) (ffi' : HolFfiState F)
    (h : oracleTie mc ms s1 ∧
      nextInterference mc s1.ffi ms = some (.ccApp a1 a2 pre post, mc', ffi') ∧
      s2.ccRegs = holShiftSeq 1 s1.ccRegs ∧
      s2.ccFpRegs = holShiftSeq 1 s1.ccFpRegs ∧
      s2.ioRegs = s1.ioRegs ∧ s2.ioFpRegs = s1.ioFpRegs ∧ s2.ffi = ffi') :
    oracleTie mc' post s2 := by
  have hp := oracleTie_cacheStep mc ms s1 a1 a2 pre post mc' ffi' ⟨h.1, h.2.1⟩
  simp only [oracleTie, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2]
  exact ⟨hp.2.2.2.2.1.symm, hp.2.2.2.2.2.symm, hp.2.2.1.symm, hp.2.2.2.1.symm⟩

/-- Flapjack natural-key ALOOKUP infrastructure: both native implementations
read the first equal key with the same equality, including duplicate keys. -/
private theorem alookup_eq_lookup {α : Type} (key : Nat) (entries : List (Nat × α)) :
    sptAListLookup key entries = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨k, value⟩
    by_cases h : key = k
    · simp [sptAListLookup, List.lookup, h]
    · cases hb : (key == k) with
      | false => simp [sptAListLookup, List.lookup, h, hb, ih]
      | true => exact False.elim (h (by simpa only [beq_iff_eq] using hb))

/-- Full original external-call residue theorem. The returned register
functions are derived from the actual external interference and read/FFI guards,
not assumed as a simulation premise. Literal total holEl is retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "oracle_tie_ExtCall_residues" (words_as_type_indexed_bitvec)]
theorem oracleTie_extCallResidues {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms1 ms2 : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (l index : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (bytes bytes2 newBytes : List (BitVec 8)) (newFfi : HolFfiState F) (t : AsmState width)
    (h : oracleTie mc ms1 s ∧
      (∀ k, findNextInterference mc s.ffi (k + l) ms1 =
        findNextInterference { mc with nextInterfer := holShiftSeq l mc.nextInterfer } s.ffi k ms2) ∧
      ¬ (mc.progAddresses (mc.target.getPc ms2) ∧ mc.target.getPc ms2 ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms2 ≠ mc.haltPc ∧ mc.target.getPc ms2 ≠ mc.ccachePc ∧
      Misc.findIndex (mc.target.getPc ms2) mc.ffiEntryPcs 0 = some index ∧
      holEl index mc.ffiNames = .extCall name ∧ mc.mmioInfo.lookup index = none ∧
      readFfiBytearraysHOL mc ms2 = (some bytes, some bytes2) ∧
      callFFIHOL s.ffi (.extCall name) bytes bytes2 = .ret newFfi newBytes) :
    (fun a => getRegValue (s.ioRegs 0 (.extCall name) a) (t.regs a) id) =
      (fun a => if a ∈ mc.calleeSavedRegs ∨ ¬ a < mc.target.config.regCount ∨
        a ∈ mc.target.config.avoidRegs then t.regs a else
          mc.target.getReg (mc.ffiInterfer 0 (index, newBytes, ms2)) a) ∧
    (fun n => s.ioFpRegs 0 n) =
      (fun n => mc.target.getFpReg (mc.ffiInterfer 0 (index, newBytes, ms2)) n) := by
  let mc2 := { mc with nextInterfer := holShiftSeq l mc.nextInterfer }
  have hn := nextInterferenceShift mc mc2 s.ffi s.ffi ms1 ms2 l h.2.1
  have he := nextInterferenceExtCall mc2 s.ffi ms2 index name bytes bytes2 newBytes newFfi (by
    simpa only [mc2, readFfiBytearraysHOL, readFfiBytearrayHOL, alookup_eq_lookup] using h.2.2)
  have hp := oracleTie_ffiStep mc ms1 s index newBytes ms2
    (mc.ffiInterfer 0 (index, newBytes, ms2))
    { mc2 with ffiInterfer := holShiftSeq 1 mc2.ffiInterfer } newFfi ⟨h.1, hn.trans he⟩
  constructor
  · funext a
    rw [hp.1 (.extCall name) a]
    split <;> rfl
  · funext n
    exact hp.2.1 n

/-- Actual whole-state oracle construction satisfies the complete tie for any
machine/state, not just a selected register. Flapjack infrastructure with no
independently named original HOL theorem. -/
theorem oracleTie_install {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    oracleTie mc ms { s with
      ioRegs := targetIoRegs mc s.ffi ms
      ioFpRegs := targetIoFpRegs mc s.ffi ms
      ccRegs := targetCcRegs mc s.ffi ms
      ccFpRegs := targetCcFpRegs mc s.ffi ms } := ⟨rfl, rfl, rfl, rfl⟩

end Flapjack.Compiler.Backend.LabToTarget
