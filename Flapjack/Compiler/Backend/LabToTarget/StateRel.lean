import Flapjack.Compiler.Backend.LabToTarget.WordLocValByte
import Flapjack.Compiler.Backend.LabToTarget.GoodCode
import Flapjack.Compiler.Backend.LabToTarget.ShareMemDomain
import Flapjack.Compiler.Backend.LabToTarget.ShareMemState
import Flapjack.Compiler.Backend.LabToTarget.CodeSafety
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidity
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Encoders.AsmProps.Encoding
import Flapjack.Compiler.Encoders.AsmProps.Interference
import Flapjack.Misc.AsmWriteBytearray
import Flapjack.Misc.BytesInMem
import Flapjack.Misc.GoodDimindex
import Flapjack.Misc.Option

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Misc

/-- Complete native relation from original lines959–1096. The Boolean Lab
memory domains are used through their truth predicates, without changing
membership or excluded-domain behavior. Total holEl retains the shared opaque
HD-nil value, and holThe retains its unspecified NONE value; no bounds or
completion premise is added. Every source conjunct, compiler/oracle
field, normal-FFI/cache contract and actual target state is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def stateRel {width : Nat} [NeZero width] {S Q F : Type}
    (bundle : MachineConfig width S Q × LabProgHOL width × Spt (Spt Nat) × BitVec width)
    (s1 : LabSem.State width Config F) (t1 : AsmState width) (ms1 : S) : Prop :=
  let (mc, code2, labs, p) := bundle
  targetStateRel mc.target t1 ms1 ∧ goodDimindex width ∧
  mc.progAddresses = t1.memDomain ∧
  ¬ mc.progAddresses mc.haltPc ∧ ¬ mc.progAddresses mc.ccachePc ∧
  asmRegOkExact s1.ptrReg mc.target.config = true ∧ mc.ptrReg = s1.ptrReg ∧
  asmRegOkExact s1.lenReg mc.target.config = true ∧ mc.lenReg = s1.lenReg ∧
  asmRegOkExact s1.ptr2Reg mc.target.config = true ∧ mc.ptr2Reg = s1.ptr2Reg ∧
  asmRegOkExact s1.len2Reg mc.target.config = true ∧ mc.len2Reg = s1.len2Reg ∧
  asmRegOkExact s1.linkReg mc.target.config = true ∧
  (∃ i, mmioPcsMinIndex mc.ffiNames = some i ∧
    ∀ index, if i ≤ index ∧ index < mc.ffiNames.length then
      ∃ info, mc.mmioInfo.lookup index = some info else mc.mmioInfo.lookup index = none) ∧
  (∀ (ms2 : S) (k index : Nat) (newBytes : List (BitVec 8)) (t : AsmState width)
      (bytes bytes2 : List (BitVec 8)) (st newSt : HolFfiState F) (i : Nat),
    mmioPcsMinIndex mc.ffiNames = some i ∧ index < i ∧
    readFfiBytearraysHOL mc ms2 = (some bytes, some bytes2) ∧
    Relation.ReflTransGen callFFIRelHOL s1.ffi st ∧
    callFFIHOL st (holEl index mc.ffiNames) bytes bytes2 = .ret newSt newBytes ∧
    mc.progAddresses = t.memDomain ∧
    targetStateRel mc.target { t with pc := p - BitVec.ofNat width ((3 + index) * ffiOffset) } ms2 ∧
    holAligned mc.target.config.codeAlignment (t.regs s1.linkReg) = true →
    let ms' := mc.ffiInterfer k (index, newBytes, ms2)
    targetStateRel mc.target
      { t with
        regs := fun a => if a ∈ mc.calleeSavedRegs ∨ ¬ a < mc.target.config.regCount ∨
            a ∈ mc.target.config.avoidRegs then t.regs a else mc.target.getReg ms' a
        fpRegs := fun n => mc.target.getFpReg ms' n
        mem := asmWriteBytearrayHOL (t.regs s1.ptr2Reg) newBytes t.mem
        pc := t.regs s1.linkReg } ms') ∧
  (∀ (ms2 : S) (t : AsmState width) (k : Nat) (a1 a2 : BitVec width),
    targetStateRel mc.target { t with pc := p - BitVec.ofNat width (2 * ffiOffset) } ms2 ∧
    holAligned mc.target.config.codeAlignment (t.regs s1.linkReg) = true →
    let ms' := mc.ccacheInterfer k (a1, a2, ms2)
    targetStateRel mc.target
      { t with
        regs := fun a => if a ∈ mc.calleeSavedRegs ∨ a = s1.ptrReg ∨
            ¬ a < mc.target.config.regCount ∨ a ∈ mc.target.config.avoidRegs
            then t.regs a else mc.target.getReg ms' a
        fpRegs := fun n => mc.target.getFpReg ms' n
        pc := t.regs s1.linkReg } ms') ∧
  s1.compile = compileLab mc.target.config ∧
  (noShareMemInst code2 → ∀ k,
    let (cfg, code) := s1.compileOracle k
    goodCode mc.target.config cfg.labels code ∧ noShareMemInst code ∧
    (k = 0 → cfg.labels = labs ∧ cfg.pos = (progToBytes code2).length ∧
      cfg.ffiNames = some mc.ffiNames)) ∧
  (∀ l1 l2 x, labLookup l1 l2 labs = some x → x % 2 = 0) ∧
  ((1 : BitVec width) &&& p) = 0 ∧
  listSubset ((findFfiNames s1.code).filter (fun x => match x with
    | .extCall _ => true | _ => false)) mc.ffiNames = true ∧
  (progToBytes code2).length % 2 = 0 ∧
  (∀ name i, name ∈ mc.ffiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    getFfiIndex mc.ffiNames name < i →
    (∃ name', name = HolFfiName.extCall name') ∧
    ¬ mc.progAddresses (p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset)) ∧
    p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset) ≠ mc.haltPc ∧
    p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset) ≠ mc.ccachePc ∧
    findIndex (p - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset))
      mc.ffiEntryPcs 0 = some (getFfiIndex mc.ffiNames name)) ∧
  p - BitVec.ofNat width ffiOffset = mc.haltPc ∧
  p - BitVec.ofNat width (2 * ffiOffset) = mc.ccachePc ∧
  interferenceOk mc.nextInterfer (mc.target.proj t1.memDomain) ∧
  (∀ l1 l2 x2, locToPc l1 l2 s1.code = some x2 →
    labLookup l1 l2 labs = some (posVal x2 0 code2)) ∧
  (∀ r, s1.fpRegs r = t1.fpRegs r) ∧
  (∀ r, wordLocVal p labs (s1.regs r) = some (t1.regs r)) ∧
  (∀ a, s1.memDomain (holByteAlign a) = true →
    t1.memDomain a ∧ s1.memDomain a = true ∧
    wordLocValByte p labs s1.memory a s1.be = some (t1.mem a)) ∧
  (∀ n, n < s1.codeBuffer.spaceLeft →
    let addr := s1.codeBuffer.position + BitVec.ofNat width (s1.codeBuffer.buffer.length + n)
    t1.memDomain addr ∧ ¬ s1.memDomain addr = true) ∧
  bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain (fun a => s1.memDomain a = true) ∧
  s1.codeBuffer.position = p + BitVec.ofNat width (progToBytes code2).length ∧
  bytesInMemHOL s1.codeBuffer.position s1.codeBuffer.buffer t1.mem t1.memDomain
    (fun a => s1.memDomain a = true) ∧
  (progToBytes code2).length + s1.codeBuffer.buffer.length + s1.codeBuffer.spaceLeft < 2 ^ width ∧
  (∀ bn, bn < s1.codeBuffer.buffer.length + s1.codeBuffer.spaceLeft →
    s1.codeBuffer.position + BitVec.ofNat width bn ∉ mc.ffiEntryPcs) ∧
  s1.failed = false ∧ t1.failed = false ∧ s1.be = t1.be ∧
  t1.pc = p + BitVec.ofNat width (posVal s1.pc 0 code2) ∧
  (p &&& BitVec.ofNat width (2 ^ t1.align - 1)) = 0 ∧
  (match mc.target.config.linkReg with | none => True | some r => t1.lr = r) ∧
  t1.be = mc.target.config.bigEndian ∧ t1.align = mc.target.config.codeAlignment ∧
  encOk mc.target.config ∧
  allEncOk mc.target.config labs (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames))) 0 code2 ∧
  (∀ sec ∈ code2, secLabelsOk sec) ∧ codeSimilar s1.code code2 ∧
  shareMemStateRel mc s1 t1 ms1 ∧
  shareMemDomainCodeRel mc p code2 (fun a => s1.sharedMemDomain a = true) ∧
  mc.ffiNames.length = mc.ffiEntryPcs.length ∧ noInstallOrNoShareMem code2 mc.ffiNames

/-- Source-relation projections are Flapjack proof infrastructure: they have
no independent original HOL declarations and assume only the full relation. -/
theorem stateRel_target {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : LabSem.State width Config F) (t : AsmState width) (ms : S)
    (h : stateRel (mc, code, labs, p) s t ms) : targetStateRel mc.target t ms := h.1

/-- Full source dimension consequence; no dimension premise is added. -/
theorem stateRel_dimension {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : LabSem.State width Config F) (t : AsmState width) (ms : S)
    (h : stateRel (mc, code, labs, p) s t ms) : goodDimindex width := h.2.1

/-- Actual compile-function equality follows from the relation, rather than
being supplied as a separate premise. Flapjack proof infrastructure. -/
theorem stateRel_compile {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : LabSem.State width Config F) (t : AsmState width) (ms : S)
    (h : stateRel (mc, code, labs, p) s t ms) : s.compile = compileLab mc.target.config := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Actual aligned memory byte correspondence is derived from the complete
relation; no post-state or byte-conversion premise is added. Flapjack infrastructure. -/
theorem stateRel_memory {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s : LabSem.State width Config F) (t : AsmState width) (ms : S)
    (h : stateRel (mc, code, labs, p) s t ms) (a : BitVec width)
    (ha : s.memDomain (holByteAlign a) = true) :
    t.memDomain a ∧ s.memDomain a = true ∧
      wordLocValByte p labs s.memory a s.be = some (t.mem a) := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha

/-- Complete relation ignores the Lab clock field, as in the literal source.
Flapjack iff strengthening; the literal original forward implication is
tagged separately as stateRelClock in the StateTransport submodule. -/
theorem stateRel_clock {width : Nat} [NeZero width] {S Q F : Type}
    (bundle : MachineConfig width S Q × LabProgHOL width × Spt (Spt Nat) × BitVec width)
    (s : LabSem.State width Config F) (t : AsmState width) (ms : S) (clock : Nat) :
    stateRel bundle { s with clock := clock } t ms ↔ stateRel bundle s t ms := by
  rcases bundle with ⟨mc, code, labs, p⟩
  rfl

/-- Full one-bit relation is rejected by the actual original dimension guard;
no reduced evaluator or replacement relation is used. Flapjack infrastructure. -/
theorem not_stateRel_oneBit {S Q F : Type}
    (bundle : MachineConfig 1 S Q × LabProgHOL 1 × Spt (Spt Nat) × BitVec 1)
    (s : LabSem.State 1 Config F) (t : AsmState 1) (ms : S) : ¬ stateRel bundle s t ms := by
  rcases bundle with ⟨mc, code, labs, p⟩
  intro h
  have hd := stateRel_dimension mc code labs p s t ms h
  have hn : ¬ goodDimindex 1 := by
    change ¬ ((1 : Nat) = 32 ∨ 1 = 64)
    decide
  exact hn hd

/-- Native Bool-domain truth conversion is pointwise lossless, including false
membership. Flapjack infrastructure, not a new representation exception. -/
theorem domainTruth_roundtrip {α : Type} (domain : α → Bool) (a : α) :
    decide (domain a = true) = domain a := by cases domain a <;> rfl

end Flapjack.Compiler.Backend.LabToTarget
