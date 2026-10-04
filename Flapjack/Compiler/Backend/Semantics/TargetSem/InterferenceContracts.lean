import Flapjack.Compiler.Backend.Semantics.TargetSem.FfiReads
import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.PostAsm
import Flapjack.Compiler.Backend.LabToTarget.Encoding
import Flapjack.Byte.WordOfBytes
import Flapjack.Misc.Alignment
import Flapjack.Misc.Sptree

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget

/-- Full original FFI interference contract: ordinary calls and both MMIO
branches, with every original universal variable and existential info witness.
Inherited total holEl/holHd retains shared opaque holHdNil/holArb past the end;
no bounds or fallback are added. The fixed word8 payload uses BitVec 8 and the
reviewed native HOL byte decoder, not an alternative byte carrier. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def ffiInterferOkHOL {width : Nat} [NeZero width] {S Q : Type}
    (pc : BitVec width) (mc : MachineConfig width S Q) : Prop :=
  ∀ (ms2 : S) (k index : Nat) (newBytes : List (BitVec 8)) (t1 : AsmState width)
    (bytes bytes2 : List (BitVec 8)) (i : Nat),
    index < mc.ffiNames.length ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
      mc.progAddresses = t1.memDomain →
      (index < i →
        readFfiBytearraysHOL mc ms2 = (some bytes, some bytes2) ∧
        newBytes.length = bytes2.length ∧
        (holEl index mc.ffiNames = .extCall (.implode []) → newBytes = bytes2) ∧
        targetStateRel mc.target
          { t1 with pc := -BitVec.ofNat width ((3 + index) * ffiOffset) + pc } ms2 ∧
        holAligned mc.target.config.codeAlignment
          (t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n)) = true →
        let ms' := mc.ffiInterfer k (index, newBytes, ms2)
        mc.target.stateOk ms' = true ∧
        mc.target.getPc ms' =
          t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n) ∧
        (∀ a, t1.memDomain a → mc.target.getByte ms' a =
          asmWriteBytearrayHOL (t1.regs mc.ptr2Reg) newBytes t1.mem a) ∧
        (∀ r, r ∈ mc.calleeSavedRegs ∧ r < mc.target.config.regCount ∧
          r ∉ mc.target.config.avoidRegs → mc.target.getReg ms' r = t1.regs r)) ∧
      (i ≤ index ∧
        targetStateRel mc.target { t1 with pc := holEl index mc.ffiEntryPcs } ms2 →
        ∃ info, sptAListLookup index mc.mmioInfo = some info ∧
          (holEl index mc.ffiNames = .sharedMem .mappedRead →
            ∀ newBytes : List (BitVec 8),
              targetStateRel mc.target
                { t1 with
                  pc := info.2.2.2
                  regs := fun n => if n = info.2.2.1 then
                    HolByte.wordOfBytes false 0 newBytes else t1.regs n }
                (mc.ffiInterfer k (index, newBytes, ms2))) ∧
          (holEl index mc.ffiNames = .sharedMem .mappedWrite →
            targetStateRel mc.target { t1 with pc := info.2.2.2 }
              (mc.ffiInterfer k (index, newBytes, ms2))))

/-- Full original cache-clear interference contract, including return PC,
all program-domain bytes and the saved-or-pointer register promises. This
retains the literal whole native states and every source antecedent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def ccacheInterferOkHOL {width : Nat} [NeZero width] {S Q : Type}
    (pc : BitVec width) (mc : MachineConfig width S Q) : Prop :=
  ∀ (ms2 : S) (t1 : AsmState width) (k : Nat) (a1 a2 : BitVec width),
    targetStateRel mc.target
      { t1 with pc := -BitVec.ofNat width (2 * ffiOffset) + pc } ms2 ∧
    holAligned mc.target.config.codeAlignment
      (t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n)) = true →
    let ms' := mc.ccacheInterfer k (a1, a2, ms2)
    mc.target.stateOk ms' = true ∧
    mc.target.getPc ms' =
      t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n) ∧
    (∀ a, t1.memDomain a → mc.target.getByte ms' a = t1.mem a) ∧
    (∀ r, (r ∈ mc.calleeSavedRegs ∨ r = mc.ptrReg) ∧
      r < mc.target.config.regCount ∧ r ∉ mc.target.config.avoidRegs →
      mc.target.getReg ms' r = t1.regs r)

end Flapjack
