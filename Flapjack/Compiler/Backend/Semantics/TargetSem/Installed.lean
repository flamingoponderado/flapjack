import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Misc.WordList
import Flapjack.Misc.SetSep
import Flapjack.Misc.Alignment

/-!
# HOL `targetSem` `installed_def`

`installed_def` (`cakeml/compiler/backend/semantics/targetSemScript.sml:472-510`): the
compiled bytes, code-buffer space, bitmaps and FFI are installed into the machine.
-/

namespace Flapjack

/-- Exact HOL `installed_def` (`targetSemScript.sml:477-510`). HOL's sets of addresses are
    Boolean domains, as in the tagged `good_init_state_def` this definition calls:
    `{w | t.regs r1 <=+ w ∧ w <+ t.regs r2}` is the decided unsigned range, `∪` is `||`,
    `DISJOINT` is pointwise exclusion, and `byte_aligned ∩ bitmaps_dm` is the conjunction of
    the two memberships. HOL's unsigned `<=+`/`<+`/`≤₊` are `BitVec` `≤`/`<`; `bytes_in_word`
    is `n2w (dimindex (:α) DIV 8)` (`StackRemove.bytesInWord`); `GENLIST f n` is
    `(List.range n).map f`; `ZIP` is on equal-length lists; `dimword (:α)` is `2 ^ width`.
    HOL's paired argument `(r1,r2)` is `regs`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def installed {width : Nat} [NeZero width] {S Q : Type} (bytes : List (BitVec 8)) (cbspace : Nat)
    (bitmaps : List (BitVec width)) (dataSp : Nat) (ffiNames : Option (List HolFfiName))
    (regs : Nat × Nat) (mc : MachineConfig width S Q)
    (shmemExtra : List Compiler.Backend.LabToTarget.ShmemInfoNum) (ms : S) : Prop :=
  ∃ (t : AsmState width) (m : BitVec width → WordLocW width) (bitmapPtr : BitVec width)
    (bitmapsDm sdm : BitVec width → Bool),
    let bytesInWord := Compiler.Backend.StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool :=
      fun w => decide (t.regs regs.1 ≤ w ∧ w < t.regs regs.2)
    goodInitState mc ms bytes cbspace t m (fun w => heapStackDm w || bitmapsDm w) sdm ∧
    holByteAligned (t.regs regs.1) = true ∧
    holByteAligned (t.regs regs.2) = true ∧
    holByteAligned bitmapPtr = true ∧
    t.regs regs.1 ≤ t.regs regs.2 ∧
    1024 * bytesInWord ≤ t.regs regs.2 - t.regs regs.1 ∧
    (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
    m (t.regs regs.1) = .word bitmapPtr ∧
    m (t.regs regs.1 + bytesInWord) =
      .word (bitmapPtr + bytesInWord * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs regs.1 + 2 * bytesInWord) =
      .word (bitmapPtr + bytesInWord * BitVec.ofNat width dataSp +
        bytesInWord * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs regs.1 + 3 * bytesInWord) =
      .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
    m (t.regs regs.1 + 4 * bytesInWord) =
      .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
    SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
      (Misc.wordListExists (bitmapPtr + bytesInWord * BitVec.ofNat width bitmaps.length) dataSp)
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) ∧
    ffiNames = some mc.ffiNames ∧
    (∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range shmemExtra.length).map (fun index => index + i))
          (shmemExtra.map fun rec => (rec.nbytes,
            Compiler.Encoders.Asm.HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + Compiler.Backend.LabToTarget.ffiOffset * (i + 3) < 2 ^ width)

end Flapjack
