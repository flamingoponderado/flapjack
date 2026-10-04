import Flapjack.Compiler.Backend.Semantics.TargetSem.Installed
import Flapjack.Pancake.Proofs.PanToTarget

/-!
# `pan_to_targetProof`: `pan_installed`

`pan_installed_def` (`cakeml/pancake/proofs/pan_to_targetProofScript.sml:290-326`) strengthens
targetSem `installed` by fixing the initial word memory on a domain and the shared-memory
domain; `pan_installed_imp_installed` (328-334) forgets these.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack

/-- HOL `pan_installed_def` (`pan_to_targetProofScript.sml:290-326`). HOL's two parameter
    sets `p_dom` and `sdm'` (`'a word set`) use the same predicate carrier as the
    `panSem` state's `memaddrs`/`sh_memaddrs`, which `pan_to_target_compile_semantics`
    passes to them directly: `a ∈ p_dom` is `p_dom a`, and `sdm' = sdm ∩ byte_aligned`
    is `sdm' = fun a => sdm a = true ∧ holByteAligned a = true`.  The existential
    domains `bitmaps_dm`/`sdm` are the Boolean domains of the tagged
    `installed_def`/`good_init_state_def`, as in `installed`.  All other clauses are those
    of `installed`, in HOL order. HOL's paired argument `(r1,r2)` is `regs`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def panInstalled {width : Nat} [NeZero width] {S Q : Type} (bytes : List (BitVec 8))
    (cbspace : Nat) (bitmaps : List (BitVec width)) (dataSp : Nat)
    (ffiNames : Option (List HolFfiName)) (regs : Nat × Nat) (mc : MachineConfig width S Q)
    (shmemExtra : List Compiler.Backend.LabToTarget.ShmemInfoNum) (ms : S)
    (pMem : BitVec width → WordLocW width) (pDom sdm' : BitVec width → Prop) : Prop :=
  ∃ (t : AsmState width) (m : BitVec width → WordLocW width) (bitmapPtr : BitVec width)
    (bitmapsDm sdm : BitVec width → Bool),
    let bytesInWord := Compiler.Backend.StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool :=
      fun w => decide (t.regs regs.1 ≤ w ∧ w < t.regs regs.2)
    (∀ a, pDom a → m a = pMem a) ∧
    goodInitState mc ms bytes cbspace t m (fun w => heapStackDm w || bitmapsDm w) sdm ∧
    sdm' = (fun a => sdm a = true ∧ holByteAligned a = true) ∧
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

/-- HOL `pan_installed_imp_installed` (`pan_to_targetProofScript.sml:328-334`). HOL's free
    variables are explicit, in order of appearance. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pan_installed_imp_installed {width : Nat} [NeZero width] {S Q : Type}
    (bytes : List (BitVec 8)) (cbspace : Nat) (bitmaps : List (BitVec width)) (dataSp : Nat)
    (ffiNames : Option (List HolFfiName)) (r1 r2 : Nat) (mc : MachineConfig width S Q)
    (shmemExtra : List Compiler.Backend.LabToTarget.ShmemInfoNum) (ms : S)
    (pMem : BitVec width → WordLocW width) (pDom sdm : BitVec width → Prop) :
    panInstalled bytes cbspace bitmaps dataSp ffiNames (r1, r2) mc shmemExtra ms pMem pDom sdm →
      installed bytes cbspace bitmaps dataSp ffiNames (r1, r2) mc shmemExtra ms := by
  rintro ⟨t, m, bitmapPtr, bitmapsDm, sdm0, -, hg, -, rest⟩
  exact ⟨t, m, bitmapPtr, bitmapsDm, sdm0, hg, rest⟩

end Flapjack.Pancake.Proofs.PanToTarget
