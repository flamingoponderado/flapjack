import Flapjack.Compiler.Backend.Semantics.TargetSem.InterferenceContracts

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget

/-- Full original post-FFI state relation, with all source bounds, byte reads,
length/empty-name promises, entry state and alignment premises. Inherited total
holEl/holHd retains shared opaque holHdNil/holArb without bounds/fallback. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "ffi_interfer_ok_post_ffi_asm" (words_as_type_indexed_bitvec)]
theorem ffiInterferOkPostFfiAsm {width : Nat} [NeZero width] {S Q : Type}
    (pc : BitVec width) (mc : MachineConfig width S Q) (index i k : Nat)
    (t1 : AsmState width) (ms2 : S) (bytes bytes2 newBytes : List (BitVec 8))
    (h : ffiInterferOkHOL pc mc ∧ index < mc.ffiNames.length ∧
      mmioPcsMinIndex mc.ffiNames = some i ∧ index < i ∧
      mc.progAddresses = t1.memDomain ∧
      readFfiBytearraysHOL mc ms2 = (some bytes, some bytes2) ∧
      newBytes.length = bytes2.length ∧
      (holEl index mc.ffiNames = .extCall (.implode []) → newBytes = bytes2) ∧
      targetStateRel mc.target
        { t1 with pc := -BitVec.ofNat width ((3 + index) * ffiOffset) + pc } ms2 ∧
      holAligned mc.target.config.codeAlignment
        (t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n)) = true) :
    targetStateRel mc.target
      (postFfiAsmHOL mc t1 newBytes (mc.ffiInterfer k (index, newBytes, ms2)))
      (mc.ffiInterfer k (index, newBytes, ms2)) := by
  rcases h with ⟨hc, hl, hm, hi, hd, hb, hn, he, hr, ha⟩
  obtain ⟨hs, hp, hmem, hregs⟩ :=
    (hc ms2 k index newBytes t1 bytes bytes2 i ⟨hl, hm, hd⟩).1 hi
      ⟨hb, hn, he, hr, ha⟩
  refine ⟨hs, hp, hmem, ?_, ?_⟩
  · intro r hreg
    have havoid : r ∉ mc.target.config.avoidRegs := by simpa using hreg.2
    by_cases hsaved : r ∈ mc.calleeSavedRegs
    · simpa [postFfiAsmHOL, hsaved] using
        hregs r ⟨hsaved, hreg.1, havoid⟩
    · simp [postFfiAsmHOL, hsaved, Nat.not_le.mpr hreg.1, havoid]
  · intro r _
    rfl

/-- Full original post-cache state relation, with the original contract,
entry-state and link-register-alignment hypotheses only. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "ccache_interfer_ok_post_ccache_asm" (words_as_type_indexed_bitvec)]
theorem ccacheInterferOkPostCcacheAsm {width : Nat} [NeZero width] {S Q : Type}
    (pc : BitVec width) (mc : MachineConfig width S Q) (t1 : AsmState width)
    (ms2 : S) (k : Nat) (a1 a2 : BitVec width)
    (h : ccacheInterferOkHOL pc mc ∧
      targetStateRel mc.target
        { t1 with pc := -BitVec.ofNat width (2 * ffiOffset) + pc } ms2 ∧
      holAligned mc.target.config.codeAlignment
        (t1.regs (match mc.target.config.linkReg with | none => 0 | some n => n)) = true) :
    targetStateRel mc.target
      (postCcacheAsmHOL mc t1 (mc.ccacheInterfer k (a1, a2, ms2)))
      (mc.ccacheInterfer k (a1, a2, ms2)) := by
  rcases h with ⟨hc, hr, ha⟩
  obtain ⟨hs, hp, hmem, hregs⟩ := hc ms2 t1 k a1 a2 ⟨hr, ha⟩
  refine ⟨hs, hp, hmem, ?_, ?_⟩
  · intro r hreg
    have havoid : r ∉ mc.target.config.avoidRegs := by simpa using hreg.2
    by_cases hsaved : r ∈ mc.calleeSavedRegs
    · simpa [postCcacheAsmHOL, hsaved] using
        hregs r ⟨Or.inl hsaved, hreg.1, havoid⟩
    · by_cases hptr : r = mc.ptrReg
      · simpa [postCcacheAsmHOL, hptr] using
          hregs r ⟨Or.inr hptr, hreg.1, havoid⟩
      · simp [postCcacheAsmHOL, hsaved, hptr, Nat.not_le.mpr hreg.1, havoid]
  · intro r _
    rfl

end Flapjack.Compiler.Backend.Semantics.TargetProps
