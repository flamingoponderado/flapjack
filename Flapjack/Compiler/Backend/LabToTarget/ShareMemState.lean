import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.MappedMemory
import Flapjack.Compiler.Encoders.AsmProps.Target
import Flapjack.EvaluateProps
import Flapjack.Byte
import Flapjack.Byte.WordOfBytes
import Flapjack.Misc.ListEl
import Mathlib.Logic.Relation

/-!
# lab_to_targetProof: `share_mem_state_rel`

Port of `share_mem_state_rel_def` (`lab_to_targetProofScript.sml:720-774`), the requirement on
the machine configuration's shared-memory FFI interference and on the halt/cache PCs. HOL `R^*`
is `Relation.ReflTransGen R`, `EL` is the total `holEl`, `ALOOKUP` is `List.lookup`, HOL sets
are predicates, `T` is `True`, and `FFI_return` is `HolFfiResult.ret`. As in the HOL kernel
typing, the labSem state's word width (`α`) is independent of the machine word width (`β`) and
appears only in the `dimindex (:α) DIV 8` alignment test. The outer `t1 : ε` and `ms1 : ζ` are
vacuous in HOL (`t1` is shadowed by the inner binder, `ms1` is unused) and are retained.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.HolByte

private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Exact HOL `share_mem_state_rel_def` (`lab_to_targetProofScript.sml:720-774`), with the
original binders `ms2 k index new_bytes t1 nb ad offs re pc' ad' st new_st i` and `index i`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def shareMemStateRel {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width]
    {γ δ : Type} {F : Type} {ε ζ : Type}
    (mcConf : MachineConfig width γ δ) (s1 : Flapjack.Compiler.Backend.LabSem.State labWidth Config F)
    (_t1 : ε) (_ms1 : ζ) : Prop :=
  (∀ (ms2 : γ) (k index : Nat) (newBytes : List (BitVec 8)) (t1 : AsmState width) (nb : BitVec 8)
      (ad : Nat) (offs : BitVec width) (re : Nat) (pc' ad' : BitVec width) (st newSt : HolFfiState F)
      (i : Nat),
      mmioPcsMinIndex mcConf.ffiNames = some i ∧ i ≤ index ∧ index < mcConf.ffiNames.length ∧
        Relation.ReflTransGen callFFIRelHOL s1.ffi st ∧
        mcConf.mmioInfo.lookup index = some (nb, .addr ad offs, re, pc') ∧
        mcConf.progAddresses = t1.memDomain ∧
        ad' = mcConf.target.getReg ms2 ad + offs ∧
        targetStateRel mcConf.target { t1 with pc := holEl index mcConf.ffiEntryPcs } ms2 →
      ∃ op : HolShmemOp, holEl index mcConf.ffiNames = HolFfiName.sharedMem op ∧
        match op with
        | .mappedRead =>
            (if nb = 0 then ad'.toNat % (labWidth / 8) = 0 else True) ∧
              mcConf.sharedAddresses ad' ∧
              isValidMappedRead (mcConf.target.getPc ms2) nb (.addr ad offs) re pc'
                mcConf.target ms2 mcConf.progAddresses ∧
              callFFIHOL st (.sharedMem .mappedRead) [nb] (wordToBytes ad' false) =
                .ret newSt newBytes →
            targetStateRel mcConf.target
              { t1 with
                  pc := pc'
                  regs := fun n => if n = re then wordOfBytes false 0 newBytes else t1.regs n }
              (mcConf.ffiInterfer k (index, newBytes, ms2))
        | .mappedWrite =>
            (if nb = 0 then ad'.toNat % (labWidth / 8) = 0 else True) ∧
              mcConf.sharedAddresses ad' ∧
              isValidMappedWrite (mcConf.target.getPc ms2) nb (.addr ad offs) re pc'
                mcConf.target ms2 mcConf.progAddresses ∧
              callFFIHOL st (.sharedMem .mappedWrite) [nb]
                  ((let w := mcConf.target.getReg ms2 re
                    if nb = 0 then wordToBytes w false else wordToBytesAux nb.toNat w false) ++
                    wordToBytes ad' false) =
                .ret newSt newBytes →
            targetStateRel mcConf.target { t1 with pc := pc' }
              (mcConf.ffiInterfer k (index, newBytes, ms2))) ∧
  (∀ index i : Nat,
      mmioPcsMinIndex mcConf.ffiNames = some i ∧ index < mcConf.ffiNames.length ∧ i ≤ index →
      mcConf.haltPc ≠ holEl index mcConf.ffiEntryPcs ∧ mcConf.ccachePc ≠ holEl index mcConf.ffiEntryPcs)

/-- With no FFI names both conjuncts are vacuous (Flapjack infrastructure; HOL proves the same
instance in `lab_to_target_share_mem_state_probe`). -/
theorem shareMemStateRel_nil {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width] {γ δ F ε ζ : Type}
    (mcConf : MachineConfig width γ δ) (s1 : Flapjack.Compiler.Backend.LabSem.State labWidth Config F)
    (t1 : ε) (ms1 : ζ) (h : mcConf.ffiNames = []) : shareMemStateRel mcConf s1 t1 ms1 := by
  refine ⟨fun _ _ index _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, hlt, _⟩ => ?_,
    fun index _ ⟨_, hlt, _⟩ => ?_⟩
  · rw [h] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  · rw [h] at hlt; exact absurd hlt (Nat.not_lt_zero _)

/-- One shared-memory FFI name whose entry PC is the halt PC violates the relation (Flapjack
infrastructure; HOL proves the same counterexample in the probe). -/
theorem not_shareMemStateRel_halt {labWidth : Nat} [NeZero labWidth] {width : Nat} [NeZero width]
    {γ δ F ε ζ : Type} (mcConf : MachineConfig width γ δ)
    (s1 : Flapjack.Compiler.Backend.LabSem.State labWidth Config F) (t1 : ε) (ms1 : ζ)
    (w : BitVec width) (hn : mcConf.ffiNames = [HolFfiName.sharedMem .mappedRead])
    (he : mcConf.ffiEntryPcs = [w]) (hh : mcConf.haltPc = w) :
    ¬ shareMemStateRel mcConf s1 t1 ms1 := by
  rintro ⟨_, h2⟩
  have hm : mmioPcsMinIndex mcConf.ffiNames = some 0 := by
    rw [hn]
    apply mmioPcsMinIndex_eq_some
    refine ⟨by simp, fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ hj => ?_⟩
    have : j = 0 := by simpa using hj
    subst this
    exact ⟨.mappedRead, rfl⟩
  have := (h2 0 0 ⟨hm, by rw [hn]; decide, Nat.le_refl 0⟩).1
  rw [he, hh] at this
  exact this rfl

end Flapjack.Compiler.Backend.LabToTarget
