import Flapjack.Compiler.Backend.LabToTarget.PositionValues
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.Semantics.TargetSem.MmioIndex
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Misc.FindIndex
import Flapjack.Misc.ListEl
import Flapjack.Misc.Alignment

/-!
# lab_to_targetProof: `share_mem_domain_code_rel`

Port of `share_mem_domain_code_rel_def` (`lab_to_targetProofScript.sml:688-717`), the relation
between the shared-memory instructions of the target code, the machine configuration's
`ffi_entry_pcs`/`ffi_names`/`mmio_info`, and the shared memory domain. HOL `EL` is the total
`holEl`, `ALOOKUP` is `List.lookup`, `find_index` is the tagged `findIndex`, `byte_align` is the
exact `holByteAlign` over the specified `LOG2`, HOL sets are predicates, `x ∈ set l` is list
membership, and `DISJOINT s t` is `∀ x, s x → ¬ t x` with the set comprehension
`{p + n2w a + n2w (pos_val pc 0 code2) | a < LENGTH (line_bytes line)}` as its existential.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Exact HOL `share_mem_domain_code_rel_def` (`lab_to_targetProofScript.sml:688-717`): the
four conjuncts with the original binders `pc op re a inst len i` and `pc line`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
noncomputable def shareMemDomainCodeRel {width : Nat} [NeZero width] {β γ : Type}
    (mcConf : MachineConfig width β γ) (p : BitVec width) (code2 : List (Section (LabLineHOL width)))
    (s1SharedMemDomain : BitVec width → Prop) : Prop :=
  (∀ (pc : Nat) (op : HolMemop) (re : Nat) (a : HolAddr width) (inst : List (BitVec 8))
      (len i : Nat),
      asmFetchAux pc code2 = some (.asm (.shareMem op re a) inst len) ∧
        mmioPcsMinIndex mcConf.ffiNames = some i →
      ∃ index, i ≤ index ∧
        Flapjack.Misc.findIndex (p + BitVec.ofNat width (posVal pc 0 code2)) mcConf.ffiEntryPcs 0 =
          some index ∧
        (let (name, nb) := getMemopInfo op
         holEl index mcConf.ffiNames = HolFfiName.sharedMem name ∧
         mcConf.mmioInfo.lookup index =
           some (nb, a, re, p + BitVec.ofNat width (posVal pc 0 code2 + len)))) ∧
  (∀ (pc : Nat) (line : LabLineHOL width),
      asmFetchAux pc code2 = some line ∧
        (∀ (op : HolMemop) (re : Nat) (a : HolAddr width) (inst : List (BitVec 8)) (len : Nat),
          line ≠ .asm (.shareMem op re a) inst len) →
      ∀ x, x ∈ mcConf.ffiEntryPcs →
        ¬ ∃ a, x = p + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2) ∧
          a < (lineBytes line).length) ∧
  (∀ a : BitVec width, s1SharedMemDomain (holByteAlign a) → s1SharedMemDomain a) ∧
  mcConf.sharedAddresses = s1SharedMemDomain

/-- On code with no lines the relation is the `byte_align` closure of the domain and the
`shared_addresses` equation (Flapjack infrastructure; HOL proves the same reduction in the
`lab_to_target_share_mem_domain_probe`). -/
theorem shareMemDomainCodeRel_nil {width : Nat} [NeZero width] {β γ : Type}
    (mcConf : MachineConfig width β γ) (p : BitVec width) (d : BitVec width → Prop) :
    shareMemDomainCodeRel mcConf p [] d ↔
      (∀ a : BitVec width, d (holByteAlign a) → d a) ∧ mcConf.sharedAddresses = d := by
  constructor
  · rintro ⟨_, _, h3, h4⟩
    exact ⟨h3, h4⟩
  · rintro ⟨h3, h4⟩
    refine ⟨fun pc _ _ _ _ _ _ ⟨h, _⟩ => ?_, fun pc _ ⟨h, _⟩ => ?_, h3, h4⟩
    · simp [asmFetchAux] at h
    · simp [asmFetchAux] at h

end Flapjack.Compiler.Backend.LabToTarget
