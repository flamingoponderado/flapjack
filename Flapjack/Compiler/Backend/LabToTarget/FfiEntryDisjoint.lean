import Flapjack.Compiler.Backend.LabToTarget.BytesInMemoryFetch
import Flapjack.Compiler.Backend.LabToTarget.ShareMemDomain
import Flapjack.Compiler.Backend.Semantics.TargetProps.Interference
import Mathlib.Data.BitVec
import Mathlib.Tactic.Ring

/-! Original FFI-entry disjointness of the bytes of a fetched non-shared-memory
instruction (lab_to_targetProofScript.sml:6570-6627). All code-similarity,
encoding-validity, shared-memory domain, memory, position and PC hypotheses
are retained. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps

/-- The shared step of both original lemmas: a fetched target line that is not
a shared-memory access keeps its bytes away from the FFI entry PCs. -/
theorem ffiEntryPcsDisjoint_of_line {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width Config F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (bytes' : List (BitVec 8)) (y0 : LabLineHOL width)
    (hy0 : asmFetchAux s1.pc code2 = some y0)
    (hnot : ∀ op re a inst len, y0 ≠ .asm (.shareMem op re a) inst len)
    (henc : allEncOk mc.target.config labs ffis 0 code2)
    (hdom : shareMemDomainCodeRel mc p code2 (fun a => s1.sharedMemDomain a = true))
    (hpos : posVal (s1.pc + 1) 0 code2 = bytes'.length + posVal s1.pc 0 code2)
    (hpc : t1.pc = p + BitVec.ofNat width (posVal s1.pc 0 code2)) :
    ffiEntryPcsDisjoint mc t1 bytes'.length := by
  have hlen := asmFetchAux_posVal_lengthEq mc.target.config labs ffis bytes' s1.pc 0 code2 y0
    ⟨hy0, henc, hpos⟩
  rintro x ⟨hx, off, hoff, rfl⟩
  apply hdom.2.1 s1.pc y0 ⟨hy0, hnot⟩ _ hx
  refine ⟨off, ?_, by omega⟩
  rw [hpc]; ring

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_ffi_entry_pcs_disjoint_Asm" (words_as_type_indexed_bitvec)]
theorem imp_ffiEntryPcsDisjoint_asm {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (mc : MachineConfig width S Q)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (instr : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (bytes : List (BitVec 8))
    (len : Nat) (p : BitVec width) (bytes' : List (BitVec 8)) (t1 : AsmState width) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      asmFetchAux s1.pc s1.code = some (.asm instr bytes len) ∧
      (∀ op re a, instr ≠ .shareMem op re a) ∧
      shareMemDomainCodeRel mc p code2 (fun a => s1.sharedMemDomain a = true) ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = bytes'.length + posVal s1.pc 0 code2 ∧
      t1.pc = p + BitVec.ofNat width (posVal s1.pc 0 code2) →
    ffiEntryPcsDisjoint mc t1 bytes'.length := by
  rintro ⟨hsim, henc, hf, hinstr, hdom, -, hpos, hpc⟩
  have hrel := codeSimilar_asmFetchAux s1.pc s1.code code2 hsim
  rw [hf] at hrel
  cases hy : asmFetchAux s1.pc code2 with
  | none => rw [hy] at hrel; cases hrel
  | some y0 =>
    rw [hy] at hrel
    cases hrel with
    | some hs =>
    refine ffiEntryPcsDisjoint_of_line mc labs ffis s1 code2 p t1 bytes' y0 hy ?_ henc hdom
      hpos hpc
    intro op re a inst l heq
    subst heq
    simp only [lineSimilar] at hs
    exact hinstr op re a hs

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_ffi_entry_pcs_disjoint_LabAsm" (words_as_type_indexed_bitvec)]
theorem imp_ffiEntryPcsDisjoint_labAsm {width : Nat} [NeZero width] {S Q F : Type}
    (s1 : LabSem.State width Config F) (mc : MachineConfig width S Q)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (instr : AsmWithLab HolCmp (HolRegImm width) MlString) (pos : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat) (p : BitVec width) (bytes' : List (BitVec 8))
    (t1 : AsmState width) :
    codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      asmFetchAux s1.pc s1.code = some (.labAsm instr pos bytes len) ∧
      shareMemDomainCodeRel mc p code2 (fun a => s1.sharedMemDomain a = true) ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      posVal (s1.pc + 1) 0 code2 = bytes'.length + posVal s1.pc 0 code2 ∧
      t1.pc = p + BitVec.ofNat width (posVal s1.pc 0 code2) →
    ffiEntryPcsDisjoint mc t1 bytes'.length := by
  rintro ⟨hsim, henc, hf, hdom, -, hpos, hpc⟩
  have hrel := codeSimilar_asmFetchAux s1.pc s1.code code2 hsim
  rw [hf] at hrel
  cases hy : asmFetchAux s1.pc code2 with
  | none => rw [hy] at hrel; cases hrel
  | some y0 =>
    rw [hy] at hrel
    cases hrel with
    | some hs =>
    refine ffiEntryPcsDisjoint_of_line mc labs ffis s1 code2 p t1 bytes' y0 hy ?_ henc hdom
      hpos hpc
    intro op re a inst l heq
    subst heq
    simp [lineSimilar] at hs

end Flapjack.Compiler.Backend.LabToTarget
