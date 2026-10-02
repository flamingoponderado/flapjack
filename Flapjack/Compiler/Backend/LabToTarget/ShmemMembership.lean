import Flapjack.Compiler.Backend.LabToTarget.ShmemExtraction
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Full original paired-extraction membership. Successful source fetch and
memory-operation pair equality are retained, with the exact original exit-PC
position expression and no assumption about the desired membership. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "MEM_get_shmem_info" (words_as_type_indexed_bitvec)]
theorem getShmemInfo_mem {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (op : HolMemop) (reg : Nat) (addr : HolAddr width)
    (bytes : List (BitVec 8)) (len : Nat) (name : HolShmemOp) (nbytes : BitVec 8) (p : Nat) :
    allEncOk c labs ffis validPos code ∧
    asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len) ∧
    getMemopInfo op = (name,nbytes) →
    (.sharedMem name,
      {entryPc:=posVal pc p code,nbytes:=nbytes,
       addrReg:=match addr with | .addr base _ => base,
       addrOff:=match addr with | .addr _ off => off.toNat,
       reg:=reg,exitPc:=posVal pc (p+bytes.length) code}) ∈
      List.zip (getShmemInfo code p [] []).1 (getShmemInfo code p [] []).2 := by
  rintro ⟨he,hfetch,hmem⟩
  rw [getShmemInfo_characterization code p [] [] validPos c labs ffis he]
  simp only [List.nil_append]
  rw [List.zip_unzip]
  simp only [List.map_map,Function.comp_def]
  apply List.mem_flatten.mpr
  refine ⟨lineToInfo code p (pc,asmFetchAux pc code), ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨pc,List.mem_range.mpr (asmFetchAux_some_ltNumPcs pc code _ hfetch),rfl⟩
  · have hpos := posVal_accSum pc (p+bytes.length) code bytes.length p (by omega)
    cases addr
    simp [lineToInfo,hfetch,hmem,hpos,Nat.add_comm]

/-- Full original paired output-length law: retains the source's sole complete
encoding-validity guard and independent query/validity starts. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "get_shmem_info_EMPTY_LENGTH_EQ" (words_as_type_indexed_bitvec)]
theorem getShmemInfo_emptyLengthEq {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (p : Nat) :
    allEncOk c labs ffis validPos code →
    (getShmemInfo code p [] []).1.length = (getShmemInfo code p [] []).2.length := by
  intro he
  rw [getShmemInfo_characterization code p [] [] validPos c labs ffis he]
  simp only [List.unzip_eq_map,List.nil_append,List.length_map]
end Flapjack.Compiler.Backend.LabToTarget
