import Flapjack.Compiler.Backend.LabToTarget.Initialization.FullStateRel
import Flapjack.Compiler.Backend.LabToTarget.OracleTie
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

/-- Complete original semantic entry contract. The compiler configuration is
HOL's concrete config, while machine/state/projection and FFI host are
independent. The existential contains the whole native relation and whole
four-function oracle tie, with no restricted witness or added premise. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "init_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def initOk {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (bundle : MachineConfig width S Q × BitVec width) (s : State width Config F) (ms : S) : Prop :=
  ∃ code2 labs t1, stateRel (bundle.1,code2,labs,bundle.2) s t1 ms ∧ oracleTie bundle.1 ms s

/-- Original unconditional oracle tie for the actual initializer. Arbitrary
compiler configuration and all twelve source inputs remain independent. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "oracle_tie_make_init"
  (words_as_type_indexed_bitvec)]
theorem oracleTie_makeInit {width : Nat} [NeZero width] {C S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool) (ms : S)
    (code : LabProgHOL width)
    (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabProgHOL width) :
    oracleTie mc ms (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle) :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- Whole original three-field conjunction: FFI, initial PC and source code,
with every source input and arbitrary compiler configuration retained. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "make_init_simp"
  (words_as_type_indexed_bitvec)]
theorem makeInit_simp {width : Nat} [NeZero width] {C S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool) (ms : S)
    (code : LabProgHOL width)
    (comp : C → LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabProgHOL width) :
    let initial := makeInit mc ffi t m dm sdm ms code comp cbpos cbspace coracle
    initial.ffi = ffi ∧ initial.pc = 0 ∧ initial.code = code := ⟨rfl,rfl,rfl⟩

/-- Flapjack proof infrastructure deriving the actual semantic entry from
all original initializer guards and the checked unconditional oracle tie.
HOL has no separately named theorem for this composition; this does not
establish machine semantics or assume the desired initialized relation. -/
theorem makeInit_initOk {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) :
    goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧ mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames) ∧
    listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true ∧
    removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code = some (code2,labs) ∧
    goodInitState mc ms (progToBytes code2) cbspace t m dm sdm ∧
    getShmemInfo code2 0 [] [] = (newFfiNames,shmemInfo) ∧
    newShmemInfo = shmemInfo.map (fun rec => { rec with
      entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
      exitPc := (mc.target.getPc ms).toNat + rec.exitPc }) ∧
    mc.ffiNames.drop i = newFfiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index+i))
      (newShmemInfo.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧
    (∀ bn, bn < cbspace → BitVec.ofNat width bn + BitVec.ofNat width (progToBytes code2).length +
      mc.target.getPc ms ∉ mc.ffiEntryPcs.take i) →
    let initial := makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle
    initOk (mc,mc.target.getPc ms) initial ms := by
  intro h
  exact ⟨code2,labs,t,makeInit_stateRel mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h,
    oracleTie_makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms+BitVec.ofNat width (progToBytes code2).length) cbspace coracle⟩
end Flapjack.Compiler.Backend.LabToTarget
