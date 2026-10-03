import Flapjack.Compiler.Backend.LabSem.State
import Flapjack.Compiler.Encoders.Asm

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-! Literal domain projections used by original LabProps alignment proofs.
HOL byte_aligned is aligned(LOG2(dimindex DIV 8)); asmAligned implements
aligned by equality after clearing those low bits, equivalently divisibility
by 2^alignment. Bool conjunction is the native HOL set intersection.
No word-width guard beyond the reviewed positive-width carrier is added.
-/

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_def"
  (words_as_type_indexed_bitvec)]
def alignDm {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) : Flapjack.Compiler.Backend.LabSem.State width C F :=
  {s with memDomain := fun address => s.memDomain address && asmAligned (Nat.log2 (width / 8)) address}

/-- The complete original eighteen unchanged fields, in source order. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_const"
  (words_as_type_indexed_bitvec)]
theorem alignDmConst {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignDm s).clock = s.clock ∧
    (alignDm s).pc = s.pc ∧
    (alignDm s).code = s.code ∧
    (alignDm s).memory = s.memory ∧
    (alignDm s).sharedMemDomain = s.sharedMemDomain ∧
    (alignDm s).be = s.be ∧
    (alignDm s).lenReg = s.lenReg ∧
    (alignDm s).linkReg = s.linkReg ∧
    (alignDm s).ptrReg = s.ptrReg ∧
    (alignDm s).ptr2Reg = s.ptr2Reg ∧
    (alignDm s).len2Reg = s.len2Reg ∧
    (alignDm s).ioRegs = s.ioRegs ∧
    (alignDm s).ioFpRegs = s.ioFpRegs ∧
    (alignDm s).codeBuffer = s.codeBuffer ∧
    (alignDm s).compile = s.compile ∧
    (alignDm s).compileOracle = s.compileOracle ∧
    (alignDm s).ffi = s.ffi ∧
    (alignDm s).failed = s.failed := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_dm_with_clock"
  (words_as_type_indexed_bitvec)]
theorem alignDmWithClock {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) (k : Nat) :
    alignDm {s with clock := k} = {alignDm s with clock := k} := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_def"
  (words_as_type_indexed_bitvec)]
def alignSdm {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) : Flapjack.Compiler.Backend.LabSem.State width C F :=
  {s with sharedMemDomain := fun address => s.sharedMemDomain address && asmAligned (Nat.log2 (width / 8)) address}

/-- The complete original eighteen unchanged fields, in source order. -/
@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_const"
  (words_as_type_indexed_bitvec)]
theorem alignSdmConst {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignSdm s).clock = s.clock ∧
    (alignSdm s).pc = s.pc ∧
    (alignSdm s).code = s.code ∧
    (alignSdm s).memory = s.memory ∧
    (alignSdm s).memDomain = s.memDomain ∧
    (alignSdm s).be = s.be ∧
    (alignSdm s).lenReg = s.lenReg ∧
    (alignSdm s).linkReg = s.linkReg ∧
    (alignSdm s).ptrReg = s.ptrReg ∧
    (alignSdm s).ptr2Reg = s.ptr2Reg ∧
    (alignSdm s).len2Reg = s.len2Reg ∧
    (alignSdm s).ioRegs = s.ioRegs ∧
    (alignSdm s).ioFpRegs = s.ioFpRegs ∧
    (alignSdm s).codeBuffer = s.codeBuffer ∧
    (alignSdm s).compile = s.compile ∧
    (alignSdm s).compileOracle = s.compileOracle ∧
    (alignSdm s).ffi = s.ffi ∧
    (alignSdm s).failed = s.failed := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "align_sdm_with_clock"
  (words_as_type_indexed_bitvec)]
theorem alignSdmWithClock {width : Nat} [NeZero width] {C F : Type} (s : Flapjack.Compiler.Backend.LabSem.State width C F) (k : Nat) :
    alignSdm {s with clock := k} = {alignSdm s with clock := k} := rfl

end Flapjack.Compiler.Backend.LabProps
