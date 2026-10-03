import Flapjack.Compiler.Backend.LabProps.DomainAlignmentOperations
import Flapjack.Compiler.Backend.LabSem.Inst

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
/-! Full unconditional SDM alignment laws for the six actual native memory
operations and both instruction dispatchers. The ordinary memory domain is
unchanged; no word-dimension guard or transition-success premise is added. -/

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memLoadAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memLoad n a (alignSdm s) = alignSdm (memLoad n a s) := by
  simp only [memLoad,addrAlignSDM]
  simp only [alignSdm,updReg,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load32_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memLoad32AlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memLoad32 n a (alignSdm s) = alignSdm (memLoad32 n a s) := by
  simp only [memLoad32,addrAlignSDM]
  simp only [alignSdm,updReg,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_byte_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memLoadByteAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memLoadByte n a (alignSdm s) = alignSdm (memLoadByte n a s) := by
  simp only [memLoadByte,addrAlignSDM]
  simp only [alignSdm,updReg,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memStoreAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memStore n a (alignSdm s) = alignSdm (memStore n a s) := by
  simp only [memStore,addrAlignSDM]
  simp only [alignSdm,updMem,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store32_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memStore32AlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memStore32 n a (alignSdm s) = alignSdm (memStore32 n a s) := by
  simp only [memStore32,addrAlignSDM]
  simp only [alignSdm,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_byte_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memStoreByteAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memStoreByte n a (alignSdm s) = alignSdm (memStoreByte n a s) := by
  simp only [memStoreByte,addrAlignSDM]
  simp only [alignSdm,assertState]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_op_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem memOpAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (m : HolMemop) (n : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    memOp m n a (alignSdm s) = alignSdm (memOp m n a s) := by
  cases m <;> simp only [memOp,memLoadAlignSDM,memLoad32AlignSDM,memLoadByteAlignSDM,
    memStoreAlignSDM,memStore32AlignSDM,memStoreByteAlignSDM,assertAlignSDM]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem asmInstAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmInst i (alignSdm s) = alignSdm (asmInst i s) := by
  cases i <;> simp only [asmInst,arithUpdAlignSDM,fpUpdAlignSDM,memOpAlignSDM,updRegAlignSDM]

end Flapjack.Compiler.Backend.LabProps
