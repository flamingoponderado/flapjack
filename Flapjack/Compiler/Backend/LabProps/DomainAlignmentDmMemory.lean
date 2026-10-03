import Flapjack.Compiler.Backend.LabProps.DomainAlignmentWordMemory
import Flapjack.Compiler.Backend.LabSem.Inst

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget

/-- Flapjack-only guard consequence at the original good word dimensions. -/
private theorem alignedBase {width : Nat} [NeZero width] (hw : goodDimindex width)
    (x : BitVec width) : holByteAligned (riscvByteAlignHOL x) = true := by
  rw [riscvByteAlignHOL_eq hw]
  apply (holAligned_word_iff hw _).2
  rw [holByteAlign_toNat hw]
  exact Nat.mul_mod_left _ _

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load32_align_dm"
  (words_as_type_indexed_bitvec)]
theorem memLoad32AlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memLoad32 n a (alignDm s) = alignDm (memLoad32 n a s) := by
  intro hw
  simp only [memLoad32,addrAlignDM]
  simp only [alignDm,memLoad32Exact,alignedBase hw,Bool.and_true,updReg,assertState]
  all_goals repeat' first | rfl | split

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_load_byte_align_dm"
  (words_as_type_indexed_bitvec)]
theorem memLoadByteAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memLoadByte n a (alignDm s) = alignDm (memLoadByte n a s) := by
  intro hw
  simp only [memLoadByte,addrAlignDM]
  simp only [alignDm,memLoadByteAuxExact,alignedBase hw,Bool.and_true,updReg,assertState]
  all_goals repeat' first | rfl | split

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store32_align_dm"
  (words_as_type_indexed_bitvec)]
theorem memStore32AlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memStore32 n a (alignDm s) = alignDm (memStore32 n a s) := by
  intro hw
  simp only [memStore32,addrAlignDM]
  simp only [alignDm,memStore32Exact,alignedBase hw,Bool.and_true,assertState]
  all_goals repeat' first | rfl | split

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_store_byte_align_dm"
  (words_as_type_indexed_bitvec)]
theorem memStoreByteAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (n : Nat) (a : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memStoreByte n a (alignDm s) = alignDm (memStoreByte n a s) := by
  intro hw
  simp only [memStoreByte,addrAlignDM]
  simp only [alignDm,memStoreByteAuxExact,alignedBase hw,Bool.and_true,assertState]
  all_goals repeat' first | rfl | split

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "mem_op_align_dm"
  (words_as_type_indexed_bitvec)]
theorem memOpAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (m : HolMemop) (n : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → memOp m n a (alignDm s) = alignDm (memOp m n a s) := by
  intro hw
  cases m <;> simp only [memOp,memLoadAlignDM n a s hw,memStoreAlignDM n a s hw,
    memLoad32AlignDM n a s hw,memLoadByteAlignDM n a s hw,
    memStore32AlignDM n a s hw,memStoreByteAlignDM n a s hw,assertAlignDM]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_inst_align_dm"
  (words_as_type_indexed_bitvec)]
theorem asmInstAlignDM {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : HolInst width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → asmInst i (alignDm s) = alignDm (asmInst i s) := by
  intro hw
  cases i <;> simp only [asmInst,arithUpdAlignDM,fpUpdAlignDM,memOpAlignDM _ _ _ s hw,
    updRegAlignDM]

end Flapjack.Compiler.Backend.LabProps
