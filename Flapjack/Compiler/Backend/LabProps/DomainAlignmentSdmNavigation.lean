import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.Semantics.WordSem

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "dec_clock_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem decClockAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    decClock (alignSdm s) = alignSdm (decClock s) := by rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "inc_pc_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem incPcAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    incPc (alignSdm s) = alignSdm (incPc s) := by rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_pc_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem updPcAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (p : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updPc p (alignSdm s) = alignSdm (updPc p s) := by rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_pc_value_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem getPcValueAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Flapjack.Compiler.Backend.LabLang.Lab) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getPcValue x (alignSdm s) = getPcValue x s := by rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "get_ret_Loc_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem getRetLocAlignSDM {width : Nat} [NeZero width] {C F : Type}
    {resultWidth : Nat} [NeZero resultWidth]
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    getRetLoc (resultWidth := resultWidth) (alignSdm s) = getRetLoc (resultWidth := resultWidth) s := by rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_bytearray_mem_load_byte_aux_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem readBytearrayMemLoadByteAuxAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    ∀ (length : Nat) (address : BitVec width), readBytearrayWordHOL address length (memLoadByteAuxExact s.memory (alignSdm s).memDomain s.be) =
      readBytearrayWordHOL address length (memLoadByteAuxExact s.memory s.memDomain s.be) := by intros; rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "write_bytearray_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem writeBytearrayAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    ∀ (bytes : List (BitVec 8)) (address : BitVec width), writeBytearrayExact address bytes s.memory (alignSdm s).memDomain s.be =
      writeBytearrayExact address bytes s.memory s.memDomain s.be := by intros; rfl

end Flapjack.Compiler.Backend.LabProps
