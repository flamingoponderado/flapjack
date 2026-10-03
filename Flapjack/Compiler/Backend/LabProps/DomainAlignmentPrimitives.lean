import Flapjack.Compiler.Backend.LabProps.DomainAlignment
import Flapjack.Compiler.Backend.LabSem.Navigation
import Flapjack.Compiler.Backend.LabSem.Arithmetic

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
/-! Original unconditional primitive alignment laws. HOL read_reg is the
source overload lambda r s.s.regs r (labSemScript77), rendered directly.
All native program/register/address values and state carriers remain generic. -/

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_fetch_align_dm"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAlignDM {width : Nat} [NeZero width] {C F : Type}
     (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmFetch (alignDm s) = asmFetch s := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_align_dm"
  (words_as_type_indexed_bitvec)]
theorem readRegAlignDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignDm s).regs n = s.regs n := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_reg_align_dm"
  (words_as_type_indexed_bitvec)]
theorem updRegAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updReg x y (alignDm s) = alignDm (updReg x y s) := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_mem_align_dm"
  (words_as_type_indexed_bitvec)]
theorem updMemAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updMem x y (alignDm s) = alignDm (updMem x y s) := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_align_dm"
  (words_as_type_indexed_bitvec)]
theorem binopUpdAlignDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : BinOp) (z w : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    binopUpd x y z w (alignDm s) = alignDm (binopUpd x y z w s) := by
  cases y <;> rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_align_dm"
  (words_as_type_indexed_bitvec)]
theorem regImmAlignDM {width : Nat} [NeZero width] {C F : Type}
    (r : HolRegImm width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    regImm r (alignDm s) = regImm r s := by
  cases r <;> rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "assert_align_dm"
  (words_as_type_indexed_bitvec)]
theorem assertAlignDM {width : Nat} [NeZero width] {C F : Type}
    (b : Bool) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    assertState b (alignDm s) = alignDm (assertState b s) := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "asm_fetch_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem asmFetchAlignSDM {width : Nat} [NeZero width] {C F : Type}
     (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    asmFetch (alignSdm s) = asmFetch s := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "read_reg_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem readRegAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    (alignSdm s).regs n = s.regs n := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_reg_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem updRegAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updReg x y (alignSdm s) = alignSdm (updReg x y s) := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "upd_mem_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem updMemAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : BitVec width) (y : WordLocW width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    updMem x y (alignSdm s) = alignSdm (updMem x y s) := rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "binop_upd_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem binopUpdAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (x : Nat) (y : BinOp) (z w : BitVec width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    binopUpd x y z w (alignSdm s) = alignSdm (binopUpd x y z w s) := by
  cases y <;> rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "reg_imm_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem regImmAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (r : HolRegImm width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    regImm r (alignSdm s) = regImm r s := by
  cases r <;> rfl

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "assert_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem assertAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (b : Bool) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    assertState b (alignSdm s) = alignSdm (assertState b s) := rfl

end Flapjack.Compiler.Backend.LabProps
