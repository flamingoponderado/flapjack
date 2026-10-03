import Flapjack.Compiler.Backend.LabProps.DomainAlignmentPrimitives
import Flapjack.Compiler.Backend.LabSem.FpUpdates
import Flapjack.Compiler.Backend.LabSem.Memory

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm
/-! Full original arithmetic, FP and address projection laws. Native FP
operations retain their inherited reals_as_rational_cuts assurance (SOUNDNESS8).
No transition success or narrower dimension premise is added. -/

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_align_dm"
  (words_as_type_indexed_bitvec)]
theorem arithUpdAlignDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolArith width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    arithUpd op (alignDm s) = alignDm (arithUpd op s) := by
  cases op <;> simp only [arithUpd, regImm, binopUpd, updReg, assertState, alignDm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_align_dm"
  (words_as_type_indexed_bitvec)]
theorem fpUpdAlignDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolFp) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    fpUpd op (alignDm s) = alignDm (fpUpd op s) := by
  cases op <;> simp only [fpUpd, readFpReg, updFpReg, updReg, assertState, alignDm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_align_dm"
  (words_as_type_indexed_bitvec)]
theorem addrAlignDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    addrValue op (alignDm s) = addrValue op s := by
  cases op <;> simp only [addrValue, alignDm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "arith_upd_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem arithUpdAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolArith width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    arithUpd op (alignSdm s) = alignSdm (arithUpd op s) := by
  cases op <;> simp only [arithUpd, regImm, binopUpd, updReg, assertState, alignSdm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "fp_upd_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem fpUpdAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolFp) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    fpUpd op (alignSdm s) = alignSdm (fpUpd op s) := by
  cases op <;> simp only [fpUpd, readFpReg, updFpReg, updReg, assertState, alignSdm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "addr_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem addrAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (op : HolAddr width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    addrValue op (alignSdm s) = addrValue op s := by
  cases op <;> simp only [addrValue, alignSdm]
  all_goals repeat' first
    | rfl
    | split
    | simp_all

end Flapjack.Compiler.Backend.LabProps
