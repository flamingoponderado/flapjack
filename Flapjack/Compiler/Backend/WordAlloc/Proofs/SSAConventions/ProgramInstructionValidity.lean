import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.PrimitiveInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.InstInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ShareInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.AllocationInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.ControlInstructionValidity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.CallInstructionValidity

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- Flapjack factoring of the generalized native structural induction motive;
no separately named HOL original. -/
private def programValid {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    everyVarHOL (fun x => decide (x < next)) prog = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config prog = true →
      fullInstOkLessExact config (ssaCcTrans prog ssa next tables).1 = true

/-- Complete original SSA instruction-validity theorem, assembled by native mutual
structural induction including both nested return and exception handlers.
Retains the original source variable bound, allocation class, SSA map invariant
and source instruction-validity hypotheses; no remaining induction premise. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_full_inst_ok_less" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_fullInstOkLess {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : everyVarHOL (fun x => decide (x < next)) prog = true ∧
      isAllocVar next ∧ ssaMapOK next ssa ∧ fullInstOkLessExact config prog = true) :
    fullInstOkLessExact config (ssaCcTrans prog ssa next tables).1 = true := by
  have all : ∀ p : WordLangProgHOL (BitVec width), programValid config p := by
    intro p
    set_option tactic.fun_induction.unfolding false in
    fun_induction everyVarHOL (fun _ => true) p with
    | case13 returns dest args handler ih =>
        rcases returns with _ | ⟨values, cutsets, body, l1, l2⟩
        · exact ssaCcTrans_fullInstTailCall config dest args handler
        · exact ssaCcTrans_fullInstReturningCall config values cutsets body l1 l2 dest args handler ih.1 ih.2
    | case1 => exact ssaCcTrans_fullInstSkip config
    | case2 => exact ssaCcTrans_fullInstMove config _ _
    | case3 => exact ssaCcTrans_fullInstInst config _
    | case4 => exact ssaCcTrans_fullInstAssign config _ _
    | case5 => exact ssaCcTrans_fullInstGet config _ _
    | case6 => exact ssaCcTrans_fullInstStore config _ _
    | case7 => exact ssaCcTrans_fullInstLocValue config _ _
    | case8 => exact ssaCcTrans_fullInstInstall config _ _ _ _ _
    | case9 => exact ssaCcTrans_fullInstCodeBufferWrite config _ _
    | case10 => exact ssaCcTrans_fullInstDataBufferWrite config _ _
    | case11 => exact ssaCcTrans_fullInstFFI config _ _ _ _ _ _
    | case16 => exact ssaCcTrans_fullInstAlloc config _ _
    | case17 => exact ssaCcTrans_fullInstStoreConsts config _ _ _ _ _
    | case18 => exact ssaCcTrans_fullInstRaise config _
    | case19 => exact ssaCcTrans_fullInstReturn config _ _
    | case20 => exact ssaCcTrans_fullInstOpCurrHeap config _ _ _
    | case21 => exact ssaCcTrans_fullInstTick config
    | case22 => exact ssaCcTrans_fullInstSet config _ _
    | case23 => exact ssaCcTrans_fullInstShareInst config _ _ _
    | case12 body ih => exact ssaCcTrans_fullInstMustTerminate config body ih
    | case14 first second ihFirst ihSecond => exact ssaCcTrans_fullInstSeq config first second ihFirst ihSecond
    | case15 cmp register right first second ihFirst ihSecond =>
        exact ssaCcTrans_fullInstIf config cmp register right first second ihFirst ihSecond
    | case24 liveIn body liveOut ih => exact ssaCcTrans_fullInstLoop config liveIn liveOut body ih
    | case25 p =>
        cases p <;> grind only [programValid, ssaCcTrans_fullInstBreak, ssaCcTrans_fullInstContinue]
  exact all prog ssa next tables h


end Flapjack.WordAlloc
