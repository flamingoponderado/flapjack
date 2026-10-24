import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Primitives
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Instructions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAConventions.Calls

namespace Flapjack.WordAlloc
open Flapjack Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the generalized native structural induction motive;
no separately named HOL original. -/
private def programPre {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (ssa : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    isAllocVar next ∧ ssaMapOK next ssa →
      preAllocConventionsHOL (ssaCcTrans prog ssa next tables).1 = true

/-- Complete original SSA pre-convention theorem, assembled by native mutual
structural induction including both nested return and exception handlers.
Only the original input allocation class and SSA map invariant are premises. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "ssa_cc_trans_pre_alloc_conventions" (words_as_type_indexed_bitvec)]
theorem ssaCcTrans_preAllocConventions {width : Nat} [NeZero width]
    (prog : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : isAllocVar next ∧ ssaMapOK next ssa) :
    preAllocConventionsHOL (ssaCcTrans prog ssa next tables).1 = true := by
  have all : ∀ p : WordLangProgHOL (BitVec width), programPre p := by
    intro p
    set_option tactic.fun_induction.unfolding false in
    fun_induction everyVarHOL (fun _ => true) p with
    | case13 returns dest args handler ih =>
        rcases returns with _ | ⟨values, cutsets, body, l1, l2⟩
        · exact ssaCcTrans_preAllocTailCall dest args handler
        · exact ssaCcTrans_preAllocReturningCall values cutsets body l1 l2 dest args handler ih.1 ih.2
    | case1 => exact ssaCcTrans_preAllocSkip
    | case2 priority moves => exact ssaCcTrans_preAllocMove priority moves
    | case3 instruction => exact ssaCcTrans_preAllocInst instruction
    | case4 destination expression => exact ssaCcTrans_preAllocAssign destination expression
    | case5 destination store => exact ssaCcTrans_preAllocGet destination store
    | case6 expression source => exact ssaCcTrans_preAllocStore expression source
    | case7 destination source => exact ssaCcTrans_preAllocLocValue destination source
    | case8 a b c d names => exact ssaCcTrans_preAllocInstall a b c d names
    | case9 a b => exact ssaCcTrans_preAllocCodeBufferWrite a b
    | case10 a b => exact ssaCcTrans_preAllocDataBufferWrite a b
    | case11 function a b c d names => exact ssaCcTrans_preAllocFFI function a b c d names
    | case16 destination names => exact ssaCcTrans_preAllocAlloc destination names
    | case17 a b c d constants => exact ssaCcTrans_preAllocStoreConsts a b c d constants
    | case18 value => exact ssaCcTrans_preAllocRaise value
    | case19 value values => exact ssaCcTrans_preAllocReturn value values
    | case20 operator left right => exact ssaCcTrans_preAllocOpCurrHeap operator left right
    | case21 => exact ssaCcTrans_preAllocTick
    | case22 store expression => exact ssaCcTrans_preAllocSet store expression
    | case23 operator destination expression => exact ssaCcTrans_preAllocShareInst operator destination expression
    | case12 body ih => exact ssaCcTrans_preAllocMustTerminate body ih
    | case14 first second ihFirst ihSecond => exact ssaCcTrans_preAllocSeq first second ihFirst ihSecond
    | case15 cmp register right first second ihFirst ihSecond =>
        exact ssaCcTrans_preAllocIf cmp register right first second ihFirst ihSecond
    | case24 liveIn body liveOut ih => exact ssaCcTrans_preAllocLoop liveIn liveOut body ih
    | case25 p =>
        cases p <;> grind only [programPre, ssaCcTrans_preAllocBreak, ssaCcTrans_preAllocContinue]
  exact all prog ssa next tables h


end Flapjack.WordAlloc
