import Flapjack.Compiler.Backend.WordAlloc.ProductionSSACanonicalHelpers
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAMetadata

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc

/-- Complete native SSA preserves canonical cutset fields from its source
program, for arbitrary renaming state, counter and loop targets. Tail-call
handlers retain the source invariant; new key maps are built canonically.
This is Flapjack codec infrastructure, not a narrowed HOL correctness port. -/
theorem ssaProgramCanonical {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (names : Spt Nat) (next : Nat)
    (loopTargets : List (Spt Nat × Spt Unit × Spt Unit))
    (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (ssaCcTrans program names next loopTargets).1 := by
  induction program, names, next, loopTargets using ssaCcTrans.induct
  case case4 instruction map n tables output mapOut nextOut generated =>
    simpa only [ssaCcTrans, generated] using ssaInstructionCanonical instruction map n
  case case10 cmp r ri left right map n tables outL mapL nL hL outR mapR nR hR prio consL consR nf mf hFix ihL ihR =>
    have helpers := ssaFixCanonical (width := width) prio mapL mapR nR
    simp only [hFix] at helpers
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
  case case11 count sets map n tables allNames names first mapFirst nFirst hFirst cut second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveCanonical (width := width) map (n + 2) names
    have back := ssaRenameMoveCanonical (width := width) cut (nFirst + 2) names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical _ _
  case case18 ptr len dptr dlen sets map n tables allNames names first mapFirst nFirst hFirst cut
      result mapResult nResult hResult second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveCanonical (width := width) map (n + 2) names
    have back := ssaRenameMoveCanonical (width := width) mapResult nResult names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical _ _
  case case21 index ptr1 len1 ptr2 len2 sets map n tables allNames names first mapFirst nFirst hFirst cut second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveCanonical (width := width) map (n + 2) names
    have back := ssaRenameMoveCanonical (width := width) cut (nFirst + 2) names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical _ _
  case case22 target arguments handler map n tables =>
    rcases handler with _ | ⟨exception, body, l1, l2⟩ <;> simp_all [ssaCcTrans, WordAllocatorProgramSetsWf]
  case case23 ret sets body l1 l2 target arguments map n tables allNames names mapStack nStack cut
      returnMove mapRet nRet hRet namesRet mapNames nNames hNames out mapOut nOut hOut stackMove hStack ih =>
    have stack := ssaRenameMoveCanonical (width := width) map (n + 2) names
    have back := ssaRenameMoveCanonical (width := width) cut (nStack + 2) names
    simp only [hStack] at stack
    simp only [hRet] at back
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical _ _
  case case24 ret sets retBody l1 l2 target arguments map n tables allNames names mapStack nStack cut
      retMove mapRet nRet hRetMove retNames mapNames nNames hRetNames outRet mapRetOut nRetOut hRetOut
      regs movRet exception excBody excL1 excL2 stackMove exceptionReg mapExc nExc hExcRename
      outExc mapExcOut nExcOut hExcOut movExc prio consRet consExc nf mf hFix hStack ihRet ihExc =>
    have stack := ssaRenameMoveCanonical (width := width) map (n + 2) names
    have back := ssaRenameMoveCanonical (width := width) cut (nStack + 2) names
    have helpers := ssaFixCanonical (width := width) prio mapRetOut mapExcOut nExcOut
    simp only [hStack] at stack
    simp only [hRetMove] at back
    simp only [hFix] at helpers
    simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical _ _
  case case27 live body exits map n tables setup mapSetup nSetup hSetup bodyMap out mapOut nOut hOut ih =>
    have setupCanonical := ssaLoopSetupCanonical (width := width) live exits map n
    have backCanonical := ssaReconcileCanonical (width := width) mapOut mapSetup live
    simp only [hSetup] at setupCanonical
    dsimp only [bodyMap] at hOut ih
    simp only [hOut] at ih
    simp only [ssaCcTrans, hSetup, hOut]
    generalize hb : ssaReconcile (width := width) mapOut mapSetup live = moves at backCanonical ⊢
    cases moves <;> simp_all +zetaDelta [WordAllocatorProgramSetsWf]
    all_goals exact ssaKeyMapsCanonical (optionLookup mapSetup) (live, exits)
  case case29 n map next tables target live exits found =>
    have back := ssaReconcileCanonical (width := width) map target exits
    simp only [ssaCcTrans, found]
    generalize hb : ssaReconcile (width := width) map target exits = output at back ⊢
    cases output <;> simp_all [WordAllocatorProgramSetsWf]
  case case31 n map next tables target live exits found =>
    have back := ssaReconcileCanonical (width := width) map target live
    simp only [ssaCcTrans, found]
    generalize hb : ssaReconcile (width := width) map target live = output at back ⊢
    cases output <;> simp_all [WordAllocatorProgramSetsWf]
  all_goals simp_all +zetaDelta [ssaCcTrans, WordAllocatorProgramSetsWf]

/-- The complete native setup/body pass has canonical cutset fields on a
canonical source program. No constraint on the argument count is introduced.
This is representation infrastructure rather than a HOL semantic port. -/
theorem fullSsaProgramCanonical {width : Nat} [NeZero width]
    (count : Nat) (program : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (fullSsaCcTrans count program) := by
  simp [fullSsaCcTrans, WordAllocatorProgramSetsWf, ssaSetupCanonical,
    ssaProgramCanonical, valid]

end Flapjack.WordAlloc
