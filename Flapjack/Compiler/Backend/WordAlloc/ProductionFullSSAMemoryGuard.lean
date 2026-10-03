import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAMemoryGuard
import Flapjack.Compiler.Backend.WordAlloc.FullSSA

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc

/-- Complete native SSA preserves the additional production memory guard,
without assuming that guard succeeds. This is Flapjack-only domain
infrastructure, not a narrowed HOL SSA or allocation correctness port. -/
theorem ssaProgramMemoryGuard {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (names : Spt Nat) (next : Nat)
    (loopTargets : List (Spt Nat × Spt Unit × Spt Unit)) :
    nativeMemorySupported (ssaCcTrans program names next loopTargets).1 =
      nativeMemorySupported program := by
  induction program, names, next, loopTargets using ssaCcTrans.induct
  case case4 instruction map n tables output mapOut nextOut generated =>
    simpa only [ssaCcTrans, generated] using ssaInstructionMemoryGuard instruction map n
  case case10 cmp r ri left right map n tables outL mapL nL hL outR mapR nR hR prio consL consR nf mf hFix ihL ihR =>
    have helpers := ssaFixMemoryGuard (width := width) prio mapL mapR nR
    simp only [hFix] at helpers
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case11 count sets map n tables allNames names first mapFirst nFirst hFirst cut second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveMemoryGuard (width := width) map (n + 2) names
    have back := ssaRenameMoveMemoryGuard (width := width) cut (nFirst + 2) names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case18 ptr len dptr dlen sets map n tables allNames names first mapFirst nFirst hFirst cut
      result mapResult nResult hResult second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveMemoryGuard (width := width) map (n + 2) names
    have back := ssaRenameMoveMemoryGuard (width := width) mapResult nResult names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case21 index ptr1 len1 ptr2 len2 sets map n tables allNames names first mapFirst nFirst hFirst cut second mapSecond nSecond hSecond =>
    have front := ssaRenameMoveMemoryGuard (width := width) map (n + 2) names
    have back := ssaRenameMoveMemoryGuard (width := width) cut (nFirst + 2) names
    simp only [hFirst] at front
    simp only [hSecond] at back
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case22 target arguments handler map n tables =>
    rcases handler with _ | ⟨exception, body, l1, l2⟩ <;> simp [ssaCcTrans, nativeMemorySupported]
  case case23 ret sets body l1 l2 target arguments map n tables allNames names mapStack nStack cut
      returnMove mapRet nRet hRet namesRet mapNames nNames hNames out mapOut nOut hOut stackMove hStack ih =>
    have stack := ssaRenameMoveMemoryGuard (width := width) map (n + 2) names
    have back := ssaRenameMoveMemoryGuard (width := width) cut (nStack + 2) names
    simp only [hStack] at stack
    simp only [hRet] at back
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case24 ret sets retBody l1 l2 target arguments map n tables allNames names mapStack nStack cut
      retMove mapRet nRet hRetMove retNames mapNames nNames hRetNames outRet mapRetOut nRetOut hRetOut
      regs movRet exception excBody excL1 excL2 stackMove exceptionReg mapExc nExc hExcRename
      outExc mapExcOut nExcOut hExcOut movExc prio consRet consExc nf mf hFix hStack ihRet ihExc =>
    have stack := ssaRenameMoveMemoryGuard (width := width) map (n + 2) names
    have back := ssaRenameMoveMemoryGuard (width := width) cut (nStack + 2) names
    have helpers := ssaFixMemoryGuard (width := width) prio mapRetOut mapExcOut nExcOut
    simp only [hStack] at stack
    simp only [hRetMove] at back
    simp only [hFix] at helpers
    simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  case case27 live body exits map n tables setup mapSetup nSetup hSetup bodyMap out mapOut nOut hOut ih =>
    have setupSupported := ssaLoopSetupMemoryGuard (width := width) live exits map n
    have backSupported := ssaReconcileMemoryGuard (width := width) mapOut mapSetup live
    simp only [hSetup] at setupSupported
    dsimp only [bodyMap] at hOut ih
    simp only [hOut] at ih
    simp only [ssaCcTrans, hSetup, hOut]
    generalize hb : ssaReconcile (width := width) mapOut mapSetup live = moves at backSupported ⊢
    cases moves <;> simp_all +zetaDelta [nativeMemorySupported]
  case case29 n map next tables target live exits found =>
    have back := ssaReconcileMemoryGuard (width := width) map target exits
    simp only [ssaCcTrans, found]
    generalize hb : ssaReconcile (width := width) map target exits = output at back ⊢
    cases output <;> simp_all [nativeMemorySupported]
  case case31 n map next tables target live exits found =>
    have back := ssaReconcileMemoryGuard (width := width) map target live
    simp only [ssaCcTrans, found]
    generalize hb : ssaReconcile (width := width) map target live = output at back ⊢
    cases output <;> simp_all [nativeMemorySupported]
  all_goals simp_all +zetaDelta [ssaCcTrans, nativeMemorySupported]
  all_goals try (split <;> simp_all [nativeMemorySupported])


/-- The full native setup/body pass retains the actual allocation domain.
This guard has no HOL original and is not added to the HOL theorem statement. -/
theorem fullSsaProgramMemoryGuard {width : Nat} [NeZero width]
    (count : Nat) (program : WordLangProgHOL (BitVec width)) :
    nativeMemorySupported (fullSsaCcTrans count program) = nativeMemorySupported program := by
  simp [fullSsaCcTrans, nativeMemorySupported, ssaSetupMemoryGuard, ssaProgramMemoryGuard]

end Flapjack.WordAlloc
