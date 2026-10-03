import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

/-- Sum the callee and normal-continuation IH clocks in the actual SOME
returning Call. The native callee Return is extended by the continuation clock
and full native dispatch executes the continuation. These local execution
premises are outputs of the original guarded IHs, not assumptions of a full
pass-correctness port. Flapjack handler-case execution composition. -/
theorem returningHandlerCallNormalRun {width : Nat} [NeZero width] {C F : Type}
    (target bodyPost targetPost : StackSemStateFiniteExact width C F)
    (l1 l2 h1 h2 bodyExtra continuationExtra : Nat) (destination : Sum Nat Nat)
    (body continuation handler : HolProg width) (result : Option (StackSemResult width))
    (found : StackSemControl.findCode destination (target.regs.eraseEq 0) target.code = some body)
    (nonzero : target.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (body,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
        clock := (StackSemStateOps.decClock target).clock+bodyExtra}) =
      (some (.result (.loc l1 l2)),bodyPost))
    (continuationRun : StackSemEvaluate.evaluate
      (continuation,{bodyPost with clock := bodyPost.clock+continuationExtra}) =
      (result,targetPost)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation,0,l1,l2)) destination (some (handler,h1,h2)),
        {target with clock := target.clock+(bodyExtra+continuationExtra)}) =
      (result,targetPost) := by
  have extended := Compiler.Backend.StackProps.evaluateAddClock continuationExtra body
    {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock+bodyExtra}
    (some (.result (.loc l1 l2))) bodyPost ⟨bodyRun,by simp⟩
  simp only [Nat.add_assoc] at extended
  rw [returningCallDispatchClock target 0 l1 l2 (bodyExtra+continuationExtra)
    destination body continuation (some (handler,h1,h2)) found nonzero]
  change (match StackSemEvaluate.evaluate
    (body,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock+(bodyExtra+continuationExtra)}) with
    | (some (.result location),post) =>
        if location ≠ WordLocW.loc l1 l2 then (some StackSemResult.error,post)
        else StackSemEvaluate.evaluate (continuation,post)
    | (some (.exception location),post) =>
        if location ≠ WordLocW.loc h1 h2 then (some StackSemResult.error,post)
        else StackSemEvaluate.evaluate (handler,post)
    | (none,post) => (some StackSemResult.error,post)
    | (some (.break _),post) => (some StackSemResult.error,post)
    | (some (.continue _),post) => (some StackSemResult.error,post)
    | (result,post) => (result,post)) = _
  rw [extended]
  simpa only [ne_eq,not_true_eq_false,↓reduceIte] using continuationRun

/-- Sum the callee and handler IH clocks in the actual SOME returning Call.
The native exception's original handler label selects the real handler code;
clock extension comes from evaluate_add_clock, with no enclosing Call run
premise. Local body/handler executions are original guarded IH outputs.
Flapjack matching-exception execution composition, not the full HOL case. -/
theorem returningHandlerCallExceptionRun {width : Nat} [NeZero width] {C F : Type}
    (target bodyPost targetPost : StackSemStateFiniteExact width C F)
    (l1 l2 h1 h2 bodyExtra handlerExtra : Nat) (destination : Sum Nat Nat)
    (body continuation handler : HolProg width) (result : Option (StackSemResult width))
    (found : StackSemControl.findCode destination (target.regs.eraseEq 0) target.code = some body)
    (nonzero : target.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (body,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
        clock := (StackSemStateOps.decClock target).clock+bodyExtra}) =
      (some (.exception (.loc h1 h2)),bodyPost))
    (handlerRun : StackSemEvaluate.evaluate
      (handler,{bodyPost with clock := bodyPost.clock+handlerExtra}) = (result,targetPost)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation,0,l1,l2)) destination (some (handler,h1,h2)),
        {target with clock := target.clock+(bodyExtra+handlerExtra)}) =
      (result,targetPost) := by
  have extended := Compiler.Backend.StackProps.evaluateAddClock handlerExtra body
    {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock+bodyExtra}
    (some (.exception (.loc h1 h2))) bodyPost ⟨bodyRun,by simp⟩
  simp only [Nat.add_assoc] at extended
  rw [returningCallDispatchClock target 0 l1 l2 (bodyExtra+handlerExtra)
    destination body continuation (some (handler,h1,h2)) found nonzero]
  change (match StackSemEvaluate.evaluate
    (body,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock+(bodyExtra+handlerExtra)}) with
    | (some (.result location),post) =>
        if location ≠ WordLocW.loc l1 l2 then (some StackSemResult.error,post)
        else StackSemEvaluate.evaluate (continuation,post)
    | (some (.exception location),post) =>
        if location ≠ WordLocW.loc h1 h2 then (some StackSemResult.error,post)
        else StackSemEvaluate.evaluate (handler,post)
    | (none,post) => (some StackSemResult.error,post)
    | (some (.break _),post) => (some StackSemResult.error,post)
    | (some (.continue _),post) => (some StackSemResult.error,post)
    | (result,post) => (result,post)) = _
  rw [extended]
  simpa only [ne_eq,not_true_eq_false,↓reduceIte] using handlerRun

/-- Connect the matched source Return and original callee IH output to the
actual enclosing SOME Call and full original caller contract. The real guarded
continuation IH constructs continuation execution; source Call guards derive
the return label, and native clock composition derives the enclosing run.
Original continuation-local compilation/bitmap/label context remains explicit here,
to be discharged through the whole caller prelude/body. The callee run is the
original body IH output, not an assumed enclosing target evaluation. Flapjack
normal-branch assembly, not the complete pass-correctness port. -/
theorem normalHandlerCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode handlerTarget : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ continuationExtra targetPost targetResult,
      StackSemEvaluate.evaluate
        (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled)),0,l1,l2))
          destination (some (handlerTarget,h1,h2)),
          {moved with clock := moved.clock+(bodyExtra+continuationExtra)}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,continuationIH⟩ := sourceHandlerReturningContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location returnedValues guards ih nonzero wholeRun notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨continuationExtra,targetPost,targetResult,continuationRun,conclusion⟩ :=
    simulateHandlerNormalContinuation ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion bs bsPost n nPost compiled compilation lengthBound
      bitmapBound bitmapPrefix labels
  have normalRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result (.loc l1 l2)),target) := by
    simpa only [locationEq] using calleeRun
  have skipped : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled)),
        {target with clock := target.clock+continuationExtra}) = (targetResult,targetPost) := by
    rw [CallReturnEval.seq_skip_left]
    exact continuationRun
  exact ⟨continuationExtra,targetPost,targetResult,
    returningHandlerCallNormalRun moved target targetPost l1 l2 h1 h2 bodyExtra continuationExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled))) handlerTarget targetResult
      found movedNonzero normalRun skipped,conclusion⟩

/-- Connect the matched source exception and original callee IH output to
actual enclosing SOME Call execution and the full original caller contract.
The source Call derives its exception label; the guarded handler IH constructs
execution after the derived full caller relation, and native clock composition
constructs the enclosing Call. Original handler compiler/bitmap/label context
is explicit pending whole-prelude/body transport. The callee run is an
original IH output, not an enclosing target-run premise. Flapjack branch
assembly, not the full guarded Call correctness port. -/
theorem exceptionHandlerCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode continuationTarget : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception location),target))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false handlerCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ handlerExtra targetPost targetResult,
      StackSemEvaluate.evaluate
        (.call (some (continuationTarget,0,l1,l2)) destination (some (compiled,h1,h2)),
          {moved with clock := moved.clock+(bodyExtra+handlerExtra)}) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  obtain ⟨valid,domain,sourceContinuation,continuationIH⟩ := sourceHandlerExceptionContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location value guards ih nonzero wholeRun notError bodyRun
  have locationEq : location = .loc h1 h2 := by
    by_contra different
    exact valid different
  obtain ⟨handlerExtra,targetPost,targetResult,handlerRun,conclusion⟩ :=
    simulateHandlerExceptionContinuation ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location value
      bodyRun calleeSize calleeFrame bodyConclusion bs bsPost n nPost compiled compilation lengthBound
      bitmapBound bitmapPrefix labels
  have exceptionRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception (.loc h1 h2)),target) := by
    simpa only [locationEq] using calleeRun
  exact ⟨handlerExtra,targetPost,targetResult,
    returningHandlerCallExceptionRun moved target targetPost l1 l2 h1 h2 bodyExtra handlerExtra
      destination calleeCode continuationTarget compiled targetResult found movedNonzero exceptionRun
      handlerRun,conclusion⟩

end Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
