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

/-- Compose the actual SOME destination/save/Push/argument prelude and
enclosing native Call into the literal full compiled programme. Compiler
equations identify both continuations and all prefixes; unconditional clock
transport derives moved.clock = target.clock, retaining every Call outcome.
The local prelude and Call executions are constructed by the guarded case
components; no full compiled evaluation is assumed. Flapjack composition
inside the still-unassembled original returning-handler correctness case. -/
theorem completeHandlerCallFromPrelude {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 handlerVar h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destination : Sum Nat Nat)
    (target moved targetPost : StackSemStateFiniteExact width C F)
    (extra : Nat) (result : Option (StackSemResult width))
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (none,moved))
    (callRun : StackSemEvaluate.evaluate
      (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode)),0,l1,l2))
        destination (some (handlerTarget,h1,h2)),{moved with clock := moved.clock+extra}) =
      (result,targetPost)) :
    StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
      (result,targetPost) := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have shifted := free target (target.clock+extra)
  rw [preludeRun] at shifted
  simp only [Prod.map,id_eq] at shifted
  have outputClock : {moved with clock := target.clock+extra} =
      {moved with clock := moved.clock+extra} := by rw [clockEq]
  rw [outputClock] at shifted
  rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
    Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc] at shifted
  simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
    Bool.false_eq_true,if_false,Prod.mk.injEq] at compilation
  obtain ⟨rfl,_⟩ := compilation
  rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
    Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
    Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc]
  rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,shifted]
  simp only
  rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
    StackSemEvaluate.evaluate_skip]
  exact callRun

/-- Actual enclosing native SOME Call for the terminal callee branches. The
callee execution is the original IH output; dispatch derives the whole Call
run, retaining Timeout, Halt and FinalFFI and their exact native post-states.
This is case-local execution composition, not a full HOL correctness port. -/
theorem returningHandlerCallTerminalRun {width : Nat} [NeZero width] {C F : Type}
    (target targetPost : StackSemStateFiniteExact width C F)
    (l1 l2 h1 h2 extra : Nat) (destination : Sum Nat Nat)
    (body continuation handler : HolProg width) (result : Option (StackSemResult width))
    (found : StackSemControl.findCode destination (target.regs.eraseEq 0) target.code = some body)
    (nonzero : target.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
        clock := (StackSemStateOps.decClock target).clock + extra}) = (result, targetPost))
    (terminal : result = some .timeOut ∨ (∃ value, result = some (.halt value)) ∨
      ∃ event, result = some (.finalFFI event)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination (some (handler,h1,h2)),
        {target with clock := target.clock + extra}) = (result, targetPost) := by
  rw [returningCallDispatchClock target 0 l1 l2 extra
    destination body continuation (some (handler,h1,h2)) found nonzero]
  change (match StackSemEvaluate.evaluate
    (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock target) with
      clock := (StackSemStateOps.decClock target).clock + extra}) with
    | (some (.result location), post) =>
        if location ≠ WordLocW.loc l1 l2 then (some StackSemResult.error, post)
        else StackSemEvaluate.evaluate (continuation, post)
    | (some (.exception location), post) =>
        if location ≠ WordLocW.loc h1 h2 then (some StackSemResult.error,post)
        else StackSemEvaluate.evaluate (handler,post)
    | (none, post) => (some StackSemResult.error, post)
    | (some (.break _), post) => (some StackSemResult.error, post)
    | (some (.continue _), post) => (some StackSemResult.error, post)
    | (result, post) => (result, post)) = _
  rw [bodyRun]
  rcases terminal with rfl | ⟨value, rfl⟩ | ⟨event, rfl⟩ <;> rfl


/-- Connect the actual terminal native Call execution with the full original
caller contract. The callee run and contract are outputs of the original
callee IH. Matching terminal results use exact source propagation; unmatched
results use the full trace/resource branch and all source outcomes remain
available. No enclosing target Call run is assumed. This is a case-local
assembly component; the full guarded theorem remains open. -/
theorem terminalHandlerCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width)) (l1 l2 handlerVar h1 h2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (initial moved targetPost : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (extra : Nat) (destination : Sum Nat Nat) (body continuation handlerTarget : HolProg width)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some body)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + extra}) = (targetResult, targetPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))
      bodyPost targetPost bodyResult targetResult (callerFrame :: lens))
    (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
      ∃ event, targetResult = some (.finalFFI event)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination (some (handlerTarget,h1,h2)),
        {moved with clock := moved.clock + extra}) = (targetResult, targetPost) ∧
    compCorrectResult ac k callerSize callerFrame source sourcePost targetPost result targetResult lens := by
  constructor
  · exact returningHandlerCallTerminalRun moved targetPost l1 l2 h1 h2 extra destination body continuation handlerTarget
      targetResult found movedNonzero calleeRun terminal
  · by_cases matching : bodyResult.map compileResult = targetResult
    · exact handlerBodyTerminalResult ac k callerSize callerFrame calleeSize calleeFrame values names
        retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult targetPost targetResult
        lens xs args1 prog ss envs guards nonzero execution bodyRun
        (CallReturning.matchingTerminalSource bodyResult targetResult matching terminal) bodyConclusion matching
    · exact handlerBodyMismatchResult ac k callerSize callerFrame calleeSize calleeFrame values names
        retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult initial targetPost
        targetResult lens xs args1 prog ss envs guards callerRelation nonzero execution bodyRun
        bodyConclusion matching

end Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
