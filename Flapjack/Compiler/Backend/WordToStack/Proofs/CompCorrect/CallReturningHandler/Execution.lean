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

/-- Actual prelude/callee execution transports the original code and bitmap
context to the body poststate. Link initialization, decrement and the original
IH clock extension preserve these carriers. Flapjack history composition;
neither code growth nor bitmap growth is supplied as a premise. -/
theorem handlerCalleeHistoryGrowth {width : Nat} [NeZero width] {C F : Type}
    (initial moved target : StackSemStateFiniteExact width C F)
    (prelude callee : HolProg width) (l1 l2 extra : Nat)
    (result : Option (StackSemResult width))
    (preludeRun : StackSemEvaluate.evaluate (prelude,initial) = (none,moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+extra}) = (result,target)) :
    initial.bitmaps.IsPrefix target.bitmaps ∧ sptSubspt initial.code target.code := by
  have preludeGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    prelude initial moved none preludeRun
  have calleeGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono callee
    {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
      clock := (StackSemStateOps.decClock moved).clock+extra} target result calleeRun
  change moved.bitmaps.IsPrefix target.bitmaps ∧ sptSubspt moved.code target.code at calleeGrowth
  exact ⟨preludeGrowth.1.trans calleeGrowth.1,
    sptSubsptTrans _ _ _ ⟨preludeGrowth.2,calleeGrowth.2⟩⟩

/-- Derive the exception continuation's complete original compiler context
from whole SOME compilation and initial guards. Both save and return compiler
accounting derive the handler input offset; the whole programme supplies its
handler labels. No handler-local length, bitmap or label guard is assumed.
Flapjack compiler-context elimination, without a standalone HOL declaration. -/
theorem handlerExceptionCompilationContext {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destination : Sum Nat Nat) (target : StackSemStateFiniteExact width C F)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (wholeCompile : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    (appListAppend retBs).length ≤ retIndex ∧
    retIndex-(appListAppend retBs).length ≤ target.bitmaps.length ∧
    (appListAppend handlerBs).IsPrefix (target.bitmaps.drop (retIndex-(appListAppend retBs).length)) ∧
    (∀ loc, StackSem.getLabelsExact handlerTarget loc → StackSem.locCheckExact target.code loc) := by
  have savedAccounting := wLiveLength names (bs,n) (k,frame,payload) savedCode (savedBs,savedIndex)
    ⟨savedCompile,lengthBound⟩
  have returnAccounting := compImpLength ac false retCode (savedBs,savedIndex) (k,frame,payload)
    returnCode (retBs,retIndex) ⟨returnCompile,savedAccounting.1⟩
  have gap : retIndex-(appListAppend retBs).length = n-(appListAppend bs).length :=
    returnAccounting.2.symm.trans savedAccounting.2.symm
  refine ⟨returnAccounting.1,?_,?_,?_⟩
  · rwa [gap]
  · rwa [gap]
  · intro loc member
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at wholeCompile
    obtain ⟨rfl,_⟩ := wholeCompile
    apply labels loc
    simp only [StackSem.getLabelsExact]
    aesop (config := { enableSimp := false })

/-- Derive full literal compiled SOME Call execution and original caller
contract in the matched normal branch from original whole compilation and
actual prelude/callee IH history. The continuation compiler/bitmap/label
obligations and moved clock guard are discharged internally; the guarded
continuation IH constructs its execution. No continuation-local metadata or
full compiled target run is assumed. The explicit callee execution/contract
are original body IH outputs, pending top-level guarded setup assembly.
Flapjack case assembly, not the complete all-outcomes correctness port. -/
theorem normalCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
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
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
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
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.result location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerReturningCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,callRun,conclusion⟩ :=
    normalHandlerCallFromCallee ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode handlerTarget bodyExtra found movedNonzero calleeRun
      savedBs retBs savedIndex retIndex returnCode returnCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion⟩

/-- Derive full literal compiled SOME Call execution and original caller
contract in the matched exception branch from original whole compilation and
actual prelude/callee IH history. The continuation compiler/bitmap/label
obligations and moved clock guard are discharged internally; the guarded
continuation IH constructs its execution. No continuation-local metadata or
full compiled target run is assumed. The explicit callee execution/contract
are original body IH outputs, pending top-level guarded setup assembly.
Flapjack case assembly, not the complete all-outcomes correctness port. -/
theorem exceptionCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
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
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
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
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.exception location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerExceptionCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact handlerTarget loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,callRun,conclusion⟩ :=
    exceptionHandlerCallFromCallee ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location value
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) bodyExtra found movedNonzero calleeRun
      retBs handlerBs retIndex handlerIndex handlerTarget handlerCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion⟩

/-- The actual non-error SOME source Call excludes body NONE/Error/Break/
Continue through its real evaluator clauses. Every Return, exception, timeout,
resource result and final FFI remains. This is derived outcome classification,
not a restriction added to the original theorem or a separate HOL port. -/
theorem handlerCalleeOutcomeCases {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width)) (l1 l2 handlerVar h1 h2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (notError : result ≠ some .error) :
    (∃ location returned, bodyResult = some (.result location returned)) ∨
    (∃ location value, bodyResult = some (.exception location value)) ∨
    bodyResult = some .timeOut ∨ bodyResult = some .notEnoughSpace ∨
    ∃ event, bodyResult = some (.finalFfi event) := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  cases bodyResult with
  | none => exact False.elim (notError (Prod.mk.inj execution).1.symm)
  | some value =>
    cases value
    case result location returned => exact Or.inl ⟨location, returned, rfl⟩
    case exception location value => exact Or.inr (Or.inl ⟨location, value, rfl⟩)
    case timeOut => exact Or.inr (Or.inr (Or.inl rfl))
    case notEnoughSpace => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    case finalFfi event => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨event, rfl⟩)))
    all_goals exact False.elim (notError (Prod.mk.inj execution).1.symm)

/-- Full original result and actual compiled execution for the successful
handler callee-entry branch. Actual setup constructs the callee relation and
the original guarded body IH constructs its target execution/contract. Every
source body outcome and every matching/resource IH alternative is assembled;
whole compiler context and actual history discharge both continuation IHs.
No target run, callee contract, continuation metadata or outcome restriction
is assumed. The room/space premises are the original successful-entry case
split; header/argument allocation failures and zero clock remain separate
original branches for the final constructor theorem. Untagged Flapjack case
assembly, not a narrowed claim of the complete Call port. -/
theorem simulateSuccessfulHandlerCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k frame payload source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * payload + 2 * k)
    (destinationCompile : callDestNative dest args (k, frame, payload) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, frame, payload) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (space : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3)
    (nonzero : source.clock ≠ 0)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) = (bodyResult,bodyPost))
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    ∃ extra targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens := by
  have returnPrefix := compImpIsPrefix ac false retCode (savedBitmaps,savedIndex) (k,frame,payload)
    returnCode (retBs,retIndex) returnCompile
  have handlerPrefix := compImpIsPrefix ac false handlerCode (retBs,retIndex) (k,frame,payload)
    handlerTarget (handlerBs,handlerIndex) handlerCompile
  have savedPrefix := returnPrefix.trans (handlerPrefix.trans bitmapPrefix)
  have handlerLocation : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨destinationTarget,saved,header,moved,entry,calleeTarget,calleeCode,body,
    calleeSize,calleeFrame,bodyExtra,targetResult,destinationRun,savedRun,pushRun,argumentsRun,
    found,calleeShape,allocationRun,bodyTargetRun,calleeRun,bodyConclusion⟩ :=
    simulateHandlerCalleeBody ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost bodyPost result bodyResult target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions maximum
      destinationCompile savedCompile bitmapLength bitmapBound savedPrefix room handlerLocation space
      nonzero wholeExecution notError bodyRun hypotheses
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,pushRun]
    exact argumentsRun
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBitmaps,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
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
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq,← related.1]; exact nonzero
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
          (finalResult,targetFinal) ∧
        compCorrectResult ac k frame payload source sourcePost targetFinal result finalResult lens := by
    obtain ⟨callRun,conclusion⟩ := terminalHandlerCallFromCallee ac k frame payload calleeSize calleeFrame
      values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost
      result bodyResult target moved calleeTarget targetResult lens xs args1 prog ss envs bodyExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) handlerTarget guards related nonzero
      wholeExecution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    exact ⟨bodyExtra,calleeTarget,targetResult,
      completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
        h1 h2 dest args bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
        savedCode returnCode handlerTarget compiled destination target moved calleeTarget bodyExtra targetResult
        destinationCompile savedCompile returnCompile handlerCompile compilation preludeRun callRun,conclusion⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := handlerCalleeOutcomeCases values names retCode handlerCode l1 l2 handlerVar h1 h2
      dest args source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero
      wholeExecution bodyRun notError
    rcases outcomes with ⟨location,returned,rfl⟩ | ⟨location,value,rfl⟩ | timeout | resource | ⟨event,ffi⟩
    · have targetEq : targetResult = some (.result location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      exact normalCompiledHandlerCallFromHistory ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location returned bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
    · have targetEq : targetResult = some (.exception location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      exact exceptionCompiledHandlerCallFromHistory ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location value bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
    · apply finishTerminal
      left
      simpa only [timeout,Option.map_some,compileResult] using matching.symm
    · apply finishTerminal
      right; left
      exact ⟨.word 1,by simpa only [resource,Option.map_some,compileResult] using matching.symm⟩
    · apply finishTerminal
      right; right
      exact ⟨event,by simpa only [ffi,Option.map_some,compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2,mismatch.1⟩))

/-- Transport actual source callee-entry overflow through every real SOME
Call branch, including zero-clock flushing, invalid return/pop/domain checks
and normal/exception continuations. The entry resource premise is constructed
by the original allocation-case relation lemmas at its consumers; no trace or
target execution is assumed. Flapjack resource transport, not a full port. -/
theorem handlerSourceCallEntryOverflow {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (overflow : miscThe (source.stackLimit+1)
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source)).stackMax >
      source.stackLimit)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost)) :
    miscThe (sourcePost.stackLimit + 1) sourcePost.stackMax > sourcePost.stackLimit := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  by_cases clock : source.clock = 0
  · rw [dif_pos clock] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact overflow
  rw [dif_neg clock, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) with
      ⟨bodyResult, bodyPost⟩
  have bodyOverflow := WordSemStateFiniteExact.evaluate_stack_limit_stack_max prog _ bodyResult bodyPost
    ⟨bodyRun, overflow⟩
  rw [bodyRun] at execution
  rcases bodyResult with _ | bodyResult
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact bodyOverflow
  cases bodyResult <;> try (
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact bodyOverflow)
  case result location returned =>
    simp only at execution
    by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
    · rw [if_pos invalid] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact bodyOverflow
    rw [if_neg invalid] at execution
    rcases pop : WordSemStateFiniteExact.popEnv bodyPost with _ | popped
    · rw [pop] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact bodyOverflow
    rw [pop] at execution
    simp only at execution
    have properties := WordSemStateFiniteExact.popEnvConst bodyPost popped pop
    have poppedLimit : popped.stackLimit = bodyPost.stackLimit := by
      aesop (config := { enableSimp := false })
    have poppedMaximum : popped.stackMax = bodyPost.stackMax := by
      aesop (config := { enableSimp := false })
    have poppedOverflow : miscThe (popped.stackLimit + 1) popped.stackMax > popped.stackLimit := by
      rw [poppedLimit, poppedMaximum]
      exact bodyOverflow
    by_cases domain : sptDomainEqUnion popped.locals envs.1 envs.2
    · rw [if_pos domain] at execution
      exact WordSemStateFiniteExact.evaluate_stack_limit_stack_max retCode _ result sourcePost
        ⟨execution, poppedOverflow⟩
    · rw [if_neg domain] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact poppedOverflow
  case exception location value =>
    simp only at execution
    by_cases invalid : location ≠ .loc h1 h2
    · rw [if_pos invalid] at execution
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj execution
      exact bodyOverflow
    rw [if_neg invalid] at execution
    by_cases domain : sptDomainEqUnion bodyPost.locals envs.1 envs.2
    · rw [if_pos domain] at execution
      exact WordSemStateFiniteExact.evaluate_stack_limit_stack_max handlerCode _ result sourcePost
        ⟨execution,bodyOverflow⟩
    · rw [if_neg domain] at execution
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj execution
      exact bodyOverflow


/-- Construct literal whole compiled execution and FULL original caller
contract when the original target has insufficient handler-header room.
The real destination/save/Push run derives Halt 2 and its FFI; original caller
conventions and stack relation derive entry overflow, transported through the
actual source Call including zero clock. No target run, overflow or trace
premise is supplied. This is an original allocation branch, untagged pending
final complete constructor assembly and source review. -/
theorem compiledHandlerHeaderFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBs : AppList (BitVec width)) (handlerIndex : Nat)
    (handlerTarget compiled : HolProg width)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,f,frame) =
      (compiled,(handlerBs,handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (noRoom : target.stackSpace < 3) :
    ∃ targetPost,
      StackSemEvaluate.evaluate (compiled,target) = (some (.halt (.word 2)),targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result (some (.halt (.word 2))) lens := by
  have retPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame)
    handlerTarget (handlerBs,handlerIndex) handlerCompile).trans bitmapPrefix
  obtain ⟨targetPost,headerRun,ffi⟩ := evaluateHandlerHeaderNoRoom ac k f frame values names retCode
    l1 l2 dest args handlerVar h1 h2 handlerCode source target lens xs args1 prog ss envs bs
    savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode destination
    guards related conventions maximum destinationCompile savedCompile returnCompile lengthBound
    bitmapBound retPrefix noRoom
  have compiledRun : StackSemEvaluate.evaluate (compiled,target) =
      (some (.halt (.word 2)),targetPost) := by
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,headerRun]
    rfl
  have nonempty : ¬ sptDomainEmpty names.1 := by
    intro empty
    exact guards.2.2.2.1 (Or.inl empty)
  have positive := handlerCallerPayloadPositive k frame values names retCode handlerCode
    l1 l2 h1 h2 handlerVar dest args nonempty conventions maximum
  have shape : if frame = 0 then f = 0 else f = frame+1 :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have framePositive : 0 < f := by split at shape <;> omega
  have resource := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have entryOverflow := handlerNoRoomSourceLimit source envs handlerVar h1 h2 handlerCode args1 ss
    f target.stackSpace target.stack resource framePositive bound noRoom
  have overflow : miscThe (source.stackLimit+1)
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source)).stackMax >
      source.stackLimit := by
    cases maximum : (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source)).stackMax <;>
      simpa only [maximum,miscThe,Option.getD_none,Option.getD_some] using entryOverflow
  have finalOverflow := handlerSourceCallEntryOverflow values names retCode l1 l2 dest args handlerVar h1 h2
    handlerCode source sourcePost result xs args1 prog ss envs guards overflow execution
  have events := WordSemStateFiniteExact.evaluate_io_events_mono
    (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2)))
    source result sourcePost execution
  have dimension : goodDimindex width :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mismatch : result.map compileResult ≠ some (.halt (.word (2 : BitVec width))) := by
    cases result with
    | none => simp
    | some value =>
      intro equal
      exact CallHelpers.compileResultNot2 value dimension (Option.some.inj equal)
  refine ⟨targetPost,compiledRun,?_⟩
  unfold compCorrectResult
  rw [if_pos mismatch]
  refine ⟨rfl,?_,?_⟩
  · rw [ffi]
    exact events
  · cases maximum : sourcePost.stackMax <;>
      simpa only [maximum,miscThe,Option.getD_none,Option.getD_some] using finalOverflow

/-- Literal handler argument allocation fails before any stack move, and
before any following Call. This local transition is used by the original
allocation-failure branch; its resource guard is derived from the saved
caller relation at the whole-case consumer. Flapjack composition infrastructure. -/
theorem handlerArgumentsAllocationFailure {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (argCount k f frame : Nat) (continuation : HolProg width)
    (useStack : target.useStack = true)
    (insufficient : target.stackSpace < Compiler.Backend.WordToStack.stackArgCount destination argCount k) :
    StackSemEvaluate.evaluate
      (.seq (stackHandlerArgsNative false destination argCount (k,f,frame)) continuation,target) =
      (some (.halt (.word 2)),StackSemStateOps.emptyEnv target) := by
  rw [CallReturnHandler.stackHandlerArgsF]
  unfold stackArgsNative
  rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
    CallReturnEval.evaluateStackMoveSeq,StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate,StackSemEvaluate.evaluate_stackAlloc]
  simp only [useStack,Bool.not_true,Bool.false_eq_true,if_false,insufficient,if_true]
  rfl

/-- Argument allocation failure paired with the FULL original caller contract.
Actual callee compilation derives argument capacity; the saved caller relation
then derives source overflow through every actual source outcome. The local
count equality and callee metadata are obtained from destination lookup at the
whole-case consumer. No target execution or source overflow is assumed.
Flapjack original-case factoring, not a complete theorem-port claim. -/
theorem handlerArgumentsFailureResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame calleeSize : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destination : Sum Nat Nat) (continuation calleeCode : HolProg width)
    (calleeBs calleePostBs : AppList (BitVec width)) (calleeIndex calleePostIndex : Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with
        locals := .ln, localsSize := some 0} saved (frame :: lens) 0)
    (calleeCompile : compileProgNative ac false prog args1.length k (calleeBs,calleeIndex) =
      (calleeCode,calleeSize,(calleePostBs,calleePostIndex)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (count : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k = args1.length-k)
    (insufficient : saved.stackSpace < Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost)) :
    StackSemEvaluate.evaluate
      (.seq (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)) continuation,saved) =
      (some (.halt (.word 2)),StackSemStateOps.emptyEnv saved) ∧
    compCorrectResult ac k f frame source sourcePost (StackSemStateOps.emptyEnv saved)
      result (some (.halt (.word 2))) lens := by
  obtain ⟨body,calleeFrame,_,_,shape,capacity,_,_⟩ := calleeBodyCompilation ac k args1.length
    prog calleeBs calleePostBs calleeIndex calleePostIndex calleeCode calleeSize calleeCompile
  have calleeInsufficient : saved.stackSpace < calleeSize := by
    rw [count] at insufficient
    split at shape <;> omega
  have useStack : saved.useStack = true := pushedRelation.2.2.2.2.1
  refine ⟨handlerArgumentsAllocationFailure saved destination (args.length+1) k f frame
    continuation useStack insufficient,?_⟩
  have contract := handlerAllocationFailureResult ac k f frame calleeSize values names retCode l1 l2
    dest args handlerVar h1 h2 handlerCode source sourcePost saved lens result xs args1 prog ss envs
    saved.clock saved.stackSpace guards pushedRelation calleeLocalsSize calleeInsufficient execution
  have same : {saved with clock := saved.clock, stackSpace := saved.stackSpace} = saved := by
    cases saved
    rfl
  rw [same] at contract
  exact contract

/-- Whole literal compiled handler Call argument-failure branch. Original
caller state relation and actual source destination guards derive callee size,
argument count, saved relation and source overflow. Original whole compilation
and label context derive the handler location. No local metadata, target run,
overflow or narrowed source outcome is assumed. Untagged original-case
assembly pending the remaining callee allocation branch and full constructor. -/
theorem compiledHandlerArgumentsFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBs : AppList (BitVec width)) (handlerIndex : Nat)
    (handlerTarget compiled : HolProg width)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,f,frame) =
      (compiled,(handlerBs,handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (insufficient : target.stackSpace - 3 <
      Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k) :
    ∃ targetPost,
      StackSemEvaluate.evaluate (compiled,target) = (some (.halt (.word 2)),targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result (some (.halt (.word 2))) lens := by
  have retPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame)
    handlerTarget (handlerBs,handlerIndex) handlerCompile).trans bitmapPrefix
  have location : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨header,headerRun,headerRelation,headerSpace,_⟩ := evaluateHandlerHeader ac k f frame
    values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source target lens xs args1
    prog ss envs bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
    returnCode destination guards related conventions maximum destinationCompile savedCompile
    returnCompile lengthBound bitmapBound retPrefix room location
  have count := CallReturning.stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  obtain ⟨calleeLocation,calleeBs,calleePostBs,calleeIndex,calleePostIndex,body,calleeSize,
    calleeFrame,_,_,_,_,_,_,_,_,localSize,frameShape,capacity,_⟩ :=
    CallReturning.calleeCompilation ac k f frame values names retCode l1 l2 dest args source
      target lens xs args1 prog ss envs guards related
  have headerInsufficient : header.stackSpace <
      Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k := by omega
  have calleeInsufficient : header.stackSpace < calleeSize := by
    rw [count] at headerInsufficient
    split at frameShape <;> omega
  have contract := handlerAllocationFailureResult ac k f frame calleeSize values names retCode l1 l2
    dest args handlerVar h1 h2 handlerCode source sourcePost header lens result xs args1 prog ss envs
    header.clock header.stackSpace guards headerRelation localSize calleeInsufficient execution
  have same : {header with clock := header.clock, stackSpace := header.stackSpace} = header := by
    cases header
    rfl
  rw [same] at contract
  refine ⟨StackSemStateOps.emptyEnv header,?_,contract⟩
  have shape := compilation
  simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
    Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
  obtain ⟨rfl,_⟩ := shape
  rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
    Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
    StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,headerRun]
  simp only
  exact handlerArgumentsAllocationFailure header destination (args.length+1) k f frame _
    headerRelation.2.2.2.2.1 headerInsufficient

/-- Whole literal compiled handler Call failure at callee frame allocation.
The original successful header/argument guards and insufficient callee frame
are the HOL case split. Original caller relation and actual compiler lookup
construct every prefix transition and the failing native Call; they derive
source overflow and trace for the FULL caller contract. No target run or
postrelation is assumed. Untagged assembly pending full constructor review. -/
theorem compiledHandlerCalleeAllocationFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar, handlerCode, h1, h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBs : AppList (BitVec width)) (handlerIndex : Nat)
    (handlerTarget compiled : HolProg width)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,f,frame) =
      (compiled,(handlerBs,handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
      target.stackSpace - 3)
    (nonzero : source.clock ≠ 0)
    (insufficient : target.stackSpace - 3 <
      (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
       else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1)) :
    ∃ targetPost,
      StackSemEvaluate.evaluate (compiled,target) = (some (.halt (.word 2)),targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result (some (.halt (.word 2))) lens := by
  have retPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame)
    handlerTarget (handlerBs,handlerIndex) handlerCompile).trans bitmapPrefix
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps,savedIndex) (k,f,frame)
    returnCode (finalBitmaps,finalIndex) returnCompile).trans retPrefix
  have location : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleePostBs,
    calleeIndex,calleePostIndex,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,_,_,_,localSize,found,
    savedLookup,headerState,savedSpace,movedClock,movedFfi⟩ :=
    prepareHandlerCalleeDestination ac k f frame values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source target lens xs args1 prog ss envs bs savedBitmaps n savedIndex
      destinationCode savedCode destination guards related conventions maximum destinationCompile
      savedCompile lengthBound bitmapBound savedPrefix room location space
  obtain ⟨body,calleeFrame,calleeShape,_,frameShape,capacity,_,frameDef⟩ := calleeBodyCompilation ac k
    args1.length prog calleeBs calleePostBs calleeIndex calleePostIndex calleeCode calleeSize calleeCompile
  have sizeDef : calleeSize = if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1 := by
    rw [← frameDef]
    by_cases zero : calleeFrame = 0
    · simpa only [zero,if_true] using frameShape
    · simpa only [zero,if_false] using frameShape
  have count := CallReturning.stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have savedUseStack : saved.useStack = true := savedRelation.2.2.2.2.1
  have savedBound := savedRelation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have moveBound := CallReturning.stackArgumentFrameBound ac k f frame values names retCode l1 l2
    dest args source saved lens xs args1 prog ss envs destinationCode destination guards savedRelation
    (conventionsWithoutHandler k values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) conventions)
    (lt_of_le_of_lt (maximumWithoutHandler values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2))) maximum) destinationCompile
  have savedRoom : 3 ≤ saved.stackSpace := by omega
  have resources := CallReturnHandler.pushedHandlerStateResources saved h1 h2 k savedHandler savedRoom
  have headerSpace : header.stackSpace+3 = target.stackSpace := by
    rw [headerState]
    omega
  obtain ⟨moved',stack,regs,moveRun',movedState,_,_,movedSpace,_,_⟩ := evaluateHandlerArguments
    k f frame h1 h2 destination (args.length+1) saved savedHandler savedUseStack savedRoom savedBound
    moveBound (by rw [← headerState]; omega)
  rw [← headerState] at moveRun' movedState movedSpace
  have sameMoved : moved' = moved := (Prod.mk.inj (moveRun'.symm.trans moveRun)).2
  rw [sameMoved] at movedState movedSpace
  have movedUseStack : moved.useStack = true := by
    rw [movedState,headerState]
    exact savedUseStack
  have calleeInsufficient : header.stackSpace < calleeSize := by rw [sizeDef]; omega
  have allocInsufficient : moved.stackSpace < calleeSize-(args1.length-k) := by
    rw [count] at movedSpace
    split at frameShape <;> omega
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedClock,← related.1]
    exact nonzero
  let entry := StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
  have calleeRun : StackSemEvaluate.evaluate (calleeCode,entry) =
      (some (.halt (.word 2)),StackSemStateOps.emptyEnv entry) := by
    rw [calleeShape,StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_stackAlloc]
    change (match (if !moved.useStack then (some .error,entry)
      else if moved.stackSpace < calleeSize-(args1.length-k) then
        (some (.halt (.word (BitVec.ofNat width 2))),StackSemStateOps.emptyEnv entry)
      else (none,{entry with stackSpace := moved.stackSpace-(calleeSize-(args1.length-k))})) with
        | (none,state) => StackSemEvaluate.evaluate (body,state)
        | (res,state) => (res,state)) = _
    simp only [movedUseStack,Bool.not_true,Bool.false_eq_true,if_false,allocInsufficient,if_true]
    rfl
  have callRun : StackSemEvaluate.evaluate
      (.call (some (.seq .skip (copyRetNative false true (k,f,frame) values
        (popHandlerNative false (k,f,frame) returnCode)),0,l1,l2)) destination
        (some (handlerTarget,h1,h2)),moved) =
      (some (.halt (.word 2)),StackSemStateOps.emptyEnv entry) := by
    rw [StackSemEvaluate.evaluate_call]
    simp only
    rw [found]
    simp only
    rw [if_neg movedNonzero,StackSemEvaluateClock.fixClockEvaluate]
    rw [show StackSemStateOps.decClock (StackSemStateOps.setVar 0 (.loc l1 l2) moved) = entry from rfl,calleeRun]
  have overflow := handlerSourceCallOverflow ac k frame calleeSize values names retCode l1 l2 dest args
    handlerVar h1 h2 handlerCode source sourcePost header lens result xs args1 prog ss envs guards
    headerRelation localSize calleeInsufficient execution
  have events := WordSemStateFiniteExact.evaluate_io_events_mono
    (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2)))
    source result sourcePost execution
  have dimension : goodDimindex width :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mismatch : result.map compileResult ≠ some (.halt (.word (2 : BitVec width))) := by
    cases result with
    | none => simp
    | some value =>
      intro equal
      exact CallHelpers.compileResultNot2 value dimension (Option.some.inj equal)
  refine ⟨StackSemStateOps.emptyEnv entry,?_,?_⟩
  · have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,pushRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,moveRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,StackSemEvaluate.evaluate_skip]
    exact callRun
  · unfold compCorrectResult
    rw [if_pos mismatch]
    refine ⟨rfl,?_,?_⟩
    · change moved.ffi.ioEvents.IsPrefix sourcePost.ffi.ioEvents
      rwa [movedFfi]
    · cases maximum : sourcePost.stackMax <;>
        simpa only [maximum,miscThe,Option.getD_none,Option.getD_some] using overflow

/-- Assemble every original SOME-handler returning Call branch: header
failure, argument allocation failure, zero clock, callee allocation failure,
and every successful callee outcome with the original guarded continuation
IHs. Actual source guards remain explicit here and are derived from whole
source non-error at the constructor wrapper. No target run, resource outcome,
body execution, or strengthened induction hypothesis is assumed. Flapjack
assembly pending the literal constructor statement and source review. -/
theorem simulateHandlerCallWithGuards {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k frame payload source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * payload + 2 * k)
    (destinationCompile : callDestNative dest args (k, frame, payload) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, frame, payload) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    ∃ extra targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens := by
  by_cases room : 3 ≤ target.stackSpace
  · by_cases arguments : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
        target.stackSpace-3
    · by_cases zero : source.clock = 0
      · have location : StackSem.locCheckExact target.code (h1,h2) := by
          apply labels (h1,h2)
          have shape := compilation
          simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
            Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
          obtain ⟨rfl,_⟩ := shape
          simp only [StackSem.getLabelsExact,or_true,true_or]
        obtain ⟨targetPost,run,contract⟩ := compiledHandlerCallTimeout ac k frame payload values names
          retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost result target lens xs
          args1 prog ss envs bs savedBitmaps retBs n savedIndex retIndex destinationCode savedCode
          returnCode destination guards related conventions maximum destinationCompile savedCompile
          returnCompile handlerBs handlerIndex handlerTarget handlerCompile room location bitmapLength
          bitmapBound compiled compilation wholeExecution arguments zero bitmapPrefix
        refine ⟨0,targetPost,some .timeOut,?_,contract⟩
        have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
        rwa [unchanged]
      · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
            else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3
        · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
                (WordSemStateFiniteExact.decClock source))) with ⟨bodyResult,bodyPost⟩
          exact simulateSuccessfulHandlerCall ac k frame payload values names retCode l1 l2 dest args
            handlerVar h1 h2 handlerCode source sourcePost bodyPost result bodyResult target lens xs args1
            prog ss envs bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
            savedCode returnCode handlerTarget compiled destination guards related conventions flat maximum
            destinationCompile savedCompile returnCompile handlerCompile compilation bitmapLength bitmapBound
            bitmapPrefix labels room calleeSpace zero wholeExecution notError bodyRun hypotheses
        · obtain ⟨targetPost,run,contract⟩ := compiledHandlerCalleeAllocationFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
            handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
            n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
            maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
            handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
            room arguments zero (by omega)
          refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract⟩
          have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
          rwa [unchanged]
    · obtain ⟨targetPost,run,contract⟩ := compiledHandlerArgumentsFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
        handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
        n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
        maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
        handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
        room (by omega)
      refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract⟩
      have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
      rwa [unchanged]
  · obtain ⟨targetPost,run,contract⟩ := compiledHandlerHeaderFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
      n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
      maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
      handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix (by omega)
    refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract⟩
    have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
    rwa [unchanged]

/-- The entire original comp_correct induction motive for a returning Call
with SOME handler. Source guards and all native compiler subtrees are derived
from the actual source execution and whole compilation. Every resource and
clock branch is covered and every actual callee outcome uses only the original
guarded IHs. This full constructor assembly is untagged pending independent
source statement review; it assumes no target execution or final relation. -/
theorem returningHandlerCase {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source) :
    Seq.Simulation ac (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens facts
  obtain ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,
    bitmapPrefix,labels,maximum⟩ := facts
  obtain ⟨xs,args1,prog,ss,envs,guards⟩ := sourceGuardsOfNotErrorWithHandler values names retCode
    l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k,f,frame) with ⟨destinationCode,destination⟩
  rcases savedCompile : wLiveNative (width := width) names (bs,n) (k,f,frame) with ⟨savedCode,savedBitmaps,savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,f,frame) with
    ⟨returnCode,retBs,retIndex⟩
  rcases handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,f,frame) with
    ⟨handlerTarget,handlerBs,handlerIndex⟩
  have shape := compilation
  simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
    Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
  obtain ⟨_,rfl,rfl⟩ := shape
  exact simulateHandlerCallWithGuards ac k f frame values names retCode l1 l2 dest args
    handlerVar h1 h2 handlerCode source sourcePost result target lens xs args1 prog ss envs bs
    savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
    returnCode handlerTarget compiled destination guards related conventions flat maximum
    destinationCompile savedCompile returnCompile handlerCompile compilation lengthBound bitmapBound
    bitmapPrefix labels execution notError hypotheses

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Literal evaluate_ind returning-handler hypotheses establish the FULL
original comp_correct constructor motive. The intermediate source tuple and
result binders are retained exactly; the fixed SOME return makes the tail IH
vacuous, as documented in inductionHypothesesOfOriginal. No target run or
strengthened IH is introduced. Source comparison retains all quantifiers and
conclusions of the motive5719–5751 and the original handler proof9020–10048;
canonical five fmap fields and positive type-indexed words are the only
carrier translations. Inherited evaluator real-carrier assurance limits apply. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectCallReturningHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (original :
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      Seq.Simulation ac retHandler (WordSemStateFiniteExact.setVars n ys s1)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ (some (handlerVar,handlerCode,h1,h2)) = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      Seq.Simulation ac h (WordSemStateFiniteExact.setVar n' y s2)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      Seq.Simulation ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))))) :
    Seq.Simulation ac (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) source :=
  returningHandlerCase ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source
    (inductionHypothesesOfOriginal ac values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source original)

end Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
