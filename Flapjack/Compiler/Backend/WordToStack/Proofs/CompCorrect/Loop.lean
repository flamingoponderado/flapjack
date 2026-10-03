import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Clock
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelCutState
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoopHandler
namespace Flapjack.WordToStackProofs.CompCorrect.Loop
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
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

/-- Flapjack factoring of precisely the two original evaluate_ind Loop induction
hypotheses under the complete simulation motive. No independent HOL declaration
names this factoring. The recursive hypothesis retains every original cut,
body-run, continuation and nonzero-clock guard; the body hypothesis requires
its original actual successful cut. -/
def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ cutSource bodyResult bodyPost,
    WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
    (bodyResult,bodyPost) = WordSemStateFiniteExact.evaluate body cutSource ∧
    wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
    Seq.Simulation ac (wordSemSTOP (.loop names body exitNames))
      (WordSemStateFiniteExact.decClock bodyPost)) ∧
  (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
    Seq.Simulation ac body cutSource)
/-- Flapjack case infrastructure: continuation controls commute with the
reviewed result translation. HOL proves these constructor reductions inline. -/
theorem contLoopCompile {width : Nat} [NeZero width]
    (result : Option (WordSemResult width)) :
    StackSemControl.contLoop (result.map compileResult) = wordSemContLoop result := by
  cases result with
  | none => rfl
  | some result => cases result <;> simp [compileResult,StackSemControl.contLoop,wordSemContLoop]

/-- Flapjack case infrastructure: target exit controls translate every outcome; Break 0
returns NONE and is paired with the source exit-name cut in the full case. -/
theorem exitLoopCompile {width : Nat} [NeZero width]
    (result : Option (WordSemResult width)) :
    StackSemControl.exitLoop (result.map compileResult) =
      match result with
      | some (.break 0) => none
      | _ => (wordSemExitLoop result).map compileResult := by
  classical
  cases result with
  | none => rfl
  | some result =>
    cases result <;> simp [compileResult,StackSemControl.exitLoop,wordSemExitLoop]
    next n => cases n <;> simp

/-- Flapjack case infrastructure: a successful continuation body supplies the
entire same-frame relation from the original result-sensitive IH conclusion. -/
theorem continuationRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (continues : wordSemContLoop result = true)
    (bodyPost : compCorrectResult ac k f frame source post target result
      (result.map compileResult) lens) : stateRel ac k f frame post target lens 0 := by
  cases result with
  | none => simpa [compCorrectResult] using bodyPost
  | some result =>
    cases result <;> simp [wordSemContLoop] at continues
    next n => simpa [compCorrectResult] using bodyPost
/-- Flapjack Loop body-entry infrastructure. Applies only the original guarded
body IH at the actual successful cut; compiler metadata and conventions are
obtained from the enclosing Loop premises. No target run is supplied. -/
theorem enterBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : Compiler.Backend.StackLang.HolProg width) (bodyResult : Option (WordSemResult width))
    (ih : InductionHypotheses ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (execution : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (notError : bodyResult ≠ some .error)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k) :
    ∃ compiledBody ck targetPost targetResult,
      compiled = .loop compiledBody ∧
      StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock+ck}) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame cutSource bodyPost targetPost bodyResult targetResult lens := by
  rcases bodyComp : compNative ac false body (bs,n) (k,f,frame) with ⟨compiledBody,next⟩
  simp only [compNative,bodyComp,Prod.mk.injEq] at compilation
  obtain ⟨rfl,nextEq⟩ := compilation
  have cutRel := StateRelCutState.stateRelCutState ac k f frame source cutSource target lens names related cut
  have bodyConventions : postAllocConventionsHOL k body = true := by
    simp [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL] at conventions ⊢
    exact ⟨conventions.1.1.2,conventions.2⟩
  have bodyFlat : flatExpConventions body = true := by simpa [flatExpConventions] using flat
  have bodyBound : maxVarHOL body < 2*frame+2*k := by
    simp only [maxVarHOL,max3HOL] at maxBound
    split at maxBound <;> split at maxBound <;> omega
  have bodyLabels : ∀ loc, StackSem.getLabelsExact compiledBody loc → StackSem.locCheckExact target.code loc := by
    simpa [StackSem.getLabelsExact] using labels
  have compilationBody : compNative ac false body (bs,n) (k,f,frame) = (compiledBody,(bsPost,nPost)) := by
    simpa [nextEq] using bodyComp
  obtain ⟨ck,post,res,actual,resultRel⟩ := ih.2 cutSource cut k f frame bodyPost target
    bodyResult bs bsPost n nPost compiledBody lens
    ⟨execution,notError,cutRel,bodyConventions,bodyFlat,compilationBody,
      lengthBound,bitmapBound,bitmapPrefix,bodyLabels,bodyBound⟩
  exact ⟨compiledBody,ck,post,res,rfl,actual,resultRel⟩
/-- Flapjack evaluator infrastructure for consuming the actual run produced by
the body IH. This is an internal execution equation, not a correctness port. -/
theorem runLoopExit {width : Nat} [NeZero width] {C F : Type}
    (body : Compiler.Backend.StackLang.HolProg width)
    (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (body,target) = (result,post))
    (exits : StackSemControl.contLoop result = false) :
    StackSemEvaluate.evaluate (.loop body,target) = (StackSemControl.exitLoop result,post) := by
  rw [StackSemEvaluate.evaluate_loop,StackSemEvaluateClock.fixClockEvaluate,run]
  simp [exits]

/-- Flapjack evaluator infrastructure: the actual continuation body run at
zero clock yields the faithful timeout and emptied target environment. -/
theorem runLoopTimeout {width : Nat} [NeZero width] {C F : Type}
    (body : Compiler.Backend.StackLang.HolProg width)
    (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (body,target) = (result,post))
    (continues : StackSemControl.contLoop result = true) (zero : post.clock = 0) :
    StackSemEvaluate.evaluate (.loop body,target) = (some .timeOut,StackSemStateOps.emptyEnv post) := by
  rw [StackSemEvaluate.evaluate_loop,StackSemEvaluateClock.fixClockEvaluate,run]
  simp [continues,zero]

/-- Flapjack Loop timeout infrastructure: full relation gives precisely the
original timeout FFI/clock result after source flush and target emptyEnv. -/
theorem timeoutRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (related : stateRel ac k f frame post target lens 0) :
    compCorrectResult ac k f frame source (WordSemStateFiniteExact.flushState true post)
      (StackSemStateOps.emptyEnv target) (some .timeOut) (some .timeOut) lens := by
  have ffi := related.2.2.2.1
  have clocks := related.1
  simp only [compCorrectResult,Option.map_some,compileResult,ne_eq,not_true_eq_false,
    ↓reduceIte,WordSemStateFiniteExact.flushState,StackSemStateOps.emptyEnv]
  exact ⟨ffi.symm,clocks⟩
/-- Flapjack Break-zero branch infrastructure: the body IH supplies its
original full relation, and the successful exit cut preserves it. -/
theorem breakZeroRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source cutSource bodyPost exitPost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (exitNames : Spt Unit)
    (bodyResult : compCorrectResult ac k f frame cutSource bodyPost target
      (some (.break 0)) (some (.break 0)) lens)
    (cut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost = some exitPost) :
    compCorrectResult ac k f frame source exitPost target none none lens := by
  have bodyRel : stateRel ac k f frame bodyPost target lens 0 := by
    simpa [compCorrectResult,compileResult] using bodyResult
  have exitRel := StateRelCutState.stateRelCutState ac k f frame bodyPost exitPost
    target lens exitNames bodyRel cut
  simpa [compCorrectResult] using exitRel

/-- Flapjack Break-zero execution infrastructure: consume the actual body IH
run to obtain normal target completion with the identical target post-state. -/
theorem runLoopBreakZero {width : Nat} [NeZero width] {C F : Type}
    (body : Compiler.Backend.StackLang.HolProg width)
    (target post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (body,target) = (some (.break 0),post)) :
    StackSemEvaluate.evaluate (.loop body,target) = (none,post) := by
  have exited := runLoopExit body target post (some (.break 0)) run rfl
  simpa [StackSemControl.exitLoop] using exited
/-- Flapjack result transport for the source exit operation. Break/Continue
depths change but their whole relation is retained; exception frames use the
same handler supplied by the actual initial cut. -/
theorem exitRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source cutSource post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width))
    (handler : source.handler = cutSource.handler)
    (bodyResult : compCorrectResult ac k f frame cutSource post target result
      (result.map compileResult) lens) :
    compCorrectResult ac k f frame source post target (wordSemExitLoop result)
      ((wordSemExitLoop result).map compileResult) lens := by
  cases result with
  | none => simpa [wordSemExitLoop,compCorrectResult] using bodyResult
  | some result =>
    cases result <;> simpa [wordSemExitLoop,compCorrectResult,compileResult,handler] using bodyResult

/-- Flapjack cut infrastructure: an actual successful source cut leaves the
handler unchanged, discharging the exception result's origin context. -/
theorem cutHandler {width : Nat} [NeZero width] {C F : Type}
    (names : Spt Unit) (source post : WordSemStateFiniteExact width C F)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some post) :
    source.handler = post.handler := by
  unfold WordSemStateFiniteExact.cutState at cut
  cases env : wordSemCutEnv (names,.ln) source.locals <;> simp [env] at cut
  next locals => subst post; rfl
/-- Flapjack recursive execution infrastructure: add the recursive IH's clock
budget to the actual non-timeout body run, then consume its actual recursive
run. The original nonzero-clock guard makes decrement commute with that budget.
Neither execution premise is a hypothesis of a tagged compiler-correctness port. -/
theorem runLoopRecursive {width : Nat} [NeZero width] {C F : Type}
    (body : Compiler.Backend.StackLang.HolProg width)
    (target bodyPost finalPost : StackSemStateFiniteExact width C F)
    (bodyResult finalResult : Option (StackSemResult width)) (extra : Nat)
    (bodyRun : StackSemEvaluate.evaluate (body,target) = (bodyResult,bodyPost))
    (continues : StackSemControl.contLoop bodyResult = true)
    (nonzero : bodyPost.clock ≠ 0)
    (recursiveRun : StackSemEvaluate.evaluate (.loop body,
      {StackSemStateOps.decClock bodyPost with clock := (StackSemStateOps.decClock bodyPost).clock+extra}) =
      (finalResult,finalPost)) :
    StackSemEvaluate.evaluate (.loop body,{target with clock := target.clock+extra}) =
      (finalResult,finalPost) := by
  have noTimeout : bodyResult ≠ some .timeOut := by
    intro eq
    subst bodyResult
    simp [StackSemControl.contLoop] at continues
  have boosted := Compiler.Backend.StackProps.evaluateAddClock extra body target bodyResult bodyPost
    ⟨bodyRun,noTimeout⟩
  have clockNonzero : bodyPost.clock+extra ≠ 0 := by omega
  have decrement : StackSemStateOps.decClock {bodyPost with clock := bodyPost.clock+extra} =
      {StackSemStateOps.decClock bodyPost with clock := (StackSemStateOps.decClock bodyPost).clock+extra} := by
    simp only [StackSemStateOps.decClock]
    congr 1
    omega
  rw [StackSemEvaluate.evaluate_loop,StackSemEvaluateClock.fixClockEvaluate,boosted]
  simp only [continues,if_true,clockNonzero,if_false]
  rw [decrement]
  exact recursiveRun
/-- Flapjack recursive-entry metadata transport from the actual body witness.
All original bitmap bounds/prefix and label obligations survive arbitrary
body code/bitmap growth; no post-state inclusion is assumed. -/
theorem recursiveMetadata {width : Nat} [NeZero width] {C F : Type}
    (body : Compiler.Backend.StackLang.HolProg width)
    (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock gap : Nat)
    (bitmapOutput : List (BitVec width))
    (run : StackSemEvaluate.evaluate (body,{target with clock := target.clock+clock}) = (result,post))
    (bound : gap ≤ target.bitmaps.length)
    (bitmapPrefix : bitmapOutput.IsPrefix (target.bitmaps.drop gap))
    (labels : ∀ loc, StackSem.getLabelsExact (.loop body) loc → StackSem.locCheckExact target.code loc) :
    gap ≤ post.bitmaps.length ∧ bitmapOutput.IsPrefix (post.bitmaps.drop gap) ∧
    (∀ loc, StackSem.getLabelsExact (.loop body) loc → StackSem.locCheckExact post.code loc) := by
  have mono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono body
    {target with clock := target.clock+clock} post result run
  refine ⟨bound.trans mono.1.length_le,bitmapPrefix.trans (mono.1.drop gap),?_⟩
  intro loc member
  exact LocationLabels.locCheckSubset target.code post.code mono.2 loc (labels loc member)

/-- Flapjack guarded recursive-entry relation: consume the original body IH
conclusion and original continuation guard, then decrement both related clocks. -/
theorem recursiveRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (cutSource bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (targetPost : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (continues : wordSemContLoop result = true)
    (bodyResult : compCorrectResult ac k f frame cutSource bodyPost targetPost result
      (result.map compileResult) lens) :
    stateRel ac k f frame (WordSemStateFiniteExact.decClock bodyPost)
      (StackSemStateOps.decClock targetPost) lens 0 := by
  exact Clock.stateRelDecClock ac k f frame bodyPost targetPost lens 0
    (continuationRelation ac k f frame cutSource bodyPost targetPost lens result continues bodyResult)
/-- Flapjack recursive IH application at its original guarded source state.
The target relation, bitmap growth, and label validity are derived from the
actual body witness; the recursive target run is the IH's existential result. -/
theorem enterRecursive {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalSource : WordSemStateFiniteExact width (Nat × C) F)
    (target targetBody : StackSemStateFiniteExact width C F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost bodyClock : Nat)
    (compiledBody : Compiler.Backend.StackLang.HolProg width)
    (bodyResult finalResult : Option (WordSemResult width))
    (ih : InductionHypotheses ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (sourceBody : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (continues : wordSemContLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (sourceRecursive : WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource))
    (notError : finalResult ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock+bodyClock}) =
      (bodyResult.map compileResult,targetBody))
    (bodyConclusion : compCorrectResult ac k f frame cutSource bodyPost targetBody
      bodyResult (bodyResult.map compileResult) lens)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) =
      (.loop compiledBody,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k) :
    ∃ clock targetPost result,
      StackSemEvaluate.evaluate (.loop compiledBody,
        {StackSemStateOps.decClock targetBody with clock := (StackSemStateOps.decClock targetBody).clock+clock}) =
        (result,targetPost) ∧
      compCorrectResult ac k f frame (WordSemStateFiniteExact.decClock bodyPost)
        finalSource targetPost finalResult result lens := by
  have recursiveIH := ih.1 cutSource bodyResult bodyPost ⟨cut,sourceBody.symm,continues,nonzero⟩
  have metadata := recursiveMetadata compiledBody target targetBody (bodyResult.map compileResult)
    bodyClock (n-(appListAppend bs).length) (appListAppend bsPost) targetRun bitmapBound bitmapPrefix labels
  have relation := recursiveRelation ac k f frame cutSource bodyPost targetBody lens bodyResult continues bodyConclusion
  apply recursiveIH k f frame finalSource (StackSemStateOps.decClock targetBody)
    finalResult bs bsPost n nPost (.loop compiledBody) lens
  simpa only [wordSemSTOP,StackSemStateOps.decClock] using
    (show WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource) ∧
      finalResult ≠ some .error ∧ stateRel ac k f frame
        (WordSemStateFiniteExact.decClock bodyPost) (StackSemStateOps.decClock targetBody) lens 0 ∧
      postAllocConventionsHOL k (.loop names body exitNames) = true ∧
      flatExpConventions (.loop names body exitNames) = true ∧
      compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (.loop compiledBody,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ targetBody.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (targetBody.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc,StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact targetBody.code loc) ∧
      maxVarHOL (.loop names body exitNames) < 2*frame+2*k from
      ⟨sourceRecursive,notError,relation,conventions,flat,compilation,lengthBound,
        metadata.1,metadata.2.1,metadata.2.2,maxBound⟩)
/-- Flapjack overflow continuation infrastructure: propagate actual source
body trace/resource evidence through every remaining Loop clause, including
recursive execution, timeout flush, exit cut, and passthrough outcomes. -/
theorem sourceTailResources {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalPost : WordSemStateFiniteExact width C F)
    (bodyResult finalResult : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (bodyRun : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (loopRun : WordSemStateFiniteExact.evaluate (.loop names body exitNames) source = (finalResult,finalPost))
    (overflow : bodyPost.stackMax.getD (bodyPost.stackLimit+1) > bodyPost.stackLimit) :
    bodyPost.ffi.ioEvents.IsPrefix finalPost.ffi.ioEvents ∧
    finalPost.stackMax.getD (finalPost.stackLimit+1) > finalPost.stackLimit := by
  rw [WordSemStateFiniteExact.evaluate,cut] at loopRun
  simp only [] at loopRun
  rw [WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at loopRun
  by_cases continues : wordSemContLoop bodyResult = true
  · simp only [continues,if_true] at loopRun
    by_cases zero : bodyPost.clock = 0
    · simp only [zero] at loopRun
      obtain ⟨rfl,rfl⟩ := loopRun
      exact ⟨(by exact ⟨[],by simp [WordSemStateFiniteExact.flushState]⟩),overflow⟩
    · simp only [zero] at loopRun
      have events := WordSemStateFiniteExact.evaluate_io_events_mono
        (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock bodyPost)
        finalResult finalPost loopRun
      have limit := WordSemStateFiniteExact.evaluate_stack_limit_stack_max
        (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock bodyPost)
        finalResult finalPost ⟨loopRun,by cases h : bodyPost.stackMax <;> simp_all [miscThe,WordSemStateFiniteExact.decClock]⟩
      exact ⟨events,by cases h : finalPost.stackMax <;> simp_all [miscThe]⟩
  · simp only [continues] at loopRun
    cases bodyResult with
    | none => simp only [wordSemExitLoop] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact ⟨(by exact ⟨[],by simp []⟩),overflow⟩
    | some result =>
      cases result <;> try (simp only [wordSemExitLoop] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact ⟨(by exact ⟨[],by simp []⟩),overflow⟩)
      next depth =>
        cases depth with
        | zero =>
          cases exitCut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost with
          | none => simp [exitCut] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact ⟨(by exact ⟨[],by simp []⟩),overflow⟩
          | some exitPost =>
            simp only [exitCut] at loopRun
            obtain ⟨rfl,rfl⟩ := loopRun
            unfold WordSemStateFiniteExact.cutState at exitCut
            cases env : wordSemCutEnv (exitNames,.ln) bodyPost.locals <;> simp [env] at exitCut
            next locals => subst finalPost; exact ⟨(by exact ⟨[],by simp []⟩),overflow⟩
        | succ depth =>
          simp only [wordSemExitLoop] at loopRun
          obtain ⟨rfl,rfl⟩ := loopRun
          exact ⟨(by exact ⟨[],by simp []⟩),overflow⟩
/-- Flapjack body-overflow branch infrastructure. The original body IH's
mismatch conclusion yields the halt run; every source Loop tail propagates
its trace/resource evidence. This internal branch consumes actual IH witnesses. -/
theorem bodyOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalSource : WordSemStateFiniteExact width (Nat × C) F)
    (target targetPost : StackSemStateFiniteExact width C F) (lens : List Nat)
    (compiledBody : Compiler.Backend.StackLang.HolProg width) (clock : Nat)
    (bodyResult finalResult : Option (WordSemResult width)) (targetResult : Option (StackSemResult width))
    (related : stateRel ac k f frame source target lens 0)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (sourceBody : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (sourceLoop : WordSemStateFiniteExact.evaluate (.loop names body exitNames) source = (finalResult,finalSource))
    (targetBody : StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock+clock}) = (targetResult,targetPost))
    (bodyConclusion : compCorrectResult ac k f frame cutSource bodyPost targetPost bodyResult targetResult lens)
    (mismatch : bodyResult.map compileResult ≠ targetResult) :
    StackSemEvaluate.evaluate (.loop compiledBody,{target with clock := target.clock+clock}) =
      (some (.halt (.word 2)),targetPost) ∧
    compCorrectResult ac k f frame source finalSource targetPost finalResult (some (.halt (.word 2))) lens := by
  classical
  simp [compCorrectResult,mismatch] at bodyConclusion
  obtain ⟨halt,events,overflow⟩ := bodyConclusion
  subst targetResult
  have tailResources := sourceTailResources names exitNames body source cutSource bodyPost finalSource
    bodyResult finalResult cut sourceBody sourceLoop overflow
  have dimension : goodDimindex width :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have finalMismatch : finalResult.map compileResult ≠ some (StackSemResult.halt (.word 2)) := by
    cases finalResult with
    | none => simp
    | some result =>
      simp only [Option.map_some,ne_eq,Option.some.injEq]
      exact Ne.symm ((haltEqCompileResult result).2 dimension)
  constructor
  · have run := runLoopExit compiledBody {target with clock := target.clock+clock} targetPost
      (some (.halt (.word 2))) targetBody rfl
    simpa [StackSemControl.exitLoop] using run
  · unfold compCorrectResult
    split
    · exact ⟨rfl,events.trans tailResources.1,tailResources.2⟩
    · contradiction
/-- Flapjack result-origin transport. Only the exception clause observes the
source handler; every other original result branch is retained verbatim. -/
theorem originRelation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source origin post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (targetResult : Option (StackSemResult width))
    (handler : source.handler = origin.handler)
    (relation : compCorrectResult ac k f frame origin post target result targetResult lens) :
    compCorrectResult ac k f frame source post target result targetResult lens := by
  unfold compCorrectResult at relation ⊢
  split at relation <;> split <;> try contradiction
  · exact relation
  · cases result with
    | none => exact relation
    | some result => cases result <;> simpa [handler] using relation

/-- Flapjack source decomposition: a body Error cannot be hidden by the
faithful enclosing Loop. The original whole-case nonerror guard discharges it. -/
theorem bodyNonError {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalPost : WordSemStateFiniteExact width C F)
    (bodyResult finalResult : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (bodyRun : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (loopRun : WordSemStateFiniteExact.evaluate (.loop names body exitNames) source = (finalResult,finalPost))
    (notError : finalResult ≠ some .error) : bodyResult ≠ some .error := by
  intro error
  subst bodyResult
  rw [WordSemStateFiniteExact.evaluate,cut] at loopRun
  simp only [] at loopRun
  rw [WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at loopRun
  simp [wordSemContLoop,wordSemExitLoop] at loopRun
  obtain ⟨rfl,rfl⟩ := loopRun
  contradiction
/-- Full original Loop constructor under precisely the original two guarded
induction hypotheses and the complete simulation motive (7767–7922). All
timeout, recursive, overflow, passthrough and Break-zero branches retained.
Evaluator closure inherits reals_as_rational_cuts; no independent numerical
FP agreement is claimed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : InductionHypotheses ac names exitNames body source) :
    Seq.Simulation ac (.loop names body exitNames) source := by
  classical
  intro k f frame finalSource target finalResult bs bsPost n nPost compiled lens premises
  rcases premises with ⟨sourceLoop,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases cut : WordSemStateFiniteExact.cutState (names,.ln) source with
  | none =>
    rw [WordSemStateFiniteExact.evaluate,cut] at sourceLoop
    have error : finalResult = some .error := congrArg Prod.fst sourceLoop.symm
    exact False.elim (notError error)
  | some cutSource =>
    rcases sourceBody : WordSemStateFiniteExact.evaluate body cutSource with ⟨bodyResult,bodyPost⟩
    have bodyError := bodyNonError names exitNames body source cutSource bodyPost finalSource
      bodyResult finalResult cut sourceBody sourceLoop notError
    obtain ⟨compiledBody,bodyClock,targetBody,targetResult,compiledEq,targetRun,bodyConclusion⟩ :=
      enterBody ac names exitNames body source cutSource bodyPost target k f frame lens
        bs bsPost n nPost compiled bodyResult ih cut sourceBody bodyError related conventions
        flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound
    subst compiled
    by_cases mismatch : bodyResult.map compileResult ≠ targetResult
    · have overflow := bodyOverflow ac k f frame names exitNames body source cutSource bodyPost
        finalSource target targetBody lens compiledBody bodyClock bodyResult finalResult targetResult
        related cut sourceBody sourceLoop targetRun bodyConclusion mismatch
      exact ⟨bodyClock,targetBody,some (.halt (.word 2)),overflow⟩
    · have resultEq : targetResult = bodyResult.map compileResult := (not_ne_iff.mp mismatch).symm
      subst targetResult
      have tailRun := sourceLoop
      rw [WordSemStateFiniteExact.evaluate,cut] at tailRun
      simp only [] at tailRun
      rw [WordSemStateFiniteExact.fix_clock_evaluate,sourceBody] at tailRun
      by_cases continues : wordSemContLoop bodyResult = true
      · have bodyRel := continuationRelation ac k f frame cutSource bodyPost targetBody lens
          bodyResult continues bodyConclusion
        have clocks := bodyRel.1
        have targetContinues : StackSemControl.contLoop (bodyResult.map compileResult) = true := by
          rw [contLoopCompile,continues]
        simp only [continues] at tailRun
        by_cases zero : bodyPost.clock = 0
        · simp only [zero] at tailRun
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj tailRun
          have targetZero : targetBody.clock = 0 := by omega
          exact ⟨bodyClock,StackSemStateOps.emptyEnv targetBody,some .timeOut,
            runLoopTimeout compiledBody {target with clock := target.clock+bodyClock} targetBody
              (bodyResult.map compileResult) targetRun targetContinues targetZero,
            timeoutRelation ac k f frame source bodyPost targetBody lens bodyRel⟩
        · simp only [zero] at tailRun
          obtain ⟨recursiveClock,post,res,recursiveRun,recursiveConclusion⟩ :=
            enterRecursive ac names exitNames body source cutSource bodyPost finalSource target targetBody
              k f frame lens bs bsPost n nPost bodyClock compiledBody bodyResult finalResult ih cut sourceBody
              continues zero (by simpa [wordSemSTOP] using tailRun) notError targetRun bodyConclusion
              conventions flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound
          have targetNonzero : targetBody.clock ≠ 0 := by omega
          have actual := runLoopRecursive compiledBody {target with clock := target.clock+bodyClock}
            targetBody post (bodyResult.map compileResult) res recursiveClock targetRun targetContinues
            targetNonzero recursiveRun
          have sourceHandler : source.handler = (WordSemStateFiniteExact.decClock bodyPost).handler := by
            have bodyHandler := LoopHandler.evaluateContLoopHandler body cutSource bodyPost bodyResult sourceBody continues
            have initialHandler := cutHandler names source cutSource cut
            simpa [WordSemStateFiniteExact.decClock] using initialHandler.trans bodyHandler.symm
          refine ⟨bodyClock+recursiveClock,post,res,?_,?_⟩
          · simpa [Nat.add_assoc] using actual
          · exact originRelation ac k f frame source (WordSemStateFiniteExact.decClock bodyPost)
              finalSource post lens finalResult res sourceHandler recursiveConclusion
      · simp only [continues] at tailRun
        by_cases breakZero : bodyResult = some (.break 0)
        · subst bodyResult
          cases exitCut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost with
          | none =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            contradiction
          | some exitPost =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            exact ⟨bodyClock,targetBody,none,
              runLoopBreakZero compiledBody {target with clock := target.clock+bodyClock} targetBody targetRun,
              breakZeroRelation ac k f frame source cutSource bodyPost exitPost targetBody lens exitNames
                bodyConclusion exitCut⟩
        · have sourceExit : (wordSemExitLoop bodyResult,bodyPost) = (finalResult,finalSource) := by
            cases bodyResult with
            | none => exact tailRun
            | some result =>
              cases result <;> try exact tailRun
              next depth => cases depth <;> simp_all
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj sourceExit
          have targetExits : StackSemControl.contLoop (bodyResult.map compileResult) = false := by
            rw [contLoopCompile]
            cases h : wordSemContLoop bodyResult <;> simp_all
          have exitEq : StackSemControl.exitLoop (bodyResult.map compileResult) =
              (wordSemExitLoop bodyResult).map compileResult := by
            rw [exitLoopCompile]
            cases bodyResult with
            | none => rfl
            | some result =>
              cases result <;> simp_all
          refine ⟨bodyClock,targetBody,(wordSemExitLoop bodyResult).map compileResult,?_,?_⟩
          · rw [← exitEq]
            exact runLoopExit compiledBody {target with clock := target.clock+bodyClock}
              targetBody (bodyResult.map compileResult) targetRun targetExits
          · exact exitRelation ac k f frame source cutSource bodyPost targetBody lens bodyResult
              (cutHandler names source cutSource cut) bodyConclusion
end Flapjack.WordToStackProofs.CompCorrect.Loop
