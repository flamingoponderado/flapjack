import Flapjack.Compiler.Backend.StackProps.EvaluateConsts
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnHandler
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnStackMoveClock

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open CallReturnHandler

/-- The three original evaluate_ind hypotheses for the returning-handler
case, at their actual guarded source states. Normal continuation requires
callee Result/location/length/pop_env/domain guards; exception continuation
requires callee Exception/location/domain guards; callee entry requires the
actual get/find/cut guards and nonzero source clock. No target run, postrelation
or stronger universally quantified context is assumed. There is no separate
HOL declaration for this Flapjack grouping of the induction hypotheses. -/
def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values ys popped)) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location value : WordLocW width)
    (calleePost : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),calleePost) ∧
    ¬ location ≠ .loc h1 h2 ∧
    sptDomainEqUnion calleePost.locals envs.1 envs.2 →
    Seq.Simulation ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost)) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    Seq.Simulation ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))))

/-- The grouped handler hypotheses follow from the literal three returning
Call hypotheses of evaluate_ind. Intermediate product/evaluation-result
binders are instantiated by their actual tuples. The fourth tail-call IH is
vacuous for this fixed SOME return descriptor and is omitted. This kernel
translation confirms that the grouping introduces no stronger source IH;
it is Flapjack infrastructure, not a separate HOL declaration. -/
theorem inductionHypothesesOfOriginal {width : Nat} [NeZero width] {C F : Type}
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
    InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
      source := by
  refine ⟨?_,?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,pop,domain⟩
    exact original.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs (some (.result location ys)) calleePost
      (.result location ys) location ys popped
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,checked,pop,domain⟩
  · intro xs args1 prog ss envs location value calleePost facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,domain⟩
    exact original.2.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs (some (.exception location value)) calleePost
      (.exception location value) location value (handlerVar,handlerCode,h1,h2)
      handlerVar (handlerCode,h1,h2) handlerCode (h1,h2) h1 h2
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,rfl,rfl,
        rfl,rfl,by simpa only [not_ne_iff] using checked,domain⟩
  · intro xs args1 prog ss envs facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock⟩
    exact original.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock⟩

/-- Handler-case source guard elimination from the actual non-error source run.
The guards precede handler selection in the original evaluator. This is
Flapjack infrastructure, with no separate HOL declaration or target-run premise. -/
theorem sourceGuardsOfNotErrorWithHandler {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args handler) source =
      (result, sourcePost)) (notError : result ≠ some .error) :
    ∃ xs args1 prog ss envs,
      CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs := by
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hget : WordSemStateFiniteExact.getVars args source with _ | xs
  · simp only [hget, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hget] at execution
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hbad, Bool.false_eq_true, if_false] at execution
  rcases hfind : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs)
      source.code source.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hfind, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hfind] at execution
  by_cases invalid : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [invalid, if_true, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [invalid, if_false] at execution
  rcases hcut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [hcut, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  exact ⟨xs, args1, prog, ss, envs, hget, hbad, hfind, invalid, hcut⟩

/-- Removing the exception continuation preserves all returning-call
conventions. This is Flapjack factoring of the original setup checks, not a
new HOL theorem or a strengthened simulation premise. -/
theorem conventionsWithoutHandler {width : Nat} [NeZero width]
    (k : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args handler) = true) :
    postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true := by
  cases handler with
  | none => exact conventions
  | some handler =>
    rcases handler with ⟨handlerVar, body, h1, h2⟩
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true, Bool.and_true] at conventions ⊢
    aesop (config := { enableSimp := false })

/-- The original handler call conventions force the exception handlerVar to
register two and establish the handler body's conventions. This support has
no separate HOL original and does not assume a restored target relation. -/
theorem handlerConventions {width : Nat} [NeZero width]
    (k : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args
        (some (handlerVar, handlerCode, h1, h2))) = true) :
    handlerVar = 2 ∧ postAllocConventionsHOL k handlerCode = true := by
  simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
    callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at conventions
  simp only [postAllocConventionsHOL, Bool.and_eq_true]
  aesop (config := { enableSimp := false })

/-- The caller maximum remains valid when the handler continuation is
removed for the shared setup lemmas. This follows the literal max_var call
clause and has no separate HOL original. -/
theorem maximumWithoutHandler {width : Nat} [NeZero width]
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args none) ≤
      maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args handler) := by
  cases handler with
  | none => exact Nat.le_refl _
  | some handler =>
    rcases handler with ⟨handlerVar, body, h1, h2⟩
    simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq]
    omega

/-- Actual destination and saved-frame prelude for a returning handler call,
using the original handler-call conventions and maximum. The shared setup
executes before PushHandler; its temporary no-handler source frame is the
actual evaluate_wLive relation. This is Flapjack case infrastructure, not
an assembled comp_correct theorem or a supplied target run. -/
theorem evaluateHandlerPrelude {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
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
      (.call (some (values, names, retCode, l1, l2)) dest args handler) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args handler) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ savedTarget : StackSemStateFiniteExact width C F,
      (∀ extra : Nat,
        StackSemEvaluate.evaluate (.seq destinationCode savedCode,
          {target with clock := target.clock + extra}) =
          (none, {savedTarget with clock := savedTarget.clock + extra})) ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with
          locals := .ln, localsSize := some 0}
        savedTarget (frame :: lens) 0 ∧
      stateRel ac k f frame source savedTarget lens 0 ∧
      savedTarget.stack.length = target.stack.length ∧
      savedTarget.stackSpace = target.stackSpace := by
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2
    dest args handler conventions
  have plainMaximum := lt_of_le_of_lt
    (maximumWithoutHandler values names retCode l1 l2 dest args handler) maximum
  exact CallReturning.evaluatePrelude ac k f frame values names retCode l1 l2 dest args
    source target lens xs args1 prog ss envs bs savedBitmaps finalBitmaps n savedIndex
    finalIndex destinationCode savedCode returnCode destination guards related
    plainConventions plainMaximum destinationCompile savedCompile returnCompile
    lengthBound bitmapBound bitmapPrefix

/-- Execute the real returning-handler header after destination and saved
frame setup, deriving its final full state relation from evaluate_PushHandler.
The initial room and label guards are the original successful header branch;
no intermediate target execution or final relation is assumed. This is
Flapjack case infrastructure, not the whole comp_correct theorem. -/
theorem evaluateHandlerHeader {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
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
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2)) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate
        (.seq (.seq destinationCode savedCode) (pushHandlerNative false h1 h2 (k,f,frame)),
          target) = (none, post) ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source
          with locals := .ln, localsSize := some 0}
        post (frame :: lens) 0 ∧
      post.stackSpace + 3 = target.stackSpace ∧
      post.stack.length = target.stack.length := by
  obtain ⟨savedTarget, savedClockRun, savedRelation, _, savedLength, savedSpace⟩ :=
    evaluateHandlerPrelude ac k f frame values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) source target lens xs args1 prog ss envs
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode destination guards related conventions maximum destinationCompile
      savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  have savedRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, savedTarget) := by simpa using savedClockRun 0
  have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.seq destinationCode savedCode) target savedTarget none savedRun
  have savedLocation := LocationLabels.locCheckSubset target.code savedTarget.code
    mono.2 (h1,h2) location
  obtain ⟨post, pushRun, _, _, _, postSpace, postLength, postRelation⟩ :=
    evaluatePushHandler ac k f frame h1 h2 handlerVar handlerCode source savedTarget
      envs lens (by rw [savedSpace]; exact room) savedRelation savedLocation
  refine ⟨post, ?_, postRelation, postSpace.trans savedSpace, postLength.trans savedLength⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
  exact pushRun

/-- The real insufficient-header-room branch halts with word two and
preserves the original FFI state. This proves the target resource failure from
source-derived setup, not an assumed run; the source stack-limit consequence
and full comp_correct resource conclusion remain separate open obligations.
There is no separate HOL declaration for this case factoring. -/
theorem evaluateHandlerHeaderNoRoom {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
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
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (noRoom : target.stackSpace < 3) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate
        (.seq (.seq destinationCode savedCode) (pushHandlerNative false h1 h2 (k,f,frame)),
          target) = (some (.halt (.word (BitVec.ofNat width 2))), post) ∧
      post.ffi = source.ffi := by
  obtain ⟨savedTarget, savedClockRun, savedRelation, _, _, savedSpace⟩ :=
    evaluateHandlerPrelude ac k f frame values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) source target lens xs args1 prog ss envs
      bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode destination guards related conventions maximum destinationCompile
      savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  have savedRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, savedTarget) := by simpa using savedClockRun 0
  have savedEnabled : savedTarget.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have savedFfi : savedTarget.ffi = source.ffi := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have short : savedTarget.stackSpace < 3 := by rw [savedSpace]; exact noRoom
  refine ⟨StackSemStateOps.emptyEnv savedTarget, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    simp only [pushHandlerF, StackSemEvaluate.evaluate_seq,
      StackSemEvaluate.evaluate_stackAlloc,
      savedEnabled, Bool.not_true, Bool.false_eq_true, if_false, short, if_true, StackSemControl.fixClock, StackSemStateOps.emptyEnv, Nat.min_self]
  · simpa only [StackSemStateOps.emptyEnv] using savedFfi

/-- Source stack-limit overflow corresponding to insufficient room for
three handler words. The original stack_size_rel supplies the occupied size;
no source or target outcome is assumed. This is Flapjack factoring of the
resource argument at original lines9038+, not a separate HOL declaration. -/
theorem handlerNoRoomSourceLimit {width : Nat} [NeZero width] {C F α : Type}
    (source : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (args : List (WordLocW width)) (size : Option Nat)
    (frame space : Nat) (stack : List α)
    (relation : stackSizeRel frame source.localsSize source.stackLimit source.stackMax
      source.stack stack space 0)
    (positive : 0 < frame) (bound : space + frame ≤ stack.length)
    (short : space < 3) :
    source.stackLimit <
      (WordSemStateFiniteExact.callEnv args size
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          source)).stackMax.getD (source.stackLimit + 1) := by
  obtain ⟨localSize, limit, maximum⟩ := relation
  cases oldMax : source.stackMax with
  | none =>
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      oldMax, wordSemOptionMax]
  | some old =>
    obtain ⟨_, localsSome, occupied, occupiedEq, occupiedSize⟩ := maximum old oldMax
    cases localsEq : source.localsSize with
    | none => simp [localsEq] at localsSome
    | some localCount =>
      have localFrame := localSize (by omega)
      simp only [localsEq, Option.getD_some] at localFrame
      have localsExact : source.localsSize = some frame := by
        rw [localsEq, localFrame]
      have frameSize : wordSemStackSize
          (.stackFrame source.localsSize (sptToAList envs.1)
            (wordSemEnvToList envs.2 source.permute).1 (some (source.handler,h1,h2)) ::
              source.stack) = some (3 + frame + occupied) := by
        change wordSemOptionAdd (wordSemStackSizeFrame _) (wordSemStackSize source.stack) = _
        simp only [wordSemStackSizeFrame, localsExact, Option.map_some, occupiedEq,
          wordSemOptionAdd]
      cases size with
      | none =>
        simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          wordSemOptionAdd, wordSemOptionMax]
      | some size =>
        simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
          frameSize, oldMax,
          wordSemOptionAdd, wordSemOptionMax, Option.getD_some]
        omega

/-- Handler-case argument-local construction after the actual three-word
header. The caller relation is retained on the pre-header state; copied
arguments are observed at the actual lowered header space. This factors the
original handler branch's local argument proof and has no separate HOL
original. The move observations are primitive register/slot facts, not an
assumed callee or post-state relation. -/
theorem handlerCalleeLocals {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved moved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k callerSize callerFrame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (headerSpace : Nat) (headerSpaceEq : headerSpace + 3 = saved.stackSpace)
    (space : calleeSize ≤ headerSpace)
    (registers : ∀ register, register ≠ k →
      StackSemStateOps.getVar register moved = StackSemStateOps.getVar register saved)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (moved.stack.drop (headerSpace - (args1.length - k))))
    (movedLength : moved.stack.length = saved.stack.length) :
    ∀ key value, sptLookup key (sptFromList2 args1) = some value →
      key % 2 = 0 ∧
      if key / 2 < k then (moved.regs.updateEq (0, .loc l1 l2)).lookup (key / 2) = some value
      else ((moved.stack.drop (headerSpace - calleeSize)).take calleeSize)[calleeSize - 1 - (key / 2 - k)]? = some value ∧ key / 2 < k + calleeFrame := by
  obtain ⟨get, _, find, _, _⟩ := guards
  obtain ⟨_, _, _, indirect, direct⟩ := CallTail.findCode_facts dest _
    source.code source.stackSize args1 prog ss find
  have argPrefix : args1.IsPrefix (.loc l1 l2 :: xs) := by
    cases dest with
    | none => rw [indirect rfl]; exact List.dropLast_prefix _
    | some p => rw [direct (by simp)]; exact List.prefix_refl _
  have argsEq := (CallReturning.returningConventions k values names retCode l1 l2 dest args conventions).2.1
  unfold stateRel at related
  obtain ⟨_, _, _, _, _, _, _, _, _, kPositive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, stackBound, _, callerShape, _, _, _, locals⟩ := related
  intro key value lookup
  have index : key / 2 < args1.length := by
    rw [fromList2Lookup] at lookup
    split at lookup
    · exact (List.getElem?_eq_some_iff.mp lookup).1
    · cases lookup
  have fullLookup := lookupFromList2Prefix args1 (.loc l1 l2 :: xs) key value argPrefix lookup
  have even : key % 2 = 0 := by
    rw [fromList2Lookup] at lookup
    split at lookup
    · assumption
    · cases lookup
  refine ⟨even, ?_⟩
  by_cases zero : key = 0
  · subst key
    have valueLoc : value = .loc l1 l2 := by
      simpa [fromList2Lookup] using fullLookup.symm
    rw [if_pos (by omega), valueLoc]
    simp [FUPDATE_HOL]
  have sourceLookup := getVarsFromList2EqCons args source xs key l1 l2 value
    (by rwa [← argsEq]) fullLookup zero
  obtain ⟨_, callerLocal⟩ := locals key value sourceLookup
  by_cases inRegister : key / 2 < k
  · rw [if_pos inRegister] at callerLocal ⊢
    have preserved := registers (key / 2) (by omega)
    simp only [StackSemStateOps.getVar] at preserved
    simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL]
    rw [if_neg (by omega), preserved]
    exact callerLocal
  · rw [if_neg inRegister] at callerLocal ⊢
    obtain ⟨callerSlot, callerIndex⟩ := callerLocal
    rw [if_neg (by omega)] at callerShape
    have calleePositive : 0 < calleeFrame := by omega
    rw [if_neg (by omega)] at calleeShape
    have countSpace : args1.length - k ≤ headerSpace := by omega
    have copyIndex : args1.length - k - 1 - (key / 2 - k) < args1.length - k := by omega
    have copied := slots _ copyIndex
    have callerAbsolute : saved.stackSpace + (callerSize - 1 - (key / 2 - k)) < saved.stack.length := by
      rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at callerSlot
      split at callerSlot
      · exact (List.getElem?_eq_some_iff.mp callerSlot).1
      · cases callerSlot
    have movedAbsolute : headerSpace - calleeSize +
        (calleeSize - 1 - (key / 2 - k)) < moved.stack.length := by omega
    refine ⟨?_, by omega⟩
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      List.getElem?_eq_getElem movedAbsolute]
    rw [Nat.add_zero, List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      List.getElem?_eq_getElem callerAbsolute] at callerSlot
    rw [holEl_eq_getElem _ _ (by simp; omega), holEl_eq_getElem _ _ (by simp; omega),
      List.getElem_drop, List.getElem_drop] at copied
    have sourceIndex : saved.stackSpace - (args1.length - k) +
        (args1.length - k - 1 - (key / 2 - k) + callerSize) =
        saved.stackSpace + (callerSize - 1 - (key / 2 - k)) := by omega
    have targetIndex : headerSpace - (args1.length - k) +
        (args1.length - k - 1 - (key / 2 - k)) =
        headerSpace - calleeSize + (calleeSize - 1 - (key / 2 - k)) := by omega
    simp only [sourceIndex, targetIndex] at copied
    rw [← copied]
    exact callerSlot

/-- Execute the real handler argument allocation/move and connect its
slots to the pre-header caller stack. Header writes lie below the occupied
caller slots. This supports the original handler callee entry; the target
move and its register/slot observations are proved, not supplied. There is
no separate HOL declaration for this case-local composition. -/
theorem evaluateHandlerArguments {width : Nat} [NeZero width] {C F : Type}
    (k f frame h1 h2 : Nat) (destination : Sum Nat Nat) (argCount : Nat)
    (saved : StackSemStateFiniteExact width C F) (savedHandler : WordLocW width)
    (useStack : saved.useStack = true) (room : 3 ≤ saved.stackSpace)
    (frameBound : saved.stackSpace + f ≤ saved.stack.length)
    (moveBound : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤ f)
    (space : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤
      (pushedHandlerState saved h1 h2 k savedHandler).stackSpace) :
    let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
    let header := pushedHandlerState saved h1 h2 k savedHandler
    ∃ (moved : StackSemStateFiniteExact width C F) (stack : List (WordLocW width))
      (regs : HolFiniteMapExact Nat (WordLocW width)),
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination argCount (k,f,frame), header) =
          (none, moved) ∧
      moved = {header with stackSpace := header.stackSpace-count, stack := stack, regs := regs} ∧
      (∀ register, register ≠ k → StackSemStateOps.getVar register moved =
        StackSemStateOps.getVar register saved) ∧
      moved.stack.length = saved.stack.length ∧
      moved.stackSpace = header.stackSpace - count ∧
      moved.stack.drop (moved.stackSpace + count) = header.stack.drop header.stackSpace ∧
      (∀ index, index < count →
        holEl (index + f) (saved.stack.drop (saved.stackSpace - count)) =
          holEl index (moved.stack.drop (header.stackSpace - count))) := by
  dsimp only
  let header := pushedHandlerState saved h1 h2 k savedHandler
  let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
  have resources := pushedHandlerStateResources saved h1 h2 k savedHandler room
  have headerLength : header.stack.length = saved.stack.length := resources.2.2
  have headerSpace : header.stackSpace + 3 = saved.stackSpace := resources.2.1
  obtain ⟨moved, stack, regs, run, movedState, registers, stackLength, movedSpace, tail, slots⟩ :=
    CallReturning.evaluateStackArguments k (f+3) (frame+3) destination argCount header
      useStack (by rw [headerLength]; omega)
      (by omega) space
  refine ⟨moved, stack, regs, ?_, movedState, ?_, ?_, movedSpace, ?_, ?_⟩
  · rw [stackHandlerArgsF]
    exact run
  · intro register distinct
    exact (registers register distinct).trans (resources.1 register distinct)
  · rw [movedState]
    change stack.length = saved.stack.length
    exact stackLength.symm.trans resources.2.2
  · simpa only [movedState] using tail
  · intro index indexBound
    have copied := slots index indexBound
    change holEl (index + (f+3)) (header.stack.drop (header.stackSpace - count)) =
      holEl index (stack.drop (header.stackSpace - count)) at copied
    rw [movedState]
    change holEl (index+f) (saved.stack.drop (saved.stackSpace-count)) =
      holEl index (stack.drop (header.stackSpace-count))
    rw [← copied, holElDrop, holElDrop]
    have absoluteEq : header.stackSpace-count+(index+(f+3)) =
        saved.stackSpace-count+(index+f) := by
      change saved.stackSpace-3-count+(index+(f+3)) = _
      omega
    rw [absoluteEq]
    have unchanged := congrArg (holEl (index+f-count))
      (pushedHandlerStateOccupiedSuffix saved h1 h2 k savedHandler room)
    rw [holElDrop, holElDrop] at unchanged
    have sameIndex : saved.stackSpace+(index+f-count) =
        saved.stackSpace-count+(index+f) := by omega
    rw [sameIndex] at unchanged
    exact unchanged.symm

/-- Full handler callee-entry state relation from the actual saved frame,
three-word PushHandler update and argument-move observations. The handler
frame is decoded by the already checked PushHandler relation; the local
argument conjunct uses the original pre-header caller. Every callee state
field is proved. This is Flapjack case infrastructure, not a whole
comp_correct port or an assumption of its target execution/result. -/
theorem handlerCalleeStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (savedHandler : WordLocW width)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved header : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (prePushRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (headerState : header = pushedHandlerState saved h1 h2 k savedHandler)
    (savedLookup : saved.store.lookup .handler = some savedHandler)
    (room : 3 ≤ saved.stackSpace)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ header.stackSpace)
    (registers : ∀ register, register ≠ k → regs.lookup register = saved.regs.lookup register)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (stack.drop (header.stackSpace - (args1.length - k))))
    (stackLength : stack.length = saved.stack.length)
    (stackTail : stack.drop header.stackSpace = header.stack.drop header.stackSpace) :
    stateRel ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))
      {header with
        clock := header.clock - 1, stackSpace := header.stackSpace - calleeSize,
        stack := stack, regs := regs.updateEq (0, .loc l1 l2)}
      (callerFrame :: lens) 0 := by
  have pushedRelation := stateRelPushedHandler ac k callerFrame h1 h2 handlerVar handlerCode
    source saved envs lens savedHandler savedLookup room prePushRelation
  rw [← headerState] at pushedRelation
  have resources := pushedHandlerStateResources saved h1 h2 k savedHandler room
  have headerLength : header.stack.length = saved.stack.length := by
    rw [headerState]; exact resources.2.2
  have headerSpace : header.stackSpace + 3 = saved.stackSpace := by
    rw [headerState]; exact resources.2.1
  have actualLength : stack.length = header.stack.length := stackLength.trans headerLength.symm
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  let cleared := {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with
    locals := .ln, localsSize := some 0}
  have calleeSource : WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)) =
      WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock cleared) := by
    rfl
  rw [calleeSource]
  change stateRel ac k 0 0 cleared header (callerFrame :: lens) 0 at pushedRelation
  unfold stateRel at pushedRelation
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, _, _,
    resource, oldStack, _⟩ := pushedRelation
  unfold stateRel
  refine ⟨?_, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, ?_, ?_,
    calleeShape, wfFromList2 args1, ?_, ?_, ?_⟩
  · show cleared.clock - 1 = header.clock - 1
    rw [g1]
  · show header.stackSpace - calleeSize + calleeSize ≤ stack.length
    omega
  · show stack.length < 2 ^ width
    omega
  · change stackSizeRel calleeSize ss cleared.stackLimit
      (wordSemOptionMax cleared.stackMax (wordSemOptionAdd (wordSemStackSize cleared.stack) ss))
      cleared.stack stack (header.stackSpace - calleeSize) 0
    obtain ⟨_, limit, maximum⟩ := resource
    refine ⟨fun _ => calleeLocalsSize, by simpa only [actualLength] using limit, ?_⟩
    intro newMaximum newValue
    rcases oldValue : cleared.stackMax with _ | oldMaximum
    · rw [oldValue] at newValue
      simp [wordSemOptionMax] at newValue
    obtain ⟨oldBound, _, size, oldSize, sizeValue⟩ := maximum oldMaximum oldValue
    rcases sizeOption : ss with _ | size
    · rw [oldValue, sizeOption, oldSize] at newValue
      simp [wordSemOptionMax, wordSemOptionAdd] at newValue
    rw [sizeOption] at calleeLocalsSize
    simp only [Option.getD_some] at calleeLocalsSize
    subst size
    rw [oldValue, oldSize, sizeOption] at newValue
    simp only [wordSemOptionMax, wordSemOptionAdd, Option.some.injEq] at newValue
    have := Nat.le_max_right oldMaximum (size + calleeSize)
    refine ⟨by omega, by simp, size, oldSize, by omega⟩
  · change stackRel k cleared.handler cleared.stack (header.store.lookup .handler)
      ((stack.drop (header.stackSpace - calleeSize + 0)).drop calleeSize)
      stack.length header.bitmaps (callerFrame :: lens)
    rw [List.drop_drop, Nat.add_zero, Nat.sub_add_cancel space, stackTail, actualLength]
    simpa only [Nat.add_zero, Nat.add_zero, List.drop_zero] using oldStack
  · apply handlerCalleeLocals ac k callerSize callerFrame calleeSize calleeFrame values names
      retCode l1 l2 dest args source saved {header with stack := stack, regs := regs} lens
      xs args1 prog ss envs guards callerRelation plainConventions calleeShape argumentBound
      header.stackSpace headerSpace space
    · intro register distinct
      change regs.lookup register = saved.regs.lookup register
      exact registers register distinct
    · exact slots
    · exact stackLength

/-- Actual StackHandlerArgs execution and native callee frame allocation,
with the full original handler callee-entry relation. The pushed header is
an explicit actual update of the saved caller, and all argument observations
are derived by executing the native move. This is Flapjack case factoring,
not the whole comp_correct result or an assumed callee target run. -/
theorem enterHandlerCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (savedHandler : WordLocW width)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (prePushRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (savedLookup : saved.store.lookup .handler = some savedHandler)
    (room : 3 ≤ saved.stackSpace)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ (pushedHandlerState saved h1 h2 k savedHandler).stackSpace) :
    let header := pushedHandlerState saved h1 h2 k savedHandler
    ∃ (moved entry : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (stackHandlerArgsNative false destination (args.length+1)
        (k,callerSize,callerFrame), header) = (none,moved) ∧
      StackSemEvaluate.evaluate (.stackAlloc (calleeSize-(args1.length-k)),
        StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none,entry) ∧
      stateRel ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))) entry (callerFrame :: lens) 0 := by
  dsimp only
  let header := pushedHandlerState saved h1 h2 k savedHandler
  change calleeSize ≤ header.stackSpace at space
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  have plainMaximum := lt_of_le_of_lt
    (maximumWithoutHandler values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2))) maximum
  have countEq := CallReturning.stackArgumentCount values names retCode l1 l2 dest args
    source xs args1 prog ss envs k callerSize callerFrame destinationCode destination guards
    destinationCompile
  have countCaller := CallReturning.stackArgumentFrameBound ac k callerSize callerFrame
    values names retCode l1 l2 dest args source saved lens xs args1 prog ss envs
    destinationCode destination guards callerRelation plainConventions plainMaximum destinationCompile
  have countCallee : args1.length-k ≤ calleeSize := by
    split_ifs at calleeShape <;> omega
  have useStack : saved.useStack = true := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  have stackBound : saved.stackSpace+callerSize ≤ saved.stack.length := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  obtain ⟨moved, stack, regs, moveRun, movedState, registers, stackLength, movedSpace,
    tail, slots⟩ := evaluateHandlerArguments k callerSize callerFrame h1 h2 destination
      (args.length+1) saved savedHandler useStack room stackBound countCaller
      (by change Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
            header.stackSpace; omega)
  rw [countEq] at movedState movedSpace tail slots
  subst moved
  let entry : StackSemStateFiniteExact width C F := {header with
    clock := header.clock-1, stackSpace := header.stackSpace-calleeSize,
    stack := stack, regs := regs.updateEq (0,.loc l1 l2)}
  refine ⟨_,entry,moveRun,?_,?_⟩
  · rw [StackSemEvaluate.evaluate_stackAlloc,
      if_neg (by simp [StackSemStateOps.setVar, StackSemStateOps.decClock,
        pushedHandlerState, useStack]),
      if_neg (by
        change ¬ header.stackSpace-(args1.length-k) < calleeSize-(args1.length-k)
        omega)]
    simp only [StackSemStateOps.setVar, StackSemStateOps.decClock]
    have spaceEq : header.stackSpace-(args1.length-k)-(calleeSize-(args1.length-k)) =
        header.stackSpace-calleeSize := by omega
    rw [spaceEq]
  · apply handlerCalleeStateRel ac k callerSize callerFrame calleeSize calleeFrame values names
      retCode l1 l2 dest args handlerVar h1 h2 handlerCode savedHandler source saved header
      lens xs args1 prog ss envs stack regs guards callerRelation prePushRelation conventions
      rfl savedLookup room calleeShape calleeLocalsSize argumentBound space
    · intro register distinct
      have preserved := registers register distinct
      change regs.lookup register = saved.regs.lookup register at preserved
      exact preserved
    · exact slots
    · change stack.length = saved.stack.length at stackLength
      exact stackLength
    · change stack.drop (header.stackSpace-(args1.length-k)+(args1.length-k)) =
        header.stack.drop header.stackSpace at tail
      rw [Nat.sub_add_cancel (show args1.length-k ≤ header.stackSpace by omega)] at tail
      exact tail

/-- Derive the handler callee non-error obligation from the actual whole
source call run before using its original guarded induction hypothesis. The
handler cannot intercept Error. This is Flapjack factoring of the original
handler body-IH step; no target run or additional non-error premise is used.
There is no separate HOL declaration for this case-local elimination. -/
theorem handlerCalleeNotError {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source sourcePost calleePost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args handler) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, calleePost)) : bodyResult ≠ some .error := by
  intro error
  rw [error] at bodyRun
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only [Prod.mk.injEq] at execution
  exact absurd execution.1.symm notError

/-- Actual destination, caller save, handler push and argument move with
preserved compiled callee lookup. The source get/find/cut guards, original
conventions and bitmap bounds construct every target execution. Indirect
destination registers avoid the actual scratch register and erased return
register. This is Flapjack handler-case infrastructure; no final target run
or callee lookup is supplied and no full comp_correct port is claimed. -/
theorem prepareHandlerCalleeDestination {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace-3) :
    ∃ (destinationTarget saved header moved : StackSemStateFiniteExact width C F)
      (calleeCode : HolProg width) (calleeSize : Nat)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat)
      (savedHandler : WordLocW width),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (pushHandlerNative false h1 h2 (k,f,frame), saved) =
        (none,header) ∧
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination (args.length + 1) (k,f,frame), header) =
        (none,moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source
          with locals := .ln, localsSize := some 0}
        header (frame :: lens) 0 ∧
      compileProgNative ac false prog args1.length k (calleeBs, calleeIndex) =
        (calleeCode, calleeSize, (calleeBsPost, calleeIndexPost)) ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode ∧
      saved.store.lookup .handler = some savedHandler ∧
      header = pushedHandlerState saved h1 h2 k savedHandler ∧
      saved.stackSpace = target.stackSpace ∧
      moved.clock = target.clock ∧ moved.ffi = source.ffi := by
  have plainConventions := conventionsWithoutHandler k values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) conventions
  have plainMaximum := lt_of_le_of_lt
    (maximumWithoutHandler values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2))) maximum
  have originalGuards := guards
  obtain ⟨get, bad, find, _, _⟩ := originalGuards
  obtain ⟨destinationTarget, destinationRun, destinationRelation,
    destinationLength, destinationSpace, callees⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens destinationCode destination xs
      (some (values, names, retCode, l1, l2)) ⟨bad, related, destinationCompile, get⟩
  obtain ⟨calleeBs, calleeIndex, calleeBsPost, calleeIndexPost, calleeSize, calleeCode,
    calleeCompile, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix,
    calleeLocalsSize, found⟩ := callees args1 prog ss find
  obtain ⟨destinationBitmaps, _⟩ := CallDest.callDest_preserves dest args (k, f, frame)
    destinationCode destination target destinationTarget destinationCompile destinationRun
  obtain ⟨saved, savedRun, pushedRelation, savedRelation, savedLength, savedSpace, savedRegisters⟩ :=
    CallReturning.evaluateSavedFrame ac k f frame values names retCode l1 l2 dest args source destinationTarget lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex savedCode guards destinationRelation
      plainConventions plainMaximum savedCompile bitmapLength (by rwa [destinationBitmaps])
      (by rwa [destinationBitmaps])
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have frameBound : saved.stackSpace + f ≤ saved.stack.length := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have moveBound := CallReturning.stackArgumentFrameBound ac k f frame values names retCode l1 l2 dest args
    source saved lens xs args1 prog ss envs destinationCode destination guards savedRelation
    plainConventions plainMaximum destinationCompile
  have savedRoom : 3 ≤ saved.stackSpace := by
    rw [savedSpace, destinationSpace]; exact room
  have preludeGrowth := sptSubsptTrans target.code destinationTarget.code saved.code
    ⟨(Compiler.Backend.StackProps.EvaluateMono.evaluateMono destinationCode target destinationTarget
      none destinationRun).2,
      (Compiler.Backend.StackProps.EvaluateMono.evaluateMono savedCode destinationTarget saved
        none savedRun).2⟩
  have savedLocation := LocationLabels.locCheckSubset target.code saved.code preludeGrowth
    (h1,h2) location
  obtain ⟨savedHandler, savedLookup, pushRun⟩ := evaluatePushHandlerFromStateRel ac k f frame
    h1 h2 source saved envs lens savedRoom pushedRelation savedLocation
  let header := pushedHandlerState saved h1 h2 k savedHandler
  have headerRelation := stateRelPushedHandler ac k frame h1 h2 handlerVar handlerCode source
    saved envs lens savedHandler savedLookup savedRoom pushedRelation
  obtain ⟨moved, stack, regs, moveRun, movedState, moveRegisters, _, _, _, _⟩ :=
    evaluateHandlerArguments k f frame h1 h2 destination (args.length+1) saved savedHandler
      useStack savedRoom frameBound moveBound
      (by change _ ≤ saved.stackSpace-3; rw [savedSpace,destinationSpace]; exact space)
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono savedCode
    destinationTarget saved none savedRun).2
  have movedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackHandlerArgsNative false destination (args.length + 1) (k,f,frame)) header moved none moveRun).2
  have headerGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (pushHandlerNative false h1 h2 (k,f,frame)) saved header none pushRun).2
  have registers : ∀ register, register ≠ k → moved.regs.lookup register =
      destinationTarget.regs.lookup register := by
    intro register notScratch
    exact (moveRegisters register notScratch).trans (savedRegisters register notScratch)
  have finalFound := CallReturning.findCodePreserved k destination destinationTarget.regs moved.regs
    destinationTarget.code moved.code calleeCode
    (CallReturning.destinationRegisterBound k f frame values names retCode l1 l2 dest args destinationCode destination
      plainConventions destinationCompile)
    registers (sptSubsptTrans _ _ _ ⟨savedGrowth,
      sptSubsptTrans _ _ _ ⟨headerGrowth,movedGrowth⟩⟩) found
  refine ⟨destinationTarget, saved, header, moved, calleeCode, calleeSize, calleeBs, calleeBsPost,
    calleeIndex, calleeIndexPost, savedHandler, destinationRun, savedRun, pushRun, moveRun,
    savedRelation, pushedRelation, headerRelation,
    calleeCompile, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize, finalFound, savedLookup, rfl,
    savedSpace.trans destinationSpace, ?_, ?_⟩
  · rw [movedState]
    exact savedRelation.1.symm.trans related.1
  · rw [movedState]
    exact savedRelation.2.2.2.1

/-- Handler callee resource overflow from the full actual pushed-frame
relation, with all Option size/max cases. This factors the original handler
allocation-failure branch, not a separately named HOL theorem; no overflow
or target result is assumed. -/
theorem handlerCalleeStackOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerFrame calleeSize : Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize) :
    let callee := WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))
    miscThe (callee.stackLimit + 1) callee.stackMax > callee.stackLimit := by
  let cleared := {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with
    locals := .ln, localsSize := some 0}
  change stateRel ac k 0 0 cleared saved (callerFrame :: lens) 0 at pushedRelation
  unfold stateRel at pushedRelation
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, stackBound, _, _, _, resource, _⟩ := pushedRelation
  change miscThe (cleared.stackLimit + 1)
    (wordSemOptionMax cleared.stackMax (wordSemOptionAdd (wordSemStackSize cleared.stack) ss)) >
    cleared.stackLimit
  obtain ⟨_, limit, maximum⟩ := resource
  rw [limit]
  rcases oldValue : cleared.stackMax with _ | oldMaximum
  · simp [wordSemOptionMax, miscThe]
  obtain ⟨_, _, size, oldSize, sizeValue⟩ := maximum oldMaximum oldValue
  rcases sizeOption : ss with _ | localSize
  · simp [wordSemOptionMax, wordSemOptionAdd, miscThe]
  rw [sizeOption] at calleeLocalsSize
  simp only [Option.getD_some] at calleeLocalsSize
  subst localSize
  simp only [oldSize, wordSemOptionMax, wordSemOptionAdd, miscThe]
  have := Nat.le_max_right oldMaximum (size + calleeSize)
  omega

/-- Flapjack factoring of the complete source resource conclusion in the
original allocation-failure branches. Timeout, callee outcomes, pop_env and
continuation evaluation all retain the exceeded-resource fact. The overflow
is derived from the actual saved-frame relation, not an added source premise. -/
theorem handlerSourceCallOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerFrame calleeSize : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost)) :
    miscThe (sourcePost.stackLimit + 1) sourcePost.stackMax > sourcePost.stackLimit := by
  have overflow := handlerCalleeStackOverflow ac k callerFrame calleeSize handlerVar h1 h2
    handlerCode source saved lens envs args1 ss
    pushedRelation calleeLocalsSize insufficient
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


/-- Full original comp_correct result/resource conclusion for the handler
argument/frame allocation-failure branches. Actual source evaluation proves
its event prefix and final resource overflow through every handler outcome;
the concrete empty-env target is Halt two. This is Flapjack branch factoring,
not a whole-case port or an assumed target execution. -/
theorem handlerAllocationFailureResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (failureClock failureSpace : Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost)) :
    compCorrectResult ac k callerSize callerFrame source sourcePost
      (StackSemStateOps.emptyEnv {saved with clock := failureClock, stackSpace := failureSpace})
      result (some (.halt (.word (BitVec.ofNat width 2)))) lens := by
  have overflow := handlerSourceCallOverflow ac k callerFrame calleeSize values names retCode l1 l2
    dest args handlerVar h1 h2 handlerCode source sourcePost saved lens result xs args1 prog ss envs guards pushedRelation
    calleeLocalsSize insufficient execution
  have events := WordSemStateFiniteExact.evaluate_io_events_mono
    (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source result sourcePost execution
  unfold stateRel at pushedRelation
  obtain ⟨_, _, _, ffi, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    dimension, _⟩ := pushedRelation
  have mismatch : result.map compileResult ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
    cases result with
    | none => simp
    | some value =>
      intro same
      exact CallHelpers.compileResultNot2 value dimension (Option.some.inj same)
  unfold compCorrectResult
  rw [if_pos mismatch]
  refine ⟨rfl, ?_, ?_⟩
  · change saved.ffi.ioEvents.IsPrefix sourcePost.ffi.ioEvents
    have ffiEq : saved.ffi = source.ffi := by simpa only [WordSemStateFiniteExact.pushEnv] using ffi
    rw [ffiEq]
    exact events
  · cases maximum : sourcePost.stackMax with
    | none => simp
    | some value => simpa only [maximum, miscThe, Option.getD_some] using overflow


/-- Decompose the actual compiled callee tree into its frame allocation
and body, retaining its exact bitmap output. Frame shape, argument capacity
and maximum are derived from compile_prog's literal definition. This is
Flapjack case infrastructure with no separate HOL declaration; no successful
execution or target relation is assumed. -/
theorem calleeBodyCompilation {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (k argumentCount : Nat)
    (prog : WordLangProgHOL (BitVec width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiledCode : HolProg width) (calleeSize : Nat)
    (compiled : compileProgNative ac false prog argumentCount k (bs,n) =
      (compiledCode,calleeSize,(bsPost,nPost))) :
    ∃ (body : HolProg width) (calleeFrame : Nat),
      compiledCode = .seq (.stackAlloc (calleeSize-(argumentCount-k))) body ∧
      compNative ac false prog (bs,n) (k,calleeSize,calleeFrame) = (body,(bsPost,nPost)) ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame+1) ∧
      argumentCount-k ≤ calleeFrame ∧ maxVarHOL prog < 2*calleeFrame+2*k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (argumentCount-k) := by
  simp only [compileProgNative] at compiled
  set calleeFrame := max (maxVarHOL prog / 2 + 1 - k) (argumentCount-k) with frameDef
  rcases bodyCompile : compNative ac false prog (bs,n)
      (k,if calleeFrame = 0 then 0 else calleeFrame+1,calleeFrame) with ⟨body,bitmaps⟩
  rw [bodyCompile] at compiled
  simp only [Prod.mk.injEq] at compiled
  obtain ⟨rfl,sizeDef,bitmapsDef⟩ := compiled
  subst bitmaps
  rw [sizeDef] at bodyCompile
  have shape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame+1 := by
    split_ifs at sizeDef ⊢ <;> omega
  have argumentBound : argumentCount-k ≤ calleeFrame := by
    rw [frameDef]
    exact Nat.le_max_right _ _
  have maximum : maxVarHOL prog < 2*calleeFrame+2*k := by
    have bound := Nat.le_max_left (maxVarHOL prog / 2 + 1 - k) (argumentCount-k)
    rw [← frameDef] at bound
    omega
  refine ⟨body,calleeFrame,?_,bodyCompile,shape,argumentBound,maximum,frameDef⟩
  rw [sizeDef]

/-- Original handler callee body induction step with an actual target run.
The whole source call supplies the non-error guard; source code and actual
prelude execution supply all compilation, label and bitmap obligations;
native handler argument movement/allocation construct the callee relation.
Only the original guarded source induction hypotheses are used. This is
Flapjack factoring of the original successful body-entry branch, not the
whole returning-handler comp_correct theorem or a supplied target run. -/
theorem simulateHandlerCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
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
    ∃ (destinationTarget saved header moved entry targetPost : StackSemStateFiniteExact width C F)
      (calleeCode body : HolProg width) (calleeSize calleeFrame extra : Nat)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (destinationCode,target) = (none,destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode,destinationTarget) = (none,saved) ∧
      StackSemEvaluate.evaluate (pushHandlerNative false h1 h2 (k,f,frame),saved) = (none,header) ∧
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination (args.length+1) (k,f,frame),header) =
          (none,moved) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode ∧
      calleeCode = .seq (.stackAlloc (calleeSize-(args1.length-k))) body ∧
      StackSemEvaluate.evaluate (.stackAlloc (calleeSize-(args1.length-k)),
        StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none,entry) ∧
      StackSemEvaluate.evaluate (body,{entry with clock := entry.clock+extra}) =
        (targetResult,targetPost) ∧
      StackSemEvaluate.evaluate
        (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
          with clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))) bodyPost targetPost bodyResult
        targetResult (frame :: lens) := by
  let expectedFrame := max (maxVarHOL prog / 2 + 1-k) (args1.length-k)
  have countEq := CallReturning.stackArgumentCount values names retCode l1 l2 dest args
    source xs args1 prog ss envs k f frame destinationCode destination guards destinationCompile
  have countBound : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
      target.stackSpace-3 := by
    rw [countEq]
    have capacity : args1.length-k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at space <;> omega
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleeBsPost,
    calleeIndex,calleeIndexPost,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,calleeBitmapLength,
    calleeBitmapBound,calleeBitmapPrefix,calleeLocalsSize,found,savedLookup,headerState,
    savedSpace,_,_⟩ := prepareHandlerCalleeDestination ac k f frame values names retCode l1 l2
      dest args handlerVar h1 h2 handlerCode source target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions
      maximum destinationCompile savedCompile bitmapLength bitmapBound bitmapPrefix room
      location countBound
  obtain ⟨body,calleeFrame,codeEq,bodyCompile,shape,argumentBound,bodyMaximum,frameEq⟩ :=
    calleeBodyCompilation ac k args1.length prog calleeBs calleeBsPost calleeIndex
      calleeIndexPost calleeCode calleeSize calleeCompile
  have frameSpace : calleeSize ≤ (pushedHandlerState saved h1 h2 k savedHandler).stackSpace := by
    change calleeSize ≤ saved.stackSpace-3
    rw [savedSpace]
    change calleeFrame = expectedFrame at frameEq
    rw [frameEq] at shape
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at shape space <;> omega
  obtain ⟨movedAgain,entry,moveAgain,allocateRun,entryRelation⟩ := enterHandlerCallee ac k f frame
    calleeSize calleeFrame values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
    savedHandler source saved lens xs args1 prog ss envs destinationCode destination guards
    savedRelation prePushRelation conventions maximum destinationCompile savedLookup
    (by rw [savedSpace]; exact room) shape calleeLocalsSize argumentBound frameSpace
  rw [← headerState] at moveAgain
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  have destinationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun
  have savedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun
  have headerMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (pushHandlerNative false h1 h2 (k,f,frame)) saved header none pushRun
  have movedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)) header moved none moveRun
  have allocationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize-(args1.length-k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) entry none allocateRun
  have allocationBitmaps : moved.bitmaps.IsPrefix entry.bitmaps := allocationMono.1
  have allocationCode : sptSubspt moved.code entry.code := allocationMono.2
  have bitmapGrowth := destinationMono.1.trans (savedMono.1.trans
    (headerMono.1.trans (movedMono.1.trans allocationBitmaps)))
  have entryBitmapBound := calleeBitmapBound.trans bitmapGrowth.length_le
  have entryBitmapPrefix := calleeBitmapPrefix.trans
    (bitmapGrowth.drop (calleeIndex-(appListAppend calleeBs).length))
  have bodyLabels : ∀ label, StackSem.getLabelsExact body label →
      StackSem.locCheckExact entry.code label := by
    intro label member
    apply LocationLabels.locCheckSubset moved.code entry.code allocationCode label
    apply StackPropsCodeLabels.findCodeImpGetLabels destination (moved.regs.eraseEq 0)
      moved.code calleeCode found label
    rw [codeEq,StackSem.getLabelsExact]
    exact Or.inr member
  obtain ⟨_,_,_,_,_,_,_,_,_,_,bodyConventions,bodyFlat,_⟩ :=
    CallReturning.calleeCompilation ac k f frame values names retCode l1 l2 dest args
      source target lens xs args1 prog ss envs guards related
  have bodyNotError := handlerCalleeNotError values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) source sourcePost bodyPost result bodyResult
    xs args1 prog ss envs guards nonzero wholeExecution notError bodyRun
  have simulation := hypotheses.2.2 xs args1 prog ss envs ⟨guards,nonzero⟩
  obtain ⟨extra,targetPost,targetResult,execution,conclusion⟩ :=
    simulation k calleeSize calleeFrame bodyPost entry bodyResult calleeBs calleeBsPost
      calleeIndex calleeIndexPost body (frame :: lens)
      ⟨bodyRun,bodyNotError,entryRelation,bodyConventions,bodyFlat,bodyCompile,
        calleeBitmapLength,entryBitmapBound,entryBitmapPrefix,bodyLabels,bodyMaximum⟩
  have allocationClock (bump : Nat) : StackSemEvaluate.evaluate
      (.stackAlloc (calleeSize-(args1.length-k)),
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
          with clock := (StackSemStateOps.decClock moved).clock + bump}) =
      (none,{entry with clock := entry.clock + bump}) := by
    have success := allocateRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_,rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc,if_neg disabled,if_neg insufficient]
    rfl
  have calleeExecution : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
        with clock := (StackSemStateOps.decClock moved).clock + extra}) =
      (targetResult,targetPost) := by
    rw [codeEq,StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extra]
    exact execution
  exact ⟨destinationTarget,saved,header,moved,entry,targetPost,calleeCode,body,calleeSize,
    calleeFrame,extra,targetResult,destinationRun,savedRun,pushRun,moveRun,found,codeEq,
    allocateRun,execution,calleeExecution,conclusion⟩

/-- Actual native restoration state after reading the saved handler slot,
setting the handler store and freeing precisely the three header words.
Flapjack proof infrastructure for the original normal-return branch9495+;
this is not a replacement evaluator or an assumed final state relation. -/
def poppedHandlerState {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) : StackSemStateFiniteExact width C F :=
  {source with
    regs := source.regs.updateEq (register, savedHandler),
    store := source.store.updateEq (.handler, savedHandler),
    stackSpace := source.stackSpace + 3}

/-- Compute the real PopHandler execution before an arbitrary continuation.
Only primitive preconditions are used; neither a target run nor postrelation
is supplied. This supports the full original case and has no separate HOL
original. All other state fields and the continuation's evaluation are exact. -/
theorem evaluatePopHandler {width : Nat} [NeZero width] {C F β γ : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (f : β) (f' : γ) (program : HolProg width) (savedHandler : WordLocW width)
    (stackEnabled : source.useStack = true) (storeEnabled : source.useStore = true)
    (room : source.stackSpace + 3 ≤ source.stack.length)
    (saved : source.stack[source.stackSpace + 2] = savedHandler) :
    StackSemEvaluate.evaluate (popHandlerNative false (register,f,f') program, source) =
      StackSemEvaluate.evaluate (program, poppedHandlerState source register savedHandler) := by
  have slotBound : source.stackSpace + 2 < source.stack.length := by omega
  simp [popHandlerF, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_set,
    StackSemEvaluate.evaluate_stackFree, StackSemStateOps.setVar,
    StackSemStateOps.getVar, StackSemStateOps.setStore,
    StackSemRegisterTransfers.storeOfSyntax, StackSemControl.fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    stackEnabled, storeEnabled, slotBound, Nat.not_lt.mpr room,
    saved, poppedHandlerState]

/-- The three-word restore preserves every non-scratch register and the
remaining occupied stack, while writing exactly the saved handler. These are
actual update consequences used by the full normal-return relation proof;
there is no separate HOL declaration. -/
theorem poppedHandlerResources {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) :
    (poppedHandlerState source register savedHandler).stackSpace = source.stackSpace + 3 ∧
    (poppedHandlerState source register savedHandler).stack = source.stack ∧
    (poppedHandlerState source register savedHandler).ffi = source.ffi ∧
    (poppedHandlerState source register savedHandler).clock = source.clock ∧
    (poppedHandlerState source register savedHandler).store.lookup .handler = some savedHandler ∧
    (∀ other, other ≠ register →
      StackSemStateOps.getVar other (poppedHandlerState source register savedHandler) =
        StackSemStateOps.getVar other source) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [poppedHandlerState, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · intro other distinct
    simp [poppedHandlerState, StackSemStateOps.getVar,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, distinct]

/-- Native PushHandler writes its saved handler into the exact slot consumed
by PopHandler. The slot bound is derived from the original stack-space bounds;
no header representation premise is introduced. Flapjack proof support. -/
theorem pushedSavedHandler {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (savedHandler : WordLocW width) (room : 3 ≤ source.stackSpace)
    (bound : source.stackSpace ≤ source.stack.length) :
    (pushedHandlerState source a b register savedHandler).stack[
      (pushedHandlerState source a b register savedHandler).stackSpace + 2]' (by simp [pushedHandlerState]; omega) = savedHandler := by
  simp [pushedHandlerState]

/-- Derive restoration after an actual native handler setup with arbitrary
continuation. This law computes both operations rather than supplying any
successful execution; it is support for the full returning-handler case. -/
theorem evaluatePopAfterPush {width : Nat} [NeZero width] {C F β γ : Type}
    (source : StackSemStateFiniteExact width C F) (a b register : Nat)
    (f : β) (f' : γ) (program : HolProg width) (savedHandler : WordLocW width)
    (stackEnabled : source.useStack = true) (storeEnabled : source.useStore = true)
    (room : 3 ≤ source.stackSpace) (bound : source.stackSpace ≤ source.stack.length) :
    StackSemEvaluate.evaluate
      (popHandlerNative false (register,f,f') program,
        pushedHandlerState source a b register savedHandler) =
    StackSemEvaluate.evaluate
      (program, poppedHandlerState (pushedHandlerState source a b register savedHandler)
        register savedHandler) := by
  have restoredRoom : (pushedHandlerState source a b register savedHandler).stackSpace + 3 ≤
      (pushedHandlerState source a b register savedHandler).stack.length := by
    simpa only [pushedHandlerState, List.length_set, Nat.sub_add_cancel room] using bound
  exact evaluatePopHandler (pushedHandlerState source a b register savedHandler)
    register f f' program savedHandler stackEnabled storeEnabled restoredRoom
    (pushedSavedHandler source a b register savedHandler room bound)

/-- Total EL inhabitation chooses no past-end observation. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Derive native restoration and the remaining saved-stack relation from the
actual full callee relation and its handler frame. The frame premise is the
source stack-swap observation established in the original normal-return branch;
it is not a desired target postrelation. This is untagged proof infrastructure,
not a narrowed comp_correct case. -/
theorem restoreFromStateRel {width : Nat} [NeZero width] {C F β γ : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width) (register : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (savedSourceHandler label1 label2 frameSize : Nat)
    (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (f : β) (f' : γ) (program : HolProg width)
    (sourceFrame : source.stack =
      .stackFrame n l0 l (some (savedSourceHandler,label1,label2)) :: rest)
    (relation : stateRel ac register 0 0 source target (frameSize :: lens) 0) :
    StackSemEvaluate.evaluate (popHandlerNative false (register,f,f') program, target) =
      StackSemEvaluate.evaluate (program, poppedHandlerState target register
        (holEl 2 (target.stack.drop target.stackSpace))) ∧
    stackRel register savedSourceHandler rest
      (some (holEl 2 (target.stack.drop target.stackSpace)))
      ((target.stack.drop target.stackSpace).drop (frameSize + 4))
      target.stack.length target.bitmaps lens := by
  unfold stateRel at relation
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38⟩ := relation
  simp only [Nat.add_zero, List.take_zero, List.drop_zero] at h38
  have savedStack := h38.1
  rw [sourceFrame] at savedStack
  have available := stackRelConsLenSome register source.handler n l0 l
    savedSourceHandler label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
    frameSize lens savedStack
  have room : target.stackSpace + 3 ≤ target.stack.length := by
    simp only [List.length_drop] at available
    omega
  constructor
  · have slot : target.stackSpace + 2 < target.stack.length := by omega
    have saved : target.stack[target.stackSpace + 2] =
        holEl 2 (target.stack.drop target.stackSpace) := by
      rw [holElDrop,
        holEl_eq_getElem (target.stackSpace + 2) target.stack (by omega)]
    exact evaluatePopHandler target register f f' program
      (holEl 2 (target.stack.drop target.stackSpace)) h5 h6 room saved
  · exact stackRelDropSome register source.handler n l0 l savedSourceHandler
      label1 label2 rest (target.store.lookup .handler)
      (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
      frameSize lens savedStack

/-- Erasing the handler from the actually updated store restores the same
canonical non-handler store. This is proved at arbitrary lookup keys, not
assumed as a poststate property. Flapjack normal-return proof infrastructure. -/
theorem poppedStoreErase {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (register : Nat)
    (savedHandler : WordLocW width) :
    (poppedHandlerState source register savedHandler).store.eraseEq .handler =
      source.store.eraseEq .handler := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [poppedHandlerState, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
  by_cases equal : key = .handler
  · simp [equal]
  · simp [equal, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The saved tail relation has exactly the occupied suffix and store of the
actual restored native state after freeing the three-word handler header.
The remaining caller frame contains its bitmap plus frameSize payload words,
just as in original normal-return proof's f = fprime + 1 step. This is derived
from the old relation and concrete updates, not a target postrelation premise. -/
theorem poppedTailRelation {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (register sourceHandler : Nat)
    (n : Option Nat) (l0 l : List (Nat × WordLocW width))
    (savedSourceHandler label1 label2 frameSize : Nat)
    (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (relation : stackRel register sourceHandler
      (.stackFrame n l0 l (some (savedSourceHandler,label1,label2)) :: rest)
      (target.store.lookup .handler) (target.stack.drop target.stackSpace)
      target.stack.length target.bitmaps (frameSize :: lens)) :
    let restored := poppedHandlerState target register
      (holEl 2 (target.stack.drop target.stackSpace))
    stackRel register savedSourceHandler rest (restored.store.lookup .handler)
      (restored.stack.drop (restored.stackSpace + (frameSize + 1)))
      restored.stack.length restored.bitmaps lens := by
  have tail := stackRelDropSome register sourceHandler n l0 l savedSourceHandler
    label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop target.stackSpace) target.stack.length target.bitmaps
    frameSize lens relation
  simpa [poppedHandlerState, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

/-- Execute the original normal-return copy with its three-word handler offset.
The saved handler slot is derived from the copy operation's untouched prefix;
no successful target execution or restoration relation is supplied. This is
Flapjack case factoring for the original normal-return branch, not a separate
HOL theorem. -/
theorem copyHandlerReturn {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (register frame count : Nat)
    (enabled : target.useStack = true)
    (room : frame + 3 ≤ target.stack.length - (target.stackSpace + count))
    (countBound : count ≤ frame) :
    ∃ copied : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (copyRetAuxNative register (frame + 3) count, target) =
        (none, copied) ∧
      copied.stack.length = target.stack.length ∧
      copied.stackSpace = target.stackSpace ∧
      copied.store = target.store ∧ copied.ffi = target.ffi ∧
      copied.clock = target.clock ∧
      holEl 2 (copied.stack.drop (copied.stackSpace + count)) =
        holEl 2 (target.stack.drop (target.stackSpace + count)) ∧
      copied.stack.drop (copied.stackSpace + count + (frame + 3)) =
        target.stack.drop (target.stackSpace + count + (frame + 3)) ∧
      (∀ other, other ≠ register →
        StackSemStateOps.getVar other copied = StackSemStateOps.getVar other target) ∧
      (∀ index, index < count →
        holEl (index + (frame + 3)) (copied.stack.drop copied.stackSpace) =
          holEl index (target.stack.drop target.stackSpace)) := by
  obtain ⟨copied, execution, stack, regs, state, length, space, tail,
    registers, untouched, values⟩ := CallReturnEval.evaluateCopyRetAux
      register (frame + 3) count target ⟨enabled, by omega, room⟩
  have saved := untouched 2 (by omega)
  refine ⟨copied, execution, ?_, space, ?_, ?_, ?_, ?_, ?_, registers, ?_⟩
  · simpa only [state] using length
  · simp only [state]
  · simp only [state]
  · simp only [state]
  · simpa only [state, Nat.add_comm] using saved
  · simpa only [state, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
  · simpa only [state] using values

/-- Compute the normal-return copy, result-slot free, and handler restore
before an arbitrary continuation. Every target transition is constructed from
primitive original frame bounds. The restored handler is the actual saved
slot before copying, not a requested target poststate. Flapjack case support. -/
theorem evaluateHandlerReturnRestore {width : Nat} [NeZero width] {C F β γ : Type}
    (target : StackSemStateFiniteExact width C F) (register frame count : Nat)
    (f : β) (f' : γ) (continuation : HolProg width)
    (enabled : target.useStack = true) (storeEnabled : target.useStore = true)
    (room : frame + 3 ≤ target.stack.length - (target.stackSpace + count))
    (countBound : count ≤ frame) :
    ∃ copied : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (copyRetAuxNative register (frame + 3) count, target) =
        (none, copied) ∧
      StackSemEvaluate.evaluate
        (.seq (copyRetAuxNative register (frame + 3) count)
          (.seq (.stackFree count) (popHandlerNative false (register,f,f') continuation)),
          target) =
        StackSemEvaluate.evaluate
          (continuation, poppedHandlerState
            {copied with stackSpace := copied.stackSpace + count} register
            (holEl 2 (target.stack.drop (target.stackSpace + count)))) ∧
      copied.stack.length = target.stack.length ∧
      copied.stackSpace = target.stackSpace ∧ copied.clock = target.clock := by
  obtain ⟨copied, execution, length, space, store, ffi, clock, saved, tail,
    registers, values⟩ := copyHandlerReturn target register frame count enabled room countBound
  have stateBound : target.stackSpace + count + 3 ≤ target.stack.length := by omega
  have copiedEnabled : copied.useStack = true := by
    exact (Compiler.Backend.StackProps.evaluateConsts
      (copyRetAuxNative register (frame + 3) count) target none copied execution).2.2.1.trans enabled
  have copiedStoreEnabled : copied.useStore = true := by
    exact (Compiler.Backend.StackProps.evaluateConsts
      (copyRetAuxNative register (frame + 3) count) target none copied execution).2.1.trans storeEnabled
  let freed : StackSemStateFiniteExact width C F :=
    {copied with stackSpace := copied.stackSpace + count}
  have freeRun : StackSemEvaluate.evaluate (.stackFree count, copied) = (none, freed) := by
    simp only [StackSemEvaluate.evaluate_stackFree, copiedEnabled, Bool.not_true,
      Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
    simp only [freed, copiedEnabled]
  have freedRoom : freed.stackSpace + 3 ≤ freed.stack.length := by
    dsimp [freed]; omega
  have savedSlot : freed.stack[freed.stackSpace + 2] =
      holEl 2 (target.stack.drop (target.stackSpace + count)) := by
    rw [← saved, holElDrop,
      holEl_eq_getElem (copied.stackSpace + count + 2) copied.stack (by omega)]
  have popRun := evaluatePopHandler freed register f f' continuation
    (holEl 2 (target.stack.drop (target.stackSpace + count)))
    copiedEnabled copiedStoreEnabled freedRoom savedSlot
  refine ⟨copied, execution, ?_, length, space, clock⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    execution]
  simp only
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, freeRun]
  exact popRun

/-- The original call conventions and maximum imply the actual number of
stack return values fits the caller frame. This discharges the copy/restore
count bound from source hypotheses rather than strengthening the full case.
Flapjack arithmetic factoring of the original normal-return proof. -/
theorem handlerReturnCountBound {width : Nat} [NeZero width]
    (k frame localsFrame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2 * localsFrame + 2 * k)
    (frameShape : if localsFrame = 0 then frame = 0 else frame = localsFrame + 1) :
    Compiler.Backend.WordToStack.numStackRet k values ≤ frame := by
  have sequence : values = (List.range values.length).map (fun x => 2 * (x + 1)) := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true, beq_iff_eq] at conventions
    aesop (config := { enableSimp := false })
  have valueMaximum : 2 * values.length ≤ maxList values := by
    by_cases empty : values.length = 0
    · simp [empty]
    · have member : 2 * values.length ∈ values := by
        rw [sequence]
        apply List.mem_map.mpr
        refine ⟨values.length - 1, List.mem_range.mpr (by omega), ?_⟩
        simp only [List.length_map, List.length_range]
        omega
      exact maxList_ge_of_mem values (2 * values.length) member
  have maximumBound : maxList values ≤ maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) := by
    simp only [maxVarHOL, Flapjack.WordAlloc.max3Eq]
    omega
  unfold Compiler.Backend.WordToStack.numStackRet
  split at frameShape <;> omega

/-- Recover the actual SOME-handler caller frame after the source callee
returns. Full evaluate_stack_swap supplies frame keys, saved handler labels,
non-GC values and size; native pop_env then computes restored locals and
handler. No returned frame or desired relation is assumed. Flapjack factoring
of the original handler normal-return branch, distinct from the NONE case. -/
theorem returnedHandlerCallerFrame {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (source bodyPost : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width)),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc (some (source.handler,h1,h2)) :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.stack.length ∧
      WordSemStateFiniteExact.popEnv bodyPost = some {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize, handler := source.handler} ∧
      sptDomainEqUnion
        (sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1))) envs.1 envs.2 := by
  have invariant := WordSemStackEq.evaluateStackSwap prog
    (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))
  unfold WordSemStackEq.stackSwapPost at invariant
  rw [bodyRun] at invariant
  obtain ⟨keys, handler, _⟩ := invariant
  have pushedKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
        (WordSemStateFiniteExact.decClock source)).stack bodyPost.stack := keys
  obtain ⟨_, _, _, _, _, popped, poppedRun, _, domain, _⟩ :=
    WordSemStackEq.pushEnvPopEnvSKeyEq envs (some (handlerVar,handlerCode,h1,h2))
      (WordSemStateFiniteExact.decClock source) bodyPost pushedKeys
  change WordSemStackEq.sKeyEq
    (.stackFrame source.localsSize (sptToAList envs.1)
      (wordSemEnvToList envs.2 source.permute).1 (some (source.handler,h1,h2)) :: source.stack) bodyPost.stack at keys
  cases stackEq : bodyPost.stack with
  | nil => simp only [stackEq, WordSemStackEq.sKeyEq] at keys
  | cons frame tail =>
    cases frame with
    | stackFrame size nonGc gc opt =>
      rw [stackEq] at keys
      obtain ⟨tailKeys, frameKeys⟩ := keys
      rw [WordSemStackEq.sFrameKeyEqDef2] at frameKeys
      obtain ⟨gcKeys, rfl, rfl, rfl⟩ := frameKeys
      have popRun : WordSemStateFiniteExact.popEnv bodyPost = some {bodyPost with
          locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
          stack := tail, localsSize := source.localsSize, handler := source.handler} := by
        rw [WordSemStateFiniteExact.popEnv, stackEq]
      have same := Option.some.inj (poppedRun.symm.trans popRun)
      subst popped
      refine ⟨gc, tail, rfl, gcKeys, tailKeys, handler, popRun, ?_⟩
      intro key
      have equality := congrFun domain key
      simpa only [sptMem, sptDomain, or_comm] using (Eq.to_iff equality.symm)

/-- The actual non-error handler Call and callee normal result derive the
return location/length checks, restored source environment, domain check,
actual continuation run and original guarded continuation IH. No target
restoration or simulation conclusion is supplied. Flapjack assembly for the
original handler normal-return branch; the full case remains unfinished. -/
theorem sourceHandlerReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
      (popped : WordSemStateFiniteExact width (Nat × C) F),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc (some (source.handler,h1,h2)) :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.stack.length ∧
      popped = {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize, handler := source.handler} ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptDomainEqUnion popped.locals envs.1 envs.2 ∧
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values returned popped) := by
  obtain ⟨gc, tail, frame, gcKeys, tailKeys, handler, popRun, domain⟩ :=
    returnedHandlerCallerFrame prog source bodyPost envs args1 ss
      handlerVar h1 h2 handlerCode location returned bodyRun
  let popped : WordSemStateFiniteExact width (Nat × C) F := {bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
    stack := tail, localsSize := source.localsSize, handler := source.handler}
  have originalGuards := guards
  obtain ⟨get, bad, find, valid, cut⟩ := originalGuards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only at execution
  by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
  · rw [if_pos invalid] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)
  rw [if_neg invalid, popRun] at execution
  simp only at execution
  rw [if_pos domain] at execution
  refine ⟨gc, tail, popped, frame, gcKeys, tailKeys, handler, rfl, popRun, domain,
    invalid, execution, ?_⟩
  exact ih.1 xs args1 prog ss envs location returned bodyPost popped
    ⟨guards, nonzero, bodyRun, invalid, popRun, domain⟩

/-- The non-error whole handler Call derives exception location/domain
checks and its actual handler continuation run. Instantiating the original
guarded exception IH supplies its simulation, without any target run or
restoration premise. Flapjack source-case assembly, not the full comp_correct
handler theorem. -/
theorem sourceHandlerExceptionContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location value : WordLocW width)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost)) :
    ¬ location ≠ .loc h1 h2 ∧ sptDomainEqUnion bodyPost.locals envs.1 envs.2 ∧
    WordSemStateFiniteExact.evaluate handlerCode
      (WordSemStateFiniteExact.setVar handlerVar value bodyPost) = (result,sourcePost) ∧
    Seq.Simulation ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value bodyPost) := by
  have originalGuards := guards
  obtain ⟨get,bad,find,valid,cut⟩ := originalGuards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get,bad,Bool.false_eq_true,if_false,find,valid,cut] at execution
  rw [dif_neg nonzero,WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at execution
  simp only at execution
  by_cases invalid : location ≠ .loc h1 h2
  · rw [if_pos invalid] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)
  rw [if_neg invalid] at execution
  by_cases domain : sptDomainEqUnion bodyPost.locals envs.1 envs.2
  · rw [if_pos domain] at execution
    exact ⟨invalid,domain,execution,ih.2.1 xs args1 prog ss envs location value bodyPost
      ⟨guards,nonzero,bodyRun,invalid,domain⟩⟩
  · rw [if_neg domain] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)

/-- Connect actual return-copy/free/PopHandler execution to the saved tail
relation. The old callee stack relation, primitive mode flags and original
return-count bound derive all room and saved-slot facts; no restored target
relation is assumed. This is Flapjack normal-return factoring, not a narrowed
port of the full comp_correct case. -/
theorem restoreHandlerCallerTail {width : Nat} [NeZero width] {C F β γ : Type}
    (target : StackSemStateFiniteExact width C F) (register currentHandler : Nat)
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (savedHandler label1 label2 frameSize count : Nat)
    (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (f : β) (f' : γ) (continuation : HolProg width)
    (enabled : target.useStack = true) (storeEnabled : target.useStore = true)
    (countBound : count ≤ frameSize + 1)
    (relation : stackRel register currentHandler
      (.stackFrame size nonGc gc (some (savedHandler,label1,label2)) :: rest)
      (target.store.lookup .handler) (target.stack.drop (target.stackSpace + count))
      target.stack.length target.bitmaps (frameSize :: lens)) :
    ∃ copied : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (copyRetAuxNative register (frameSize + 4) count, target) =
        (none,copied) ∧
      let restored := poppedHandlerState
        {copied with stackSpace := copied.stackSpace + count} register
        (holEl 2 (target.stack.drop (target.stackSpace + count)))
      StackSemEvaluate.evaluate
        (.seq (copyRetAuxNative register (frameSize + 4) count)
          (.seq (.stackFree count) (popHandlerNative false (register,f,f') continuation)),target) =
        StackSemEvaluate.evaluate (continuation,restored) ∧
      stackRel register savedHandler rest (restored.store.lookup .handler)
        (restored.stack.drop (restored.stackSpace + (frameSize + 1)))
        restored.stack.length restored.bitmaps lens ∧
      restored.store.eraseEq .handler = target.store.eraseEq .handler ∧
      restored.stackSpace = target.stackSpace + count + 3 ∧
      restored.clock = target.clock ∧ restored.ffi = target.ffi := by
  have available := stackRelConsLenSome register currentHandler size nonGc gc
    savedHandler label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop (target.stackSpace + count)) target.stack.length target.bitmaps
    frameSize lens relation
  simp only [List.length_drop] at available
  have room : frameSize + 4 ≤ target.stack.length - (target.stackSpace + count) := available
  obtain ⟨copied,copyRun,stack,regs,state,length,space,tail,registers,untouched,values⟩ :=
    CallReturnEval.evaluateCopyRetAux register (frameSize + 4) count target
      ⟨enabled,by omega,room⟩
  obtain ⟨copiedAgain,copyAgain,restoreRun,_,_,_⟩ := evaluateHandlerReturnRestore
    target register (frameSize + 1) count f f' continuation enabled storeEnabled
      (by omega) countBound
  have same : copiedAgain = copied := by
    have normalized : StackSemEvaluate.evaluate
        (copyRetAuxNative register (frameSize + 4) count,target) = (none,copiedAgain) := by
      simpa only [show frameSize + 1 + 3 = frameSize + 4 by omega] using copyAgain
    exact congrArg Prod.snd (normalized.symm.trans copyRun)
  subst copiedAgain
  let restored := poppedHandlerState
    {copied with stackSpace := copied.stackSpace + count} register
    (holEl 2 (target.stack.drop (target.stackSpace + count)))
  have oldTail := stackRelDropSome register currentHandler size nonGc gc
    savedHandler label1 label2 rest (target.store.lookup .handler)
    (target.stack.drop (target.stackSpace + count)) target.stack.length target.bitmaps
    frameSize lens relation
  have dropEq : restored.stack.drop (restored.stackSpace + (frameSize + 1)) =
      (target.stack.drop (target.stackSpace + count)).drop (frameSize + 4) := by
    simpa only [restored,poppedHandlerState,List.drop_drop,state,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail
  refine ⟨copied,copyRun,?_,?_,?_,?_,?_,?_⟩
  · simpa only [show frameSize + 1 + 3 = frameSize + 4 by omega] using restoreRun
  · change stackRel register savedHandler rest (restored.store.lookup .handler)
      (restored.stack.drop (restored.stackSpace + (frameSize + 1)))
      restored.stack.length restored.bitmaps lens
    rw [dropEq]
    simpa only [restored,poppedHandlerState,state,HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL,if_true,length] using oldTail
  · simpa only [state] using poppedStoreErase
      {copied with stackSpace := copied.stackSpace + count} register
      (holEl 2 (target.stack.drop (target.stackSpace + count)))
  · simp only [poppedHandlerState,state]
  · simp only [poppedHandlerState,state]
  · simp only [poppedHandlerState,state]

/-- The literal copy_ret wrapper has exactly the explicit copy/free
execution, including zero return values. The zero free is discharged from
primitive stack flags/bounds, rather than changing the native program.
Flapjack evaluator factoring with no separate HOL declaration. -/
theorem evaluateHandlerCopyRetNative {width : Nat} [NeZero width] {C F α γ : Type}
    (target : StackSemStateFiniteExact width C F) (register frame : Nat)
    (unused : γ) (values : List α) (continuation : HolProg width)
    (enabled : target.useStack = true) (bound : target.stackSpace ≤ target.stack.length) :
    StackSemEvaluate.evaluate
      (copyRetNative false true (register,frame,unused) values continuation,target) =
    StackSemEvaluate.evaluate
      (.seq (copyRetAuxNative register (frame + 3)
        (Compiler.Backend.WordToStack.numStackRet register values))
        (.seq (.stackFree (Compiler.Backend.WordToStack.numStackRet register values))
          continuation),target) := by
  by_cases zero : Compiler.Backend.WordToStack.numStackRet register values = 0
  · simp only [copyRetNative,zero,if_true,copyRetAuxNative]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_stackFree]
    simp [enabled,Nat.not_lt.mpr bound]
    simp only [← enabled]
  · simp only [copyRetNative,zero,if_false,seqStackFreeNative,
      Compiler.Backend.WordToStack.handlerSlots,Bool.false_eq_true,if_true]

/-- Original source conventions/maximum and the callee saved-frame relation
suffice to execute the literal native copy_ret/PopHandler wrapper and recover
the caller tail/store. Zero caller frames and zero return counts are retained.
This factors the actual normal-return target code; no target execution or
restored relation is supplied. Full caller locals/state_rel assembly remains
separate and this declaration has no separate HOL original. -/
theorem restoreHandlerCallerTailNative {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (k frame localsFrame currentHandler : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (size : Option Nat) (nonGc gc : List (Nat × WordLocW width))
    (savedHandler : Nat) (rest : List (WordSemStackFrame width)) (lens : List Nat)
    (continuation : HolProg width)
    (enabled : target.useStack = true) (storeEnabled : target.useStore = true)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2 * localsFrame + 2 * k)
    (frameShape : if localsFrame = 0 then frame = 0 else frame = localsFrame + 1)
    (relation : stackRel k currentHandler
      (.stackFrame size nonGc gc (some (savedHandler,h1,h2)) :: rest)
      (target.store.lookup .handler)
      (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
      target.stack.length target.bitmaps (localsFrame :: lens)) :
    ∃ copied : StackSemStateFiniteExact width C F,
      let count := Compiler.Backend.WordToStack.numStackRet k values
      let restored := poppedHandlerState
        {copied with stackSpace := copied.stackSpace + count} k
        (holEl 2 (target.stack.drop (target.stackSpace + count)))
      StackSemEvaluate.evaluate
        (copyRetNative false true (k,frame,localsFrame) values
          (popHandlerNative false (k,frame,localsFrame) continuation),target) =
        StackSemEvaluate.evaluate (continuation,restored) ∧
      stackRel k savedHandler rest (restored.store.lookup .handler)
        (restored.stack.drop (restored.stackSpace + (localsFrame + 1)))
        restored.stack.length restored.bitmaps lens ∧
      restored.store.eraseEq .handler = target.store.eraseEq .handler ∧
      restored.stackSpace = target.stackSpace + count + 3 ∧
      restored.clock = target.clock ∧ restored.ffi = target.ffi := by
  let count := Compiler.Backend.WordToStack.numStackRet k values
  have countFits := handlerReturnCountBound k frame localsFrame values names retCode handlerCode
    l1 l2 h1 h2 handlerVar dest args conventions maximum frameShape
  have frameBound : frame ≤ localsFrame + 1 := by split at frameShape <;> omega
  have bound := stackRelConsLenSome k currentHandler size nonGc gc savedHandler h1 h2 rest
    (target.store.lookup .handler) (target.stack.drop (target.stackSpace + count))
    target.stack.length target.bitmaps localsFrame lens relation
  simp only [List.length_drop] at bound
  obtain ⟨copied,copyRun,restoreRun,tail,store,space,clock,ffi⟩ := restoreHandlerCallerTail
    target k currentHandler size nonGc gc savedHandler h1 h2 localsFrame count rest lens
    frame localsFrame continuation enabled storeEnabled (by dsimp [count]; omega) relation
  have offset : copyRetAuxNative (width := width) k (frame + 3) count =
      copyRetAuxNative k (localsFrame + 4) count := by
    by_cases zero : count = 0
    · simp only [zero,copyRetAuxNative]
    · have nonzero : localsFrame ≠ 0 := by
        intro empty
        have zeroFrame : frame = 0 := by simpa only [empty,ite_true] using frameShape
        dsimp [count] at zero
        omega
      have exactFrame : frame = localsFrame + 1 := by
        simpa only [if_neg nonzero] using frameShape
      rw [exactFrame]
  refine ⟨copied,?_,tail,store,space,clock,ffi⟩
  rw [evaluateHandlerCopyRetNative target k frame localsFrame values
    (popHandlerNative false (k,frame,localsFrame) continuation) enabled (by omega),offset]
  exact restoreRun

/-- Unconditional clock transport through the entire actual handler entry
prelude, including destination, saved caller frame, PushHandler and argument
move. All failure outcomes are retained; no bounds, success or target-run
premise is needed. This is Flapjack composition of reviewed original clock
laws for the eventual whole-call assembly. -/
theorem completeHandlerPreludeClockFree {width : Nat} [NeZero width] {C F : Type}
    (k frame localsFrame h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (names : WordLangCutsetsHOL) (bs bsPost : AppList (BitVec width) × Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (destinationCompile : callDestNative dest args (k,frame,localsFrame) =
      (destinationCode,destination))
    (savedCompile : wLiveNative names bs (k,frame,localsFrame) = (savedCode,bsPost)) :
    CallReturnEval.ClockFree (C := C) (F := F)
      (.seq destinationCode (.seq savedCode
        (.seq (pushHandlerNative (width := width) false h1 h2 (k,frame,localsFrame))
          (stackHandlerArgsNative (width := width) false destination (args.length + 1) (k,frame,localsFrame))))) := by
  have destinationClock : CallReturnEval.ClockFree (C := C) (F := F) destinationCode := by
    intro target clock
    simpa only [Prod.map,id_eq] using CallReturnEval.evaluateCallDestClock
      dest args k frame localsFrame destinationCode destination target clock destinationCompile
  have savedClock : CallReturnEval.ClockFree (C := C) (F := F) savedCode := by
    intro target clock
    exact CallReturnEval.evaluateWLiveClock (C := C) (F := F)
      (k,frame,localsFrame) clock names target savedCode bs bsPost savedCompile
  have pushClock : CallReturnEval.ClockFree (C := C) (F := F)
      (pushHandlerNative (width := width) false h1 h2 (k,frame,localsFrame)) := by
    intro target clock
    simpa only [Prod.map,id_eq] using
      evaluatePushHandlerClock target h1 h2 k frame localsFrame clock
  have argumentsClock : CallReturnEval.ClockFree (C := C) (F := F)
      (stackHandlerArgsNative (width := width) false destination (args.length + 1) (k,frame,localsFrame)) := by
    rw [stackHandlerArgsF]
    exact CallReturning.stackArgumentsClockFree k (frame + 3) (localsFrame + 3)
      destination (args.length + 1)
  exact CallReturnEval.clockFree_seq _ _ destinationClock
    (CallReturnEval.clockFree_seq _ _ savedClock
      (CallReturnEval.clockFree_seq _ _ pushClock argumentsClock))

/-- Construct the actual native zero-clock handler Call under the original
successful header/argument-space split. Callee dispatch is derived from the
source guards; the whole compiled Call times out before entering its body,
and the actual source evaluate_def clause proves the complete clock/FFI
compCorrectResult. No supplied target run or body/result relation is needed.
This is untagged Flapjack branch assembly; the full handler case is unfinished. -/
theorem compiledHandlerCallTimeout {width : Nat} [NeZero width] {C F : Type}
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
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (handlerBitmaps : AppList (BitVec width)) (handlerIndex : Nat) (handlerTarget : HolProg width)
    (handlerCompile : compNative ac false handlerCode (finalBitmaps,finalIndex) (k,f,frame) =
      (handlerTarget,(handlerBitmaps,handlerIndex)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (compiled : HolProg width)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) (bs, n) (k, f, frame) =
      (compiled, (handlerBitmaps, handlerIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace - 3)
    (zero : source.clock = 0)
    (bitmapPrefix : (appListAppend handlerBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ targetPost : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (compiled, target) = (some .timeOut, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result
        (some .timeOut) lens := by
  have handlerPrefix := (compImpIsPrefix ac false handlerCode (finalBitmaps,finalIndex)
    (k,f,frame) handlerTarget (handlerBitmaps,handlerIndex) handlerCompile).trans bitmapPrefix
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps,savedIndex)
    (k,f,frame) returnCode (finalBitmaps,finalIndex) returnCompile).trans handlerPrefix
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleeBsPost,
    calleeIndex,calleeIndexPost,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,calleeBitmapLength,
    calleeBitmapBound,calleeBitmapPrefix,calleeLocalsSize,found,savedLookup,headerState,
    savedSpace,movedClock,movedFfi⟩ := prepareHandlerCalleeDestination ac k f frame
      values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix room location space
  have targetClock : target.clock = 0 := related.1.symm.trans zero
  have movedZero : moved.clock = 0 := movedClock.trans targetClock
  have callRun : StackSemEvaluate.evaluate
      (.call (some (.seq .skip (copyRetNative false true (k, f, frame) values
          (popHandlerNative false (k,f,frame) returnCode)),
        0, l1, l2)) destination (some (handlerTarget,h1,h2)), moved) =
      (some .timeOut, StackSemStateOps.emptyEnv moved) := by
    rw [StackSemEvaluate.evaluate_call]
    simp only
    rw [found]
    simp only
    rw [if_pos (show moved.clock = 0 from movedZero)]
  simp only [compNative, destinationCompile, savedCompile, returnCompile,handlerCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at compilation
  obtain ⟨rfl, _⟩ := compilation
  refine ⟨StackSemStateOps.emptyEnv moved, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, pushRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, moveRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    exact callRun
  · obtain ⟨get, bad, find, valid, cut⟩ := guards
    rw [WordSemStateFiniteExact.evaluate] at execution
    simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
    rw [dif_pos zero] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
      not_true_eq_false, ↓reduceIte]
    exact ⟨movedFfi.symm,zero.trans movedZero.symm⟩

end Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
