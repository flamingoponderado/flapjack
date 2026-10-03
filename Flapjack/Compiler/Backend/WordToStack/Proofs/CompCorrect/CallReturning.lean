import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnEval
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnSupport
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnStackMoveClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.EvaluateWLive
import Flapjack.Pancake.WordConvs.MaxVarIntro

namespace Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Flapjack factoring of the original returning-call source guards. It has
no separate HOL declaration: these are the actual evaluate_def tests before
callee evaluation, not successful target execution assumptions. -/
def SourceGuards {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)) : Prop :=
  WordSemStateFiniteExact.getVars args source = some xs ∧
  ¬ wordSemBadDestArgs dest args = true ∧
  wordSemFindCode dest (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs)
    source.code source.stackSize = some (args1, prog, ss) ∧
  ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup) ∧
  wordSemCutEnvs names source.locals = some envs

/-- Flapjack factoring of the two original evaluate_ind hypotheses for the
no-handler returning-call branch. The continuation premise uses the actual
source callee Result, location/length checks, successful pop_env and domain
union check. Neither premise assumes a target evaluation or postrelation.
There is no separate HOL declaration for this factoring. -/
def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values ys popped)) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    Seq.Simulation ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))))

/-- Flapjack proof factoring of the original source guard elimination at
word_to_stackProofScript.sml8170 onward. The guards are derived from the
actual non-error source run, retaining timeout, resource, normal-return and
exception outcomes. This is infrastructure for the full case, not a HOL
comp_correct port or a target simulation theorem. -/
theorem sourceGuardsOfNotError {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error) :
    ∃ xs args1 prog ss envs,
      SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs := by
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

/-- Flapjack factoring of the actual source conventions at the returning-call
setup. It is not a separate HOL declaration or a comp_correct port. -/
theorem returningConventions {width : Nat} [NeZero width]
    (k : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true) :
    postAllocConventionsHOL k retCode = true ∧
    args = (List.range args.length).map (fun index => 2 * (index + 1)) ∧
    values = (List.range values.length).map (fun index => 2 * (index + 1)) ∧
    (∀ key, sptDomain names.1 key → key % 2 = 0 ∧ k ≤ key / 2) ∧
    (∀ key, sptDomain names.2 key → key % 2 = 0 ∧ k ≤ key / 2) := by
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
  obtain ⟨allPhysical, allStack, allArguments⟩ := conventions
  rw [everyVarHOL] at allPhysical
  rw [everyStackVarHOL] at allStack
  rw [callArgConventionHOL] at allArguments
  simp only [Bool.and_eq_true, Bool.and_true, beq_iff_eq] at allPhysical allStack allArguments
  have physical : everyNameHOL isPhyVar names = true := by
    aesop (config := { enableSimp := false })
  have stackNames : everyNameHOL (fun name => decide (name ≥ 2 * k)) names = true := by
    aesop (config := { enableSimp := false })
  have retConvention : postAllocConventionsHOL k retCode = true := by
    simp only [postAllocConventionsHOL, Bool.and_eq_true]
    aesop (config := { enableSimp := false })
  have argsEq : args = (List.range args.length).map (fun index => 2 * (index + 1)) := by
    aesop (config := { enableSimp := false })
  have valuesEq : values = (List.range values.length).map (fun index => 2 * (index + 1)) := by
    aesop (config := { enableSimp := false })
  simp only [everyNameHOL, Bool.and_eq_true] at physical stackNames
  refine ⟨retConvention, argsEq, valuesEq, ?_, ?_⟩
  · intro key member
    have hm := (sptMemMapFstToAList names.1 key).mpr member
    have hp := List.all_eq_true.mp physical.1 key hm
    have hs := List.all_eq_true.mp stackNames.1 key hm
    simp only [isPhyVar, decide_eq_true_eq] at hp hs
    exact ⟨hp, by omega⟩
  · intro key member
    have hm := (sptMemMapFstToAList names.2 key).mpr member
    have hp := List.all_eq_true.mp physical.2 key hm
    have hs := List.all_eq_true.mp stackNames.2 key hm
    simp only [isPhyVar, decide_eq_true_eq] at hp hs
    exact ⟨hp, by omega⟩

/-- Flapjack factoring of the original saved-frame positivity derivation.
A real nonempty live cut-set supplies a key at least 2*k; the caller maximum
bounds that same key. No frame-positivity or successful wLive run is assumed. -/
theorem positiveCallerFrame {width : Nat} [NeZero width] {C F : Type}
    (k frame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k) :
    0 < frame := by
  classical
  obtain ⟨_, _, _, validNames, _⟩ := guards
  have nonempty : ¬ sptDomainEmpty names.1 := fun h => validNames (Or.inl h)
  have witness : ∃ key, sptDomain names.1 key := by
    by_contra none
    apply nonempty
    intro key member
    exact none ⟨key, member⟩
  obtain ⟨key, member⟩ := witness
  have nameFacts := (returningConventions k values names retCode l1 l2 dest args conventions).2.2.2.1
  have lower := (nameFacts key member).2
  have listed := (sptMemMapFstToAList names.1 key).mpr member
  have upper := maxList_ge_of_mem _ key listed
  rw [maxVarHOL] at maximum
  simp only [Flapjack.WordAlloc.max3Eq, cutsetsMaxHOL] at maximum
  omega

/-- Flapjack factoring of the actual saved-frame run in the original
returning-call prelude (8170-8242). The original caller convention and maximum
supply all live-name and frame-size obligations; the saved target run and
both state relations are proved, not assumed. This is setup infrastructure;
the full no-handler comp_correct case and its resource/result branches remain
separate unfinished work. There is no separate HOL declaration for this
specialization of evaluate_wLive. -/
theorem evaluateSavedFrame {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (savedCode : HolProg width)
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (compilation : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ savedTarget : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (savedCode, target) = (none, savedTarget) ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with
          locals := .ln, localsSize := some 0}
        savedTarget (frame :: lens) 0 ∧
      stateRel ac k f frame source savedTarget lens 0 ∧
      savedTarget.stack.length = target.stack.length ∧
      savedTarget.stackSpace = target.stackSpace ∧
      ∀ register, register ≠ k →
        StackSemStateOps.getVar register savedTarget = StackSemStateOps.getVar register target := by
  have positive := positiveCallerFrame k frame values names retCode l1 l2 dest args
    source xs args1 prog ss envs guards conventions maximum
  have shape : if frame = 0 then f = 0 else f = frame + 1 := by
    have relation := related
    unfold stateRel at relation
    aesop (config := { enableSimp := false })
  rw [if_neg (by omega)] at shape
  have fPositive : 1 ≤ f := by omega
  obtain ⟨_, _, _, firstNames, secondNames⟩ :=
    returningConventions k values names retCode l1 l2 dest args conventions
  obtain ⟨_, _, _, _, cut⟩ := guards
  exact EvaluateWLive.evaluateWLive ac k f frame names bs n savedCode bsPost nPost
    source target lens envs
    ⟨compilation, firstNames, secondNames, related, fPositive, cut,
      lengthBound, bitmapBound, bitmapPrefix⟩

/-- Flapjack factoring of the complete actual destination/saved-frame
prelude, including arbitrary extra target clock. Bitmap-prefix obligations
are derived from the actual continuation compilation and its final prefix;
no intermediate prefix or target run is assumed. The stack-argument allocation,
callee entry and all resource/return branches of the full case are still open. -/
theorem evaluatePrelude {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width))
    (n savedIndex finalIndex : Nat) (destinationCode savedCode returnCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
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
  have originalGuards := guards
  obtain ⟨get, bad, _, _, _⟩ := originalGuards
  obtain ⟨destinationTarget, destinationRun, destinationRelation,
    destinationLength, destinationSpace, _⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens destinationCode
      destination xs (some (values, names, retCode, l1, l2))
      ⟨bad, related, destinationCompile, get⟩
  obtain ⟨destinationBitmaps, _⟩ := CallDest.callDest_preserves dest args (k, f, frame)
    destinationCode destination target destinationTarget destinationCompile destinationRun
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex)
    (k, f, frame) returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨savedTarget, savedRun, pushedRelation, savedRelation, savedLength, savedSpace, _⟩ :=
    evaluateSavedFrame ac k f frame values names retCode l1 l2 dest args source
      destinationTarget lens xs args1 prog ss envs bs savedBitmaps n savedIndex savedCode
      guards destinationRelation conventions maximum savedCompile lengthBound
      (by rw [destinationBitmaps]; exact bitmapBound)
      (by rw [destinationBitmaps]; exact savedPrefix)
  refine ⟨savedTarget, ?_, pushedRelation, savedRelation,
    savedLength.trans destinationLength, savedSpace.trans destinationSpace⟩
  intro extra
  have destinationClock := CallReturnEval.evaluateCallDestClock dest args k f frame
    destinationCode destination target (target.clock + extra) destinationCompile
  rw [destinationRun] at destinationClock
  simp only [Prod.map, id_eq] at destinationClock
  have savedClock := CallReturnEval.evaluateWLiveClock (C := C) (F := F)
    (k, f, frame) (target.clock + extra) names destinationTarget savedCode
    (bs, n) (savedBitmaps, savedIndex) savedCompile
  rw [savedRun] at savedClock
  have sameClock : target.clock = savedTarget.clock := related.1.symm.trans savedRelation.1
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    destinationClock]
  simp only
  simpa only [sameClock] using savedClock

/-- Flapjack factoring of the argument-count identity used at HOL lines
8255–8269. The inserted return location and indirect destination removal are
computed from the actual source guards and call-destination compilation;
there is no independent HOL declaration for this case-local identity. -/
theorem stackArgumentCount {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (k f frame : Nat) (destinationCode : HolProg width)
    (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (compiled : callDestNative dest args (k, f, frame) =
      (destinationCode, destination)) :
    Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k =
      args1.length - k := by
  obtain ⟨get, bad, find, _, _⟩ := guards
  obtain ⟨_, _, _, indirect, direct⟩ := CallTail.findCode_facts dest _
    source.code source.stackSize args1 prog ss find
  have length := WordSemStateFiniteExact.getVarsLengthLemma args source xs get
  cases dest with
  | none =>
    have nonempty : args ≠ [] := by
      rintro rfl
      simp [wordSemBadDestArgs] at bad
    have nonzero : ¬ args.length = 0 := by simpa using nonempty
    simp only [callDestNative, dif_neg nonzero, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl⟩ := compiled
    rw [indirect rfl]
    simp only [Compiler.Backend.WordToStack.stackArgCount, wordSemAddRetLoc,
      List.length_dropLast, List.length_cons, length]
  | some p =>
    simp only [callDestNative, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl⟩ := compiled
    rw [direct (by simp)]
    simp only [Compiler.Backend.WordToStack.stackArgCount, wordSemAddRetLoc,
      List.length_cons, length]

end Flapjack.WordToStackProofs.CompCorrect.CallReturning
