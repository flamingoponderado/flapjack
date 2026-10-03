import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.StackProps.EvaluateMono
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnEval
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnSupport
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallReturnStackMoveClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.EvaluateWLive
import Flapjack.Pancake.WordConvs.MaxVarIntro
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.FilterBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeInsertWf
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveLength
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnLabels

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

/-- Flapjack case-local frame bound used before the actual stack move.
It derives the move's offset bound from the original caller maximum and
shifted GENLIST argument convention; no target-run assumption is introduced. -/
theorem stackArgumentFrameBound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source
      xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (compiled : callDestNative dest args (k, f, frame) =
      (destinationCode, destination)) :
    Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ f := by
  have positive := positiveCallerFrame k frame values names retCode l1 l2 dest args
    source xs args1 prog ss envs guards conventions maximum
  have shape : if frame = 0 then f = 0 else f = frame + 1 := by
    unfold stateRel at related
    aesop (config := { enableSimp := false })
  rw [if_neg (by omega)] at shape
  have argsEq := (returningConventions k values names retCode l1 l2 dest args conventions).2.1
  have argBound : args.length ≤ frame + k := by
    rcases Nat.eq_zero_or_pos args.length with empty | nonempty
    · omega
    · have member : 2 * ((args.length - 1) + 1) ∈ args := by
        have mapped : 2 * ((args.length - 1) + 1) ∈
            (List.range args.length).map (fun index => 2 * (index + 1)) :=
          List.mem_map.mpr ⟨args.length - 1, List.mem_range.mpr (by omega), rfl⟩
        rwa [← argsEq] at mapped
      have upper := maxList_ge_of_mem args _ member
      rw [maxVarHOL] at maximum
      simp only [Flapjack.WordAlloc.max3Eq] at maximum
      omega
  cases destination <;>
    simp only [Compiler.Backend.WordToStack.stackArgCount] <;> omega

/-- Flapjack case-local execution of StackArgs after the original resource
split. The offset and memory bounds are the checked caller bounds. This
lemma proves the actual allocation/move run and retains the stack/register
observations needed for callee state_rel; it is not the full Call simulation. -/
theorem evaluateStackArguments {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (destination : Sum Nat Nat) (argCount : Nat)
    (target : StackSemStateFiniteExact width C F)
    (useStack : target.useStack = true)
    (frameBound : target.stackSpace + f ≤ target.stack.length)
    (moveBound : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤ f)
    (space : Compiler.Backend.WordToStack.stackArgCount destination argCount k ≤ target.stackSpace) :
    let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
    ∃ (moved : StackSemStateFiniteExact width C F)
      (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
      StackSemEvaluate.evaluate (stackArgsNative destination argCount (k, f, frame), target) =
        (none, moved) ∧
      moved = {target with stackSpace := target.stackSpace - count, stack := stack, regs := regs} ∧
      (∀ register, register ≠ k →
        StackSemStateOps.getVar register moved = StackSemStateOps.getVar register target) ∧
      target.stack.length = stack.length ∧
      moved.stackSpace = target.stackSpace - count ∧
      stack.drop (moved.stackSpace + count) = target.stack.drop target.stackSpace ∧
      (∀ index, index < count →
        holEl (index + f) (target.stack.drop (target.stackSpace - count)) =
          holEl index (stack.drop (target.stackSpace - count))) := by
  dsimp only
  set count := Compiler.Backend.WordToStack.stackArgCount destination argCount k with countDef
  let allocated : StackSemStateFiniteExact width C F :=
    {target with stackSpace := target.stackSpace - count}
  obtain ⟨moved, run, stack, regs, state, registers, length, movedSpace, tail, slots⟩ :=
    CallReturnEval.evaluateStackMove k count 0 allocated f
      ⟨useStack, by dsimp [allocated]; omega, moveBound⟩
  refine ⟨moved, stack, regs, ?_, state, registers, length, movedSpace, ?_, ?_⟩
  · rw [stackArgsNative, CallReturnEval.evaluateStackMoveSeq,
      StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_stackAlloc, if_neg (by simp [useStack]), if_neg (by simpa only using Nat.not_lt.mpr space)]
    simp only
    exact run
  · simpa only [allocated, Nat.add_zero, Nat.sub_add_cancel space] using tail
  · simpa only [movedSpace, allocated, Nat.add_zero] using slots

/-- Flapjack case-local failure equation for the other original StackArgs
resource branch. It retains the actual Halt 2/empty_env outcome; proving the
source event-prefix and exceeded-resource conclusion remains part of the
unfinished full Call case. -/
theorem evaluateStackArgumentsInsufficient {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (destination : Sum Nat Nat) (argCount : Nat)
    (target : StackSemStateFiniteExact width C F)
    (useStack : target.useStack = true)
    (space : target.stackSpace <
      Compiler.Backend.WordToStack.stackArgCount destination argCount k) :
    StackSemEvaluate.evaluate (stackArgsNative destination argCount (k, f, frame), target) =
      (some (.halt (.word (BitVec.ofNat width 2))), StackSemStateOps.emptyEnv target) := by
  rw [stackArgsNative, CallReturnEval.evaluateStackMoveSeq,
    StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    StackSemEvaluate.evaluate_stackAlloc, if_neg (by simp [useStack]), if_pos space]

/-- Flapjack factoring of the callee locals conjunct in the original
no-handler branch (8500–8574). The return Loc occupies key zero; other locals
are recovered from the original shifted source arguments and actual move
observations. This is a conjunct of the full state relation, not a narrowed
HOL comp_correct port. -/
theorem calleeLocals {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved moved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k callerSize callerFrame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ saved.stackSpace)
    (registers : ∀ register, register ≠ k →
      StackSemStateOps.getVar register moved = StackSemStateOps.getVar register saved)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (moved.stack.drop (saved.stackSpace - (args1.length - k))))
    (movedLength : moved.stack.length = saved.stack.length) :
    ∀ key value, sptLookup key (sptFromList2 args1) = some value →
      key % 2 = 0 ∧
      if key / 2 < k then (moved.regs.updateEq (0, .loc l1 l2)).lookup (key / 2) = some value
      else ((moved.stack.drop (saved.stackSpace - calleeSize)).take calleeSize)[calleeSize - 1 - (key / 2 - k)]? = some value ∧ key / 2 < k + calleeFrame := by
  obtain ⟨get, _, find, _, _⟩ := guards
  obtain ⟨_, _, _, indirect, direct⟩ := CallTail.findCode_facts dest _
    source.code source.stackSize args1 prog ss find
  have argPrefix : args1.IsPrefix (.loc l1 l2 :: xs) := by
    cases dest with
    | none => rw [indirect rfl]; exact List.dropLast_prefix _
    | some p => rw [direct (by simp)]; exact List.prefix_refl _
  have argsEq := (returningConventions k values names retCode l1 l2 dest args conventions).2.1
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
    have countSpace : args1.length - k ≤ saved.stackSpace := by omega
    have copyIndex : args1.length - k - 1 - (key / 2 - k) < args1.length - k := by omega
    have copied := slots _ copyIndex
    have callerAbsolute : saved.stackSpace + (callerSize - 1 - (key / 2 - k)) < saved.stack.length := by
      rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at callerSlot
      split at callerSlot
      · exact (List.getElem?_eq_some_iff.mp callerSlot).1
      · cases callerSlot
    have movedAbsolute : saved.stackSpace - calleeSize +
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
    have targetIndex : saved.stackSpace - (args1.length - k) +
        (args1.length - k - 1 - (key / 2 - k)) =
        saved.stackSpace - calleeSize + (calleeSize - 1 - (key / 2 - k)) := by omega
    simp only [sourceIndex, targetIndex] at copied
    rw [← copied]
    exact callerSlot

/-- Flapjack factoring of the full callee-entry state_rel construction at
HOL 8450–8574. Both input relations are established by the actual saved-frame
prelude; stack/register observations come from the actual argument move. The
entire callee relation is proved, including stack_size_rel and stack_rel.
This is case-local infrastructure, not a completed comp_correct port. -/
theorem calleeStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ saved.stackSpace)
    (registers : ∀ register, register ≠ k → regs.lookup register = saved.regs.lookup register)
    (slots : ∀ index, index < args1.length - k →
      holEl (index + callerSize) (saved.stack.drop (saved.stackSpace - (args1.length - k))) =
        holEl index (stack.drop (saved.stackSpace - (args1.length - k))))
    (stackLength : stack.length = saved.stack.length)
    (stackTail : stack.drop saved.stackSpace = saved.stack.drop saved.stackSpace) :
    stateRel ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      {saved with
        clock := saved.clock - 1, stackSpace := saved.stackSpace - calleeSize,
        stack := stack, regs := regs.updateEq (0, .loc l1 l2)}
      (callerFrame :: lens) 0 := by
  let cleared := {WordSemStateFiniteExact.pushEnv envs none source with
    locals := .ln, localsSize := some 0}
  have calleeSource : WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)) =
      WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock cleared) := by
    rfl
  rw [calleeSource]
  change stateRel ac k 0 0 cleared saved (callerFrame :: lens) 0 at pushedRelation
  unfold stateRel at pushedRelation
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, _, _,
    resource, oldStack, _⟩ := pushedRelation
  unfold stateRel
  refine ⟨?_, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, ?_, ?_,
    calleeShape, wfFromList2 args1, ?_, ?_, ?_⟩
  · show cleared.clock - 1 = saved.clock - 1
    rw [g1]
  · show saved.stackSpace - calleeSize + calleeSize ≤ stack.length
    omega
  · show stack.length < 2 ^ width
    omega
  · change stackSizeRel calleeSize ss cleared.stackLimit
      (wordSemOptionMax cleared.stackMax (wordSemOptionAdd (wordSemStackSize cleared.stack) ss))
      cleared.stack stack (saved.stackSpace - calleeSize) 0
    obtain ⟨_, limit, maximum⟩ := resource
    refine ⟨fun _ => calleeLocalsSize, by simpa only [stackLength] using limit, ?_⟩
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
  · change stackRel k cleared.handler cleared.stack (saved.store.lookup .handler)
      ((stack.drop (saved.stackSpace - calleeSize + 0)).drop calleeSize)
      stack.length saved.bitmaps (callerFrame :: lens)
    rw [List.drop_drop, Nat.add_zero, Nat.sub_add_cancel space, stackTail, stackLength]
    simpa only [Nat.add_zero, Nat.add_zero, List.drop_zero] using oldStack
  · exact calleeLocals ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved {saved with stack := stack, regs := regs} lens
      xs args1 prog ss envs guards callerRelation conventions calleeShape argumentBound space
      registers slots stackLength

/-- Flapjack case-local extraction of the actual compiled callee from the
original find_code guard and state_rel code conjunct. Compiler frame bounds,
callee conventions and bitmap obligations are derived, not assumed. -/
theorem calleeCompilation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k callerSize callerFrame source target lens 0) :
    ∃ (location : Nat) (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
      (body : HolProg width) (calleeSize calleeFrame : Nat),
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location target.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) = (body, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k := by
  obtain ⟨_, _, find, _, _⟩ := guards
  obtain ⟨location, sourceCode, sourceSize, _, _⟩ := CallTail.findCode_facts dest _
    source.code source.stackSize args1 prog ss find
  unfold stateRel at related
  obtain ⟨_, _, _, _, _, _, _, _, _, kPositive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, code, _⟩ := related
  obtain ⟨conventions, flat, bs, n, bsPost, nPost, calleeSize, stackProg,
    compiled, bitmapLength, bitmapBound, bitmapPrefix, targetCode, localSize⟩ :=
    code location prog args1.length sourceCode
  simp only [compileProgNative] at compiled
  set calleeFrame := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) with frameDef
  rcases bodyCompile : compNative ac false prog (bs, n)
      (k, if calleeFrame = 0 then 0 else calleeFrame + 1, calleeFrame) with ⟨body, bitmaps⟩
  rw [bodyCompile] at compiled
  simp only [Prod.mk.injEq] at compiled
  obtain ⟨rfl, sizeDef, bitmapsDef⟩ := compiled
  subst bitmaps
  rw [sizeDef] at targetCode bodyCompile
  have shape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1 := by
    split_ifs at sizeDef ⊢ <;> omega
  have argumentBound : args1.length - k ≤ calleeFrame := by
    rw [frameDef]
    exact Nat.le_max_right _ _
  have maximumBound : maxVarHOL prog < 2 * calleeFrame + 2 * k := by
    have variableBound := Nat.le_max_left (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
    rw [← frameDef] at variableBound
    omega
  refine ⟨location, bs, bsPost, n, nPost, body, calleeSize, calleeFrame,
    sourceCode, targetCode, conventions, flat, bodyCompile, bitmapLength,
    bitmapBound, bitmapPrefix, ?_, shape, argumentBound, maximumBound⟩
  rwa [sourceSize]

/-- Flapjack factoring of the actual successful callee-entry execution.
The prelude relations and compiler frame facts are derived above; the sole
space guard is the original resource split. Both StackArgs and the callee
frame allocation are executed here and the complete callee state_rel is
established. The full result/resource Call assembly remains unfinished. -/
theorem enterCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
        (k, callerSize, callerFrame), saved) = (none, moved) ∧
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none, entry) ∧
      stateRel ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
        entry (callerFrame :: lens) 0 := by
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k callerSize callerFrame destinationCode destination guards destinationCompile
  have countCaller := stackArgumentFrameBound ac k callerSize callerFrame values names retCode
    l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination guards
    callerRelation conventions maximum destinationCompile
  have countCallee : args1.length - k ≤ calleeSize := by
    split_ifs at calleeShape <;> omega
  have useStack : saved.useStack = true := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  have stackBound : saved.stackSpace + callerSize ≤ saved.stack.length := by
    unfold stateRel at callerRelation
    aesop (config := { enableSimp := false })
  obtain ⟨moved, stack, regs, moveRun, movedState, registers, stackLength, movedSpace, tail, slots⟩ :=
    evaluateStackArguments k callerSize callerFrame destination (args.length + 1) saved
      useStack stackBound countCaller (by omega)
  rw [countEq] at movedState movedSpace tail slots
  subst moved
  let entry : StackSemStateFiniteExact width C F := {saved with
    clock := saved.clock - 1, stackSpace := saved.stackSpace - calleeSize,
    stack := stack, regs := regs.updateEq (0, .loc l1 l2)}
  refine ⟨_, entry, moveRun, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_stackAlloc,
      if_neg (by simp [StackSemStateOps.setVar, StackSemStateOps.decClock, useStack]),
      if_neg (by
        change ¬ saved.stackSpace - (args1.length - k) < calleeSize - (args1.length - k)
        omega)]
    simp only [StackSemStateOps.setVar, StackSemStateOps.decClock]
    have spaceEq : saved.stackSpace - (args1.length - k) -
        (calleeSize - (args1.length - k)) = saved.stackSpace - calleeSize := by omega
    rw [spaceEq]
  · exact calleeStateRel ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs stack regs guards callerRelation
      pushedRelation conventions calleeShape calleeLocalsSize argumentBound space
      registers slots stackLength.symm (by
        change stack.drop (saved.stackSpace - (args1.length - k) + (args1.length - k)) = _ at tail
        rw [Nat.sub_add_cancel (show args1.length - k ≤ saved.stackSpace by omega)] at tail
        exact tail)

/-- Flapjack factoring of the original indirect destination register bound.
The shifted caller argument convention supplies a positive physical register;
wReg2 chooses that register below k or the distinct k+1 scratch register.
There is no separate HOL declaration for this case-local fact. -/
theorem destinationRegisterBound {width : Nat} [NeZero width]
    (k f frame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (code : HolProg width) (destination : Sum Nat Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (compiled : callDestNative dest args (k, f, frame) = (code, destination)) :
    ∀ register, destination = .inr register → register ≠ 0 ∧ register ≠ k := by
  have argsEq := (returningConventions k values names retCode l1 l2 dest args conventions).2.1
  cases dest with
  | some location =>
    simp only [callDestNative, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl⟩ := compiled
    intro register impossible
    cases impossible
  | none =>
    by_cases empty : args.length = 0
    · simp only [callDestNative, dif_pos empty, Prod.mk.injEq] at compiled
      obtain ⟨_, rfl⟩ := compiled
      intro register impossible
      cases impossible
    have nonempty : args ≠ [] := by simpa using empty
    simp only [callDestNative, dif_neg empty, Prod.mk.injEq] at compiled
    obtain ⟨_, rfl⟩ := compiled
    have member : args.getLast nonempty ∈ args := List.getLast_mem nonempty
    have mappedMember := Eq.mp (congrArg (fun items => args.getLast nonempty ∈ items) argsEq) member
    obtain ⟨index, _, last⟩ := List.mem_map.mp mappedMember
    intro register equal
    have equalRegister := Sum.inr.inj equal
    simp only [Compiler.Backend.WordToStackRegFormat.wReg2] at equalRegister
    split at equalRegister
    · simp only at equalRegister
      rw [← equalRegister, ← last]
      omega
    · simp only at equalRegister
      omega

/-- Flapjack factoring of lookup preservation in the original returning-call
prelude. Code growth preserves existing callee entries, moving arguments only
changes register k, and the call clears register zero. The actual compiled
indirect destination is distinct from both, as proved above. This is not a
HOL pass-correctness statement or a target-run assumption. -/
theorem findCodePreserved {width : Nat} [NeZero width] {α : Type}
    (k : Nat) (destination : Sum Nat Nat)
    (oldRegs newRegs : HolFiniteMapExact Nat (WordLocW width))
    (oldCode newCode : Spt α) (program : α)
    (avoids : ∀ register, destination = .inr register → register ≠ 0 ∧ register ≠ k)
    (registers : ∀ register, register ≠ k → newRegs.lookup register = oldRegs.lookup register)
    (growth : sptSubspt oldCode newCode)
    (found : StackSemControl.findCode destination oldRegs oldCode = some program) :
    StackSemControl.findCode destination (newRegs.eraseEq 0) newCode = some program := by
  cases destination with
  | inl location =>
    exact (sptSubsptLookup oldCode newCode).mp growth location program found
  | inr register =>
    obtain ⟨notZero, notScratch⟩ := avoids register rfl
    simp only [StackSemControl.findCode]
    rw [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, if_neg notZero, registers register notScratch]
    simp only [StackSemControl.findCode] at found
    cases lookupEq : oldRegs.lookup register with
    | none => simp [lookupEq] at found
    | some value =>
      cases value with
      | word word => simp [lookupEq] at found
      | loc location offset =>
        cases offset with
        | zero =>
          simp only [lookupEq] at found ⊢
          exact (sptSubsptLookup oldCode newCode).mp growth location program found
        | succ offset => simp [lookupEq] at found

/-- Flapjack factoring of the actual destination/save/argument-move path
at HOL 8170–8388. Every target run and the final callee lookup are constructed
from the original source guards, compiler equations and caller relation.
The space condition is the original StackArgs resource split, whose failure
branch is retained separately. This is not the full comp_correct case. -/
theorem prepareCalleeDestination {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (calleeCode : HolProg width) (calleeSize : Nat)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      compileProgNative ac false prog args1.length k (calleeBs, calleeIndex) =
        (calleeCode, calleeSize, (calleeBsPost, calleeIndexPost)) ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode ∧
      saved.stackSpace = target.stackSpace ∧
      ∃ (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
        moved = {saved with
          stackSpace := saved.stackSpace -
            Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k,
          stack := stack, regs := regs} := by
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
    evaluateSavedFrame ac k f frame values names retCode l1 l2 dest args source destinationTarget lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex savedCode guards destinationRelation
      conventions maximum savedCompile bitmapLength (by rwa [destinationBitmaps])
      (by rwa [destinationBitmaps])
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have frameBound : saved.stackSpace + f ≤ saved.stack.length := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have moveBound := stackArgumentFrameBound ac k f frame values names retCode l1 l2 dest args
    source saved lens xs args1 prog ss envs destinationCode destination guards savedRelation
    conventions maximum destinationCompile
  obtain ⟨moved, stack, regs, moveRun, movedState, moveRegisters, _, _, _, _⟩ :=
    evaluateStackArguments k f frame destination (args.length + 1) saved useStack frameBound
      moveBound (by rw [savedSpace, destinationSpace]; exact space)
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono savedCode
    destinationTarget saved none savedRun).2
  have movedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, f, frame)) saved moved none moveRun).2
  have registers : ∀ register, register ≠ k → moved.regs.lookup register =
      destinationTarget.regs.lookup register := by
    intro register notScratch
    exact (moveRegisters register notScratch).trans (savedRegisters register notScratch)
  have finalFound := findCodePreserved k destination destinationTarget.regs moved.regs
    destinationTarget.code moved.code calleeCode
    (destinationRegisterBound k f frame values names retCode l1 l2 dest args destinationCode destination
      conventions destinationCompile)
    registers (sptSubsptTrans _ _ _ ⟨savedGrowth, movedGrowth⟩) found
  exact ⟨destinationTarget, saved, moved, calleeCode, calleeSize, calleeBs, calleeBsPost,
    calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun, savedRelation, pushedRelation,
    calleeCompile, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    finalFound, savedSpace.trans destinationSpace, stack, regs, movedState⟩

/-- Flapjack factoring of the original callee non-error obligation before
applying its guarded induction hypothesis (HOL 8575–8585). It is derived from
the actual whole source Call run, never supplied as an extra pass hypothesis. -/
theorem calleeNotError {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost calleePost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, calleePost)) : bodyResult ≠ some .error := by
  intro error
  rw [error] at bodyRun
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only [Prod.mk.injEq] at execution
  exact absurd execution.1.symm notError

/-- Flapjack factoring of the original source overflow fact for returning
Call allocation failures (HOL 8278–8294 and 8413–8427). The stack_size_rel of
the actual saved frame and compiler-derived callee local size imply that the
source call_env exceeds its stack limit. No source overflow is assumed. -/
theorem calleeStackOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerFrame calleeSize : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize) :
    let callee := WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))
    miscThe (callee.stackLimit + 1) callee.stackMax > callee.stackLimit := by
  let cleared := {WordSemStateFiniteExact.pushEnv envs none source with
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
theorem sourceCallOverflow {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerFrame calleeSize : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) :
    miscThe (sourcePost.stackLimit + 1) sourcePost.stackMax > sourcePost.stackLimit := by
  have overflow := calleeStackOverflow ac k callerFrame calleeSize source saved lens envs args1 ss
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
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
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

/-- Flapjack factoring of the full comp_correct result/resource conclusion
for returning-call allocation failure. The concrete empty_env target result
is Halt 2; its event prefix comes from the whole actual source evaluation and
its exceeded-resource fact is proved above. Failure clock/space cover both
original allocation points. This is a branch conclusion, not a full port. -/
theorem allocationFailureResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width)) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (failureClock failureSpace : Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (insufficient : saved.stackSpace < calleeSize)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) :
    compCorrectResult ac k callerSize callerFrame source sourcePost
      (StackSemStateOps.emptyEnv {saved with clock := failureClock, stackSpace := failureSpace})
      result (some (.halt (.word (BitVec.ofNat width 2)))) lens := by
  have overflow := sourceCallOverflow ac k callerFrame calleeSize values names retCode l1 l2
    dest args source sourcePost saved lens result xs args1 prog ss envs guards pushedRelation
    calleeLocalsSize insufficient execution
  have events := WordSemStateFiniteExact.evaluate_io_events_mono
    (.call (some (values, names, retCode, l1, l2)) dest args none) source result sourcePost execution
  unfold stateRel at callerRelation
  obtain ⟨_, _, _, ffi, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    dimension, _⟩ := callerRelation
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
    rw [ffi]
    exact events
  · cases maximum : sourcePost.stackMax with
    | none => simp
    | some value => simpa only [maximum, miscThe, Option.getD_some] using overflow

/-- Flapjack factoring of the original first allocation-failure branch.
The whole compiled no-handler Call executes its actual destination/save prelude
and fails in StackArgs before entering the callee. The exceeded-resource and
event-prefix conclusions are derived from the actual source evaluation; no
target execution or resource conclusion is assumed. This remains one branch
of the unfinished full comp_correct case, with no separate HOL declaration. -/
theorem compiledStackArgumentsFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
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
    (compiled : HolProg width)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (insufficient : target.stackSpace <
      Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ targetPost : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (compiled, target) =
        (some (.halt (.word (BitVec.ofNat width 2))), targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result
        (some (.halt (.word (BitVec.ofNat width 2)))) lens := by
  obtain ⟨saved, preludeRun, pushedRelation, savedRelation, _, savedSpace⟩ :=
    evaluatePrelude ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps finalBitmaps n savedIndex finalIndex
      destinationCode savedCode returnCode destination guards related conventions maximum
      destinationCompile savedCompile returnCompile lengthBound bitmapBound bitmapPrefix
  obtain ⟨_, _, _, _, _, _, calleeSize, calleeFrame, _, _, _, _, _, _, _, _,
    calleeLocalsSize, calleeShape, argumentBound, _⟩ :=
    calleeCompilation ac k f frame values names retCode l1 l2 dest args source saved lens
      xs args1 prog ss envs guards savedRelation
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have calleeSpace : saved.stackSpace < calleeSize := by
    rw [savedSpace]
    rw [countEq] at insufficient
    split_ifs at calleeShape <;> omega
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have argumentRun := evaluateStackArgumentsInsufficient k f frame destination (args.length + 1)
    saved useStack (by rwa [savedSpace])
  have branchResult := allocationFailureResult ac k f frame calleeSize values names retCode
    l1 l2 dest args source sourcePost saved lens result xs args1 prog ss envs
    saved.clock saved.stackSpace guards savedRelation pushedRelation calleeLocalsSize
    calleeSpace execution
  obtain ⟨get, bad, _, _, _⟩ := guards
  obtain ⟨destinationTarget, destinationRun, _, _, _, _⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens destinationCode
      destination xs (some (values, names, retCode, l1, l2))
      ⟨bad, related, destinationCompile, get⟩
  have savedRun := preludeRun 0
  simp only [Nat.add_zero] at savedRun
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    destinationRun] at savedRun
  simp only at savedRun
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at compilation
  obtain ⟨rfl, _⟩ := compilation
  refine ⟨StackSemStateOps.emptyEnv saved, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, argumentRun]
  · exact branchResult

/-- Flapjack execution factoring for the actual compile_prog callee allocation.
The original insufficient-space branch executes its StackAlloc and returns
Halt 2 before the compiled body. No target run is a premise, and there is no
separate HOL declaration for this case-local equation. -/
theorem compiledCalleeAllocationFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width))
    (argumentCount k : Nat) (bs bsPost : AppList (BitVec width) × Nat)
    (calleeCode : HolProg width) (calleeSize : Nat)
    (target : StackSemStateFiniteExact width C F)
    (compiled : compileProgNative ac false prog argumentCount k bs =
      (calleeCode, calleeSize, bsPost))
    (useStack : target.useStack = true)
    (insufficient : target.stackSpace < calleeSize - (argumentCount - k)) :
    StackSemEvaluate.evaluate (calleeCode, target) =
      (some (.halt (.word (BitVec.ofNat width 2))), StackSemStateOps.emptyEnv target) := by
  simp only [compileProgNative, Prod.mk.injEq] at compiled
  obtain ⟨rfl, size, _⟩ := compiled
  rw [← size] at insufficient
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    StackSemEvaluate.evaluate_stackAlloc, if_neg (by simp [useStack]), if_pos insufficient]

/-- Flapjack factoring of the original second allocation-failure branch.
After the actual destination/save/argument prelude, the compiled Call enters
its actual compiled callee and fails its frame allocation. The callee size
is derived from code_rel, and the original resource branch remains explicit.
The clock is positive here; timeout and successful-body/return branches remain
part of the unfinished full comp_correct case. No separate HOL declaration. -/
theorem compiledCalleeFrameFailure {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
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
    (compiled : HolProg width)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace)
    (nonzero : source.clock ≠ 0)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ calleeSize : Nat, ss.getD calleeSize = calleeSize ∧
      calleeSize = (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
        else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ∧
      (target.stackSpace < calleeSize →
        ∃ targetPost : StackSemStateFiniteExact width C F,
          StackSemEvaluate.evaluate (compiled, target) =
            (some (.halt (.word (BitVec.ofNat width 2))), targetPost) ∧
          compCorrectResult ac k f frame source sourcePost targetPost result
            (some (.halt (.word (BitVec.ofNat width 2)))) lens) := by
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex)
    (k, f, frame) returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, calleeCode, calleeSize, calleeBs, calleeBsPost,
    calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun, savedRelation,
    pushedRelation, calleeCompile, _, _, _, calleeLocalsSize, found, savedSpace,
    stack, regs, movedState⟩ :=
    prepareCalleeDestination ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix space
  have canonicalSize := calleeCompile
  simp only [compileProgNative, Prod.mk.injEq] at canonicalSize
  refine ⟨calleeSize, calleeLocalsSize, canonicalSize.2.1.symm, ?_⟩
  intro insufficient
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have savedClock : saved.clock = source.clock := savedRelation.1.symm
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  subst moved
  let moved : StackSemStateFiniteExact width C F := {saved with
    stackSpace := saved.stackSpace -
      Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k,
    stack := stack, regs := regs}
  let entry := StackSemStateOps.decClock (StackSemStateOps.setVar 0 (.loc l1 l2) moved)
  have calleeRun := compiledCalleeAllocationFailure ac prog args1.length k
    (calleeBs, calleeIndex) (calleeBsPost, calleeIndexPost) calleeCode calleeSize entry
    calleeCompile (by simpa only [entry, moved, StackSemStateOps.decClock,
      StackSemStateOps.setVar] using useStack) (by
        change saved.stackSpace -
          Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k <
          calleeSize - (args1.length - k)
        rw [countEq]
        rw [← savedSpace, countEq] at space
        rw [← savedSpace] at insufficient
        omega)
  have callRun : StackSemEvaluate.evaluate
      (.call (some (.seq .skip (copyRetNative false false (k, f, frame) values returnCode),
        0, l1, l2)) destination none, moved) =
      (some (.halt (.word (BitVec.ofNat width 2))), StackSemStateOps.emptyEnv entry) := by
    rw [StackSemEvaluate.evaluate_call]
    simp only
    rw [found]
    simp only
    rw [if_neg (by change saved.clock ≠ 0; rwa [savedClock]),
      StackSemEvaluateClock.fixClockEvaluate, calleeRun]
  have branchResult := allocationFailureResult ac k f frame calleeSize values names retCode
    l1 l2 dest args source sourcePost saved lens result xs args1 prog ss envs
    (saved.clock - 1) (saved.stackSpace -
      Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k)
    guards savedRelation pushedRelation calleeLocalsSize (by rwa [savedSpace]) execution
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at compilation
  obtain ⟨rfl, _⟩ := compilation
  refine ⟨StackSemStateOps.emptyEnv entry, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, moveRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    exact callRun
  · simpa only [entry, moved, StackSemStateOps.emptyEnv,
      StackSemStateOps.decClock, StackSemStateOps.setVar] using branchResult

/-- Flapjack factoring of the original guarded callee induction step
(8568–8620). Successful entry is executed above; all bitmap, label, compiler,
convention, frame and non-error obligations are discharged here. The original
IH supplies the complete clock-existential compCorrectResult for every body
outcome, including allocation failure. This is case-local assembly, not a
separate HOL declaration or a completed full Call port. -/
theorem simulateCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost)) :
    ∃ (calleeSize calleeFrame : Nat) (body : HolProg width) (location : Nat),
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      (calleeSize ≤ saved.stackSpace →
        ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens)) := by
  obtain ⟨location, bs, bsPost, n, nPost, body, calleeSize, calleeFrame,
    sourceCode, targetCode, bodyConventions, bodyFlat, bodyCompile, bitmapLength,
    bitmapBound, bitmapPrefix, calleeLocalsSize, calleeShape, argumentBound, bodyMaximum⟩ :=
    calleeCompilation ac k callerSize callerFrame values names retCode l1 l2 dest args
      source saved lens xs args1 prog ss envs guards callerRelation
  refine ⟨calleeSize, calleeFrame, body, location, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, ?_⟩
  intro space
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  obtain ⟨extraClock, targetPost, targetResult, targetRun, conclusion⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩ k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩
  have allocationClock : ∀ extra : Nat,
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
            clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (none, {entry with clock := entry.clock + extra}) := by
    intro extra
    have success := allocationRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_, rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc, if_neg disabled, if_neg insufficient]
    rfl
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
      (targetResult, targetPost) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extraClock]
    exact targetRun
  exact ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, conclusion⟩

/-- Flapjack assembly of the original zero-clock returning Call branch.
The argument allocation succeeds under the original space split, then the
actual compiled Call times out before entering the callee. The complete
source result and FFI/clock conclusion follow from its actual evaluate_def
clause. No separate HOL declaration; full-case assembly remains unfinished. -/
theorem compiledCallTimeout {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
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
    (compiled : HolProg width)
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace)
    (zero : source.clock = 0)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ targetPost : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (compiled, target) = (some .timeOut, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result
        (some .timeOut) lens := by
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex)
    (k, f, frame) returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, _, _, _, _, _, _, destinationRun, savedRun,
    moveRun, savedRelation, _, _, _, _, _, _, found, _, stack, regs, movedState⟩ :=
    prepareCalleeDestination ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile lengthBound bitmapBound
      savedPrefix space
  have savedClock : saved.clock = 0 := savedRelation.1.symm.trans zero
  have ffi : saved.ffi = source.ffi := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  subst moved
  let moved : StackSemStateFiniteExact width C F := {saved with
    stackSpace := saved.stackSpace -
      Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k,
    stack := stack, regs := regs}
  have callRun : StackSemEvaluate.evaluate
      (.call (some (.seq .skip (copyRetNative false false (k, f, frame) values returnCode),
        0, l1, l2)) destination none, moved) =
      (some .timeOut, StackSemStateOps.emptyEnv moved) := by
    rw [StackSemEvaluate.evaluate_call]
    simp only
    rw [found]
    simp only
    rw [if_pos (show moved.clock = 0 from savedClock)]
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at compilation
  obtain ⟨rfl, _⟩ := compilation
  refine ⟨StackSemStateOps.emptyEnv moved, ?_, ?_⟩
  · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
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
    exact ⟨ffi.symm, zero.trans savedClock.symm⟩

/-- Flapjack clock transport for the complete native StackArgs program.
Every success/error/resource outcome is retained, with no bounds or successful
run premise. This composes the original stack_move clock lemma with the
literal allocation clause; there is no separate HOL declaration. -/
theorem stackArgumentsClockFree {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (destination : Sum Nat Nat) (argCount : Nat) :
    CallReturnEval.ClockFree (C := C) (F := F)
      (stackArgsNative (width := width) destination argCount (k, f, frame)) := by
  let count := Compiler.Backend.WordToStack.stackArgCount destination argCount k
  have allocation : CallReturnEval.ClockFree (C := C) (F := F)
      (.stackAlloc count : HolProg width) := by
    intro target clock
    simp only [StackSemEvaluate.evaluate_stackAlloc]
    split_ifs <;> rfl
  have move : CallReturnEval.ClockFree (C := C) (F := F)
      (stackMoveNative (width := width) count 0 f k .skip) := by
    intro target clock
    simpa only [Prod.map, id_eq] using
      CallReturnStackMoveClock.evaluateStackMoveClock count 0 f k target clock
  intro target clock
  rw [stackArgsNative, CallReturnEval.evaluateStackMoveSeq,
    CallReturnEval.evaluateStackMoveSeq]
  exact CallReturnEval.clockFree_seq _ _ allocation move target clock

/-- Flapjack unconditional clock transport for the actual destination/save/
argument Call prelude. Compiler equations identify the actual programs;
all evaluator outcomes are retained. This case-local composition has no
separate HOL declaration and assumes no target run. -/
theorem completePreludeClockFree {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (dest : Option Nat) (args : List Nat)
    (names : WordLangCutsetsHOL) (bs bsPost : AppList (BitVec width) × Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (destinationCompile : callDestNative dest args (k, f, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names bs (k, f, frame) = (savedCode, bsPost)) :
    CallReturnEval.ClockFree (C := C) (F := F)
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, f, frame)))) := by
  have destClock : CallReturnEval.ClockFree (C := C) (F := F) destinationCode := by
    intro target clock
    simpa only [Prod.map, id_eq] using
      CallReturnEval.evaluateCallDestClock dest args k f frame destinationCode destination
        target clock destinationCompile
  have savedClock : CallReturnEval.ClockFree (C := C) (F := F) savedCode := by
    intro target clock
    exact CallReturnEval.evaluateWLiveClock (C := C) (F := F) (k, f, frame) clock names
      target savedCode bs bsPost savedCompile
  exact CallReturnEval.clockFree_seq _ _ destClock
    (CallReturnEval.clockFree_seq _ _ savedClock
      (stackArgumentsClockFree k f frame destination (args.length + 1)))

/-- Flapjack source-frame recovery at the original normal-return branch
(8660 onward). The full evaluate_stack_swap theorem derives the returned
caller's frame, its original non-GC values and size, and its preserved GC
keys from the actual callee Result run. The actual pop_env result is then
computed. No returned frame, restored locals, or target run is assumed;
there is no separate HOL declaration for this case-local recovery. -/
theorem returnedCallerFrame {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (source bodyPost : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (location : WordLocW width) (returned : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width)),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc none :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.handler ∧
      WordSemStateFiniteExact.popEnv bodyPost = some {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize} ∧
      sptDomainEqUnion
        (sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1))) envs.1 envs.2 := by
  have invariant := WordSemStackEq.evaluateStackSwap prog
    (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
  unfold WordSemStackEq.stackSwapPost at invariant
  rw [bodyRun] at invariant
  obtain ⟨keys, handler, _⟩ := invariant
  have pushedKeys : WordSemStackEq.sKeyEq
      (WordSemStateFiniteExact.pushEnv envs none
        (WordSemStateFiniteExact.decClock source)).stack bodyPost.stack := keys
  obtain ⟨_, _, _, _, _, popped, poppedRun, _, domain, _⟩ :=
    WordSemStackEq.pushEnvPopEnvSKeyEq envs none
      (WordSemStateFiniteExact.decClock source) bodyPost pushedKeys
  change WordSemStackEq.sKeyEq
    (.stackFrame source.localsSize (sptToAList envs.1)
      (wordSemEnvToList envs.2 source.permute).1 none :: source.stack) bodyPost.stack at keys
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
          stack := tail, localsSize := source.localsSize} := by
        rw [WordSemStateFiniteExact.popEnv, stackEq]
      have same := Option.some.inj (poppedRun.symm.trans popRun)
      subst popped
      refine ⟨gc, tail, rfl, gcKeys, tailKeys, handler, popRun, ?_⟩
      intro key
      have equality := congrFun domain key
      simpa only [sptMem, sptDomain, or_comm] using (Eq.to_iff equality.symm)

/-- Flapjack assembly of the source normal-return restoration and original
continuation IH (8660 onward). The actual non-error whole Call proves the
return location/length tests; evaluate_stack_swap and push/pop semantics prove
the saved frame and restored local-domain check. The continuation is the
actual source execution, and its simulation is the original guarded IH.
There is no target run or restored-state relation premise and no separate
HOL declaration; target return-copy/state_rel assembly remains unfinished. -/
theorem sourceReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
      (popped : WordSemStateFiniteExact width (Nat × C) F),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc none :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.handler ∧
      popped = {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize} ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptDomainEqUnion popped.locals envs.1 envs.2 ∧
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values returned popped) := by
  obtain ⟨gc, tail, frame, gcKeys, tailKeys, handler, popRun, domain⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  let popped : WordSemStateFiniteExact width (Nat × C) F := {bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
    stack := tail, localsSize := source.localsSize}
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

/-- Flapjack execution of the actual no-handler return copy/free wrapper.
This composes evaluate_copy_ret_aux and SeqStackFree, retaining cold fields,
registers, the frame tail, live frame slots and copied return slots. Its
bounds are the original copy-aux bounds, discharged from the callee result
relation in the Call case; no target run is assumed. There is no separate
HOL declaration for this wrapper specialization. -/
theorem evaluateReturnCopyFree {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (values : List Nat) (target : StackSemStateFiniteExact width C F)
    (useStack : target.useStack = true) (positive : f ≠ 0)
    (bound : f ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values)) :
    let count := Compiler.Backend.WordToStack.numStackRet k values
    ∃ (restored : StackSemStateFiniteExact width C F)
      (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
      StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values .skip, target) =
        (none, restored) ∧
      restored = {target with stack := stack, regs := regs, stackSpace := target.stackSpace + count} ∧
      stack.length = target.stack.length ∧
      stack.drop (f + count + target.stackSpace) = target.stack.drop (f + count + target.stackSpace) ∧
      (∀ register, register ≠ k →
        regs.lookup register = target.regs.lookup register) ∧
      (∀ index, index < f - count →
        holEl index (stack.drop (count + target.stackSpace)) =
          holEl index (target.stack.drop (count + target.stackSpace))) ∧
      (∀ index, index < count →
        holEl (index + f) (stack.drop target.stackSpace) =
          holEl index (target.stack.drop target.stackSpace)) := by
  dsimp only
  let count := Compiler.Backend.WordToStack.numStackRet k values
  obtain ⟨copied, copyRun, stack, regs, copiedState, length, _, tail, registers, live, returns⟩ :=
    CallReturnEval.evaluateCopyRetAux k f count target ⟨useStack, positive, bound⟩
  subst copied
  let restored : StackSemStateFiniteExact width C F := {target with
    stack := stack, regs := regs, stackSpace := target.stackSpace + count}
  refine ⟨restored, stack, regs, ?_, rfl, length, tail, registers, live, returns⟩
  by_cases zero : count = 0
  · have unchanged : {target with stack := stack, regs := regs} = target := by
      have run := copyRun
      rw [zero, copyRetAuxNative, StackSemEvaluate.evaluate_skip] at run
      exact (Prod.mk.inj run).2.symm
    have restoredEq : restored = target := by
      dsimp [restored]
      rw [zero, Nat.add_zero]
      exact unchanged
    rw [copyRetNative, if_pos zero, StackSemEvaluate.evaluate_skip, restoredEq]
  · rw [copyRetNative, if_neg zero]
    simp only [Bool.false_eq_true, if_false]
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, copyRun]
    simp only
    rw [CallHelpers.evaluateSeqStackFree count .skip {target with stack := stack, regs := regs}
      ⟨useStack, by change target.stackSpace ≤ stack.length; rw [length]; omega⟩,
      StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_stackFree, if_neg (by simp [useStack]),
      if_neg (by change ¬ stack.length < target.stackSpace + count; rw [length]; omega)]
    simp only
    rw [StackSemEvaluate.evaluate_skip]

/-- Flapjack normal-return target assembly from the actual original guarded
callee IH. The full body result contract retains all resource outcomes;
its original matching-Return branch derives the copy/free bounds from the
recovered source frame and target stack_rel, then executes the actual return
wrapper. No postrelation or successful target run is a premise. Final caller
state_rel and continuation execution remain open; no separate HOL declaration. -/
theorem simulateCalleeAndCopyReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (returnedLocation : WordLocW width) (returned : List (WordLocW width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result returnedLocation returned), bodyPost)) :
    ∃ (calleeSize calleeFrame : Nat) (body : HolProg width) (codeLocation : Nat),
      sptLookup codeLocation source.code = some (args1.length, prog) ∧
      sptLookup codeLocation saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      (calleeSize ≤ saved.stackSpace →
        ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost (some (.result returnedLocation returned)) targetResult
            (callerFrame :: lens) ∧
          (targetResult = some (.result returnedLocation) →
            let count := Compiler.Backend.WordToStack.numStackRet k values
            ∃ (restored : StackSemStateFiniteExact width C F)
              (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
              StackSemEvaluate.evaluate
                (copyRetNative false false (k, callerSize, callerFrame) values .skip, targetPost) =
                (none, restored) ∧
              restored = {targetPost with
                stack := stack, regs := regs, stackSpace := targetPost.stackSpace + count} ∧
              stack.length = targetPost.stack.length ∧
              stack.drop (callerSize + count + targetPost.stackSpace) =
                targetPost.stack.drop (callerSize + count + targetPost.stackSpace) ∧
              (∀ register, register ≠ k → regs.lookup register = targetPost.regs.lookup register) ∧
              (∀ index, index < callerSize - count →
                holEl index (stack.drop (count + targetPost.stackSpace)) =
                  holEl index (targetPost.stack.drop (count + targetPost.stackSpace))) ∧
              (∀ index, index < count →
                holEl (index + callerSize) (stack.drop targetPost.stackSpace) =
                  holEl index (targetPost.stack.drop targetPost.stackSpace)))) := by
  obtain ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, simulate⟩ :=
    simulateCalleeBody ac k callerSize callerFrame values names retCode l1 l2 dest args source
      sourcePost bodyPost result (some (.result returnedLocation returned)) saved lens xs args1
      prog ss envs destinationCode destination guards callerRelation pushedRelation conventions
      maximum destinationCompile ih nonzero execution notError bodyRun
  refine ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, ?_⟩
  intro space
  obtain ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion⟩ := simulate space
  refine ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion, ?_⟩
  intro targetReturn
  obtain ⟨gc, tail, _, sourceFrame, _, _, _, _, _, _, valid, _, _⟩ :=
    sourceReturningContinuation ac values names retCode l1 l2 dest args source sourcePost
      bodyPost result xs args1 prog ss envs returnedLocation returned guards ih nonzero
      execution notError bodyRun
  have positive := positiveCallerFrame k callerFrame values names retCode l1 l2 dest args
    source xs args1 prog ss envs guards conventions maximum
  have callerShape : if callerFrame = 0 then callerSize = 0 else callerSize = callerFrame + 1 := by
    have relation := callerRelation
    unfold stateRel at relation
    aesop (config := { enableSimp := false })
  have callerSizeEq : callerSize = callerFrame + 1 := by
    split_ifs at callerShape <;> omega
  have kBound : 4 < k := by
    have relation := callerRelation
    unfold stateRel at relation
    aesop (config := { enableSimp := false })
  have countEq : Compiler.Backend.WordToStack.numStackRet k values = returned.length - (k - 1) := by
    unfold Compiler.Backend.WordToStack.numStackRet
    have lengthEq := (not_or.mp valid).2
    omega
  have matching := conclusion
  rw [targetReturn] at matching
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at matching
  obtain ⟨returnedRelation, _⟩ := matching
  have useStack : targetPost.useStack = true := by
    unfold stateRel at returnedRelation
    aesop (config := { enableSimp := false })
  have stackRelation : stackRel k bodyPost.handler bodyPost.stack
      (targetPost.store.lookup .handler)
      (targetPost.stack.drop (targetPost.stackSpace + (returned.length - (k - 1))))
      targetPost.stack.length targetPost.bitmaps (callerFrame :: lens) := by
    unfold stateRel at returnedRelation
    aesop (config := { enableSimp := false })
  rw [sourceFrame] at stackRelation
  have frameBound := CallReturnSupport.stackRelConsLenNone k bodyPost.handler source.localsSize
    (sptToAList envs.1) gc tail (targetPost.store.lookup .handler)
    (targetPost.stack.drop (targetPost.stackSpace + (returned.length - (k - 1))))
    targetPost.stack.length targetPost.bitmaps callerFrame lens stackRelation
  rw [List.length_drop] at frameBound
  exact evaluateReturnCopyFree k callerSize callerFrame values targetPost useStack
    (by omega) (by rwa [callerSizeEq, countEq])

/-- Case-local source lookup decomposition used by the original normal-return
restoration proof. It unfolds the actual popped NONE frame and actual `setVars`:
returned entries take precedence, then restored GC entries, then the saved
non-GC environment. No distinctness, lookup outcome, or target relation is
assumed. This is infrastructure factoring inside `comp_correct`, not a separate
HOL declaration or the completed caller state relation. -/
theorem restoredCallerLookup {width : Nat} [NeZero width] {C F : Type}
    (bodyPost : WordSemStateFiniteExact width C F) (size : Nat)
    (nonGC : Spt (WordLocW width)) (gc : List (Nat × WordLocW width))
    (tail : List (WordSemStackFrame width))
    (values : List Nat) (returned : List (WordLocW width)) (key : Nat)
    (frame : bodyPost.stack = .stackFrame size (sptToAList nonGC) gc none :: tail) :
    ∃ popped, WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptLookup key (WordSemStateFiniteExact.setVars values returned popped).locals =
        match holAlookup (values.zip returned) key with
        | some result => some result
        | none => match sptAListLookup key gc with
          | some result => some result
          | none => sptLookup key nonGC := by
  refine ⟨{ bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList nonGC)),
    stack := tail, localsSize := size }, ?_, ?_⟩
  · simp only [WordSemStateFiniteExact.popEnv, frame]
  · have savedLookup : sptAListLookup key (sptToAList nonGC) = sptLookup key nonGC := by
      rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList]
    simp only [WordSemStateFiniteExact.setVars, lookup_alist_insert_any,
      sptLookup_sptUnion, sptLookup_sptFromAList, savedLookup]
    cases holAlookup (values.zip returned) key <;> cases sptAListLookup key gc <;> rfl

/-- Recover the actual saved NONE frame's GC and non-GC slot observations
from the complete stack relation. The bitmap and concrete frame are derived
from successful abstraction; GC membership is derived from the actual bitmap
filter. No slot correspondence or bounds are added as premises. This is
case-local factoring of the normal-return restoration proof, not a separate
HOL declaration or a completed caller relation. -/
theorem savedCallerFrameSlots {width handlerWidth : Nat}
    [NeZero width] [NeZero handlerWidth]
    (k handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth)) (stack : List (WordLocW width))
    (length : Nat) (bitmaps : List (BitVec width)) (frame : Nat) (lens : List Nat)
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      targetHandler stack length bitmaps (frame :: lens)) :
    ∃ bitmap rest bits, stack = bitmap :: rest ∧
      StackSem.fullReadBitmap bitmaps bitmap = some bits ∧
      bits.length = frame ∧ frame ≤ rest.length ∧
      (∀ key value, sptAListLookup key gc = some value →
        key / 2 - k < (rest.take frame).length ∧
        (rest.take frame)[(rest.take frame).length - (key / 2 - k + 1)]? = some value) ∧
      (∀ key value, nonGC.lookup key = some value → gc.lookup key = none →
        adjustNames key < k + bits.length ∧
        bits[k + bits.length - (adjustNames key + 1)]? = some false ∧
        (indexList (rest.take frame) k).lookup (key / 2) = some value) := by
  obtain ⟨_, abstract, decoded, _, auxiliary⟩ := relation
  obtain ⟨bitmap, rest, bits, ys, shape, read, bitsLength, bound, _, abstractShape⟩ :=
    CallReturnSupport.absStack_cons_none bitmaps size nonGC gc tail stack frame lens abstract decoded
  rw [abstractShape] at auxiliary
  simp only [stackRelAux] at auxiliary
  refine ⟨bitmap, rest, bits, shape, read, bitsLength, bound, ?_, auxiliary.1⟩
  intro key value lookup
  have member := sptAListLookup_mem key gc value lookup
  have mapped : (adjustNames key, value) ∈ gc.map (fun p => (adjustNames p.1, p.2)) :=
    List.mem_map.mpr ⟨(key, value), member, rfl⟩
  have indexMember := Compiler.Backend.WordToStack.filterBitmapMem bits
    (indexList (rest.take frame) k) _ (adjustNames key, value) auxiliary.2.1 mapped
  have indexBound := memIndexListLim (rest.take frame) (adjustNames key) value k indexMember
  have slot := memIndexListEl (rest.take frame) (adjustNames key) value k indexMember
  simp only [adjustNames] at indexBound slot
  refine ⟨indexBound, ?_⟩
  rw [List.getElem?_eq_getElem (by omega), slot]

/-- Derive concrete non-GC caller slots from the original auxiliary relation.
Both lower and upper key bounds follow from the successful indexed-frame
lookup; neither a register/stack decision nor a target slot is assumed.
This is case-local restoration infrastructure, not a separate HOL port. -/
theorem savedCallerNonGCSlots {width handlerWidth : Nat}
    [NeZero width] [NeZero handlerWidth]
    (k handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth)) (stack : List (WordLocW width))
    (length : Nat) (bitmaps : List (BitVec width)) (frame : Nat) (lens : List Nat)
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      targetHandler stack length bitmaps (frame :: lens)) :
    ∃ bitmap rest, stack = bitmap :: rest ∧ frame ≤ rest.length ∧
      ∀ key value, sptAListLookup key nonGC = some value → sptAListLookup key gc = none →
        k ≤ key / 2 ∧ key / 2 < k + frame ∧
        (rest.take frame)[frame - 1 - (key / 2 - k)]? = some value := by
  obtain ⟨bitmap, rest, bits, shape, _, bitsLength, bound, _, nonGCSlots⟩ :=
    savedCallerFrameSlots k handler size nonGC gc tail targetHandler stack length bitmaps
      frame lens relation
  refine ⟨bitmap, rest, shape, bound, ?_⟩
  intro key value lookup absent
  obtain ⟨keyBound, _, slot⟩ := nonGCSlots key value
    (by rwa [GcSimulation.lookup_eq_sptAListLookup])
    (by rwa [GcSimulation.lookup_eq_sptAListLookup])
  simp only [adjustNames] at keyBound
  rw [bitsLength] at keyBound
  have frameLength : (rest.take frame).length = frame := by
    rw [List.length_take, Nat.min_eq_left bound]
  rw [GcSimulation.lookup_eq_sptAListLookup, aLookupIndexList _ _ _
    (by rw [frameLength]; omega), frameLength] at slot
  have positionBound := (List.getElem?_eq_some_iff.mp slot).1
  rw [frameLength] at positionBound
  have lower : k ≤ key / 2 := by omega
  refine ⟨lower, keyBound, ?_⟩
  rwa [show frame + k - (key / 2 + 1) = frame - 1 - (key / 2 - k) by omega] at slot

/-- Recover concrete GC caller slots from actual bitmap-filter membership.
Indexed-frame membership proves the lower key bound as well as the upper bound
and actual value. This adds no convention, range or target-slot premise and is
case-local infrastructure for the full normal-return caller restoration. -/
theorem savedCallerGCSlots {width handlerWidth : Nat}
    [NeZero width] [NeZero handlerWidth]
    (k handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth)) (stack : List (WordLocW width))
    (length : Nat) (bitmaps : List (BitVec width)) (frame : Nat) (lens : List Nat)
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      targetHandler stack length bitmaps (frame :: lens)) :
    ∃ bitmap rest, stack = bitmap :: rest ∧ frame ≤ rest.length ∧
      ∀ key value, sptAListLookup key gc = some value →
        k ≤ key / 2 ∧ key / 2 < k + frame ∧
        (rest.take frame)[frame - 1 - (key / 2 - k)]? = some value := by
  obtain ⟨_, abstract, decoded, _, auxiliary⟩ := relation
  obtain ⟨bitmap, rest, bits, ys, shape, _, _, bound, _, abstractShape⟩ :=
    CallReturnSupport.absStack_cons_none bitmaps size nonGC gc tail stack frame lens abstract decoded
  rw [abstractShape] at auxiliary
  simp only [stackRelAux] at auxiliary
  refine ⟨bitmap, rest, shape, bound, ?_⟩
  intro key value lookup
  have member := sptAListLookup_mem key gc value lookup
  have mapped : (adjustNames key, value) ∈ gc.map (fun p => (adjustNames p.1, p.2)) :=
    List.mem_map.mpr ⟨(key, value), member, rfl⟩
  have indexMember := Compiler.Backend.WordToStack.filterBitmapMem bits
    (indexList (rest.take frame) k) _ (adjustNames key, value) auxiliary.2.1 mapped
  have keyMember : adjustNames key ∈ (indexList (rest.take frame) k).map Prod.fst :=
    List.mem_map.mpr ⟨(adjustNames key, value), indexMember, rfl⟩
  rw [mapFstIndexList, List.mem_reverse] at keyMember
  obtain ⟨offset, _, keyEq⟩ := List.mem_map.mp keyMember
  have lower : k ≤ key / 2 := by simp only [adjustNames] at keyEq; omega
  have upper := memIndexListLim (rest.take frame) (adjustNames key) value k indexMember
  have slot := memIndexListEl (rest.take frame) (adjustNames key) value k indexMember
  have frameLength : (rest.take frame).length = frame := by
    rw [List.length_take, Nat.min_eq_left bound]
  have optional := List.getElem?_eq_some_iff.mpr ⟨_, slot⟩
  simp only [adjustNames, frameLength] at upper optional
  refine ⟨lower, by omega, ?_⟩
  rwa [show frame - (key / 2 - k + 1) = frame - 1 - (key / 2 - k) by omega] at optional

/-- Optional-index observations of the actual return-copy/free execution.
The original copy bounds imply every index used here is in range; the proof
converts total HOL EL only after deriving those bounds. No chosen out-of-range
value or assumed target execution is used. This is case-local infrastructure
for transporting caller locals, not a separate HOL correctness declaration. -/
theorem evaluateReturnCopyFreeLookup {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (values : List Nat) (target : StackSemStateFiniteExact width C F)
    (useStack : target.useStack = true) (positive : f ≠ 0)
    (bound : f ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values)) :
    let count := Compiler.Backend.WordToStack.numStackRet k values
    ∃ (restored : StackSemStateFiniteExact width C F)
      (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
      StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values .skip, target) =
        (none, restored) ∧
      restored = {target with stack := stack, regs := regs, stackSpace := target.stackSpace + count} ∧
      stack.length = target.stack.length ∧
      stack.drop (f + count + target.stackSpace) = target.stack.drop (f + count + target.stackSpace) ∧
      (∀ register, register ≠ k → regs.lookup register = target.regs.lookup register) ∧
      (∀ index, index < f - count →
        (stack.drop (count + target.stackSpace))[index]? =
          (target.stack.drop (count + target.stackSpace))[index]?) ∧
      (∀ index, index < count →
        (stack.drop target.stackSpace)[index + f]? =
          (target.stack.drop target.stackSpace)[index]?) := by
  dsimp only
  let count := Compiler.Backend.WordToStack.numStackRet k values
  obtain ⟨restored, stack, regs, execution, shape, length, tail, registers, live, returns⟩ :=
    evaluateReturnCopyFree k f frame values target useStack positive bound
  refine ⟨restored, stack, regs, execution, shape, length, tail, registers, ?_, ?_⟩
  · intro index indexBound
    have sourceBound : index < (target.stack.drop (count + target.stackSpace)).length := by
      rw [List.length_drop]; dsimp [count] at *; omega
    have targetBound : index < (stack.drop (count + target.stackSpace)).length := by
      rw [List.length_drop, length]; dsimp [count] at *; omega
    rw [List.getElem?_eq_getElem targetBound, List.getElem?_eq_getElem sourceBound]
    have observation := live index indexBound
    change holEl index (stack.drop (count + target.stackSpace)) =
      holEl index (target.stack.drop (count + target.stackSpace)) at observation
    rw [holEl_eq_getElem index _ targetBound, holEl_eq_getElem index _ sourceBound] at observation
    exact congrArg some observation
  · intro index indexBound
    have sourceBound : index < (target.stack.drop target.stackSpace).length := by
      rw [List.length_drop]; dsimp [count] at *; omega
    have targetBound : index + f < (stack.drop target.stackSpace).length := by
      rw [List.length_drop, length]; dsimp [count] at *; omega
    rw [List.getElem?_eq_getElem targetBound, List.getElem?_eq_getElem sourceBound]
    exact congrArg some (by
      simpa only [holEl_eq_getElem (index + f) _ targetBound,
        holEl_eq_getElem index _ sourceBound] using returns index indexBound)

/-- An original physical caller key absent from the canonical return names
lies beyond every return name. This is the arithmetic/name fact used by the
normal-return restoration proof to select the unchanged frame region; it has
no separate HOL declaration and assumes no target observation. -/
theorem callerKeyPastReturns (values : List Nat) (key : Nat)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (physical : key % 2 = 0) (positive : 0 < key) (absent : key ∉ values) :
    values.length < key / 2 := by
  by_contra outside
  have keyEq : 2 * (key / 2 - 1 + 1) = key := by omega
  apply absent
  rw [canonical]
  exact List.mem_map.mpr ⟨key / 2 - 1, List.mem_range.mpr (by omega), keyEq⟩

/-- A lookup in the actual popped GC/non-GC union has a concrete caller-frame
slot, including the bitmap word's offset. GC takes precedence exactly as in
popEnv; both key bounds and the slot are derived from the full stack relation.
This is case-local infrastructure, not the completed caller state relation. -/
theorem poppedCallerSlot {width handlerWidth : Nat}
    [NeZero width] [NeZero handlerWidth]
    (k handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth)) (stack : List (WordLocW width))
    (length : Nat) (bitmaps : List (BitVec width)) (frame : Nat) (lens : List Nat)
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      targetHandler stack length bitmaps (frame :: lens))
    (key : Nat) (value : WordLocW width)
    (lookup : sptLookup key (sptUnion (sptFromAList gc) (sptFromAList nonGC)) = some value) :
    k ≤ key / 2 ∧ key / 2 < k + frame ∧
      (stack.take (frame + 1))[frame - (key / 2 - k)]? = some value := by
  rw [sptLookup_sptUnion, sptLookup_sptFromAList, sptLookup_sptFromAList] at lookup
  have recovered : ∃ bitmap rest, stack = bitmap :: rest ∧ frame ≤ rest.length ∧
      k ≤ key / 2 ∧ key / 2 < k + frame ∧
      (rest.take frame)[frame - 1 - (key / 2 - k)]? = some value := by
    cases found : sptAListLookup key gc with
    | none =>
      rw [found] at lookup
      obtain ⟨bitmap, rest, shape, bound, slots⟩ :=
        savedCallerNonGCSlots k handler size nonGC gc tail targetHandler stack length bitmaps
          frame lens relation
      obtain ⟨lower, upper, slot⟩ := slots key value lookup found
      exact ⟨bitmap, rest, shape, bound, lower, upper, slot⟩
    | some gcValue =>
      rw [found] at lookup
      simp only [Option.some.injEq] at lookup
      subst gcValue
      obtain ⟨bitmap, rest, shape, bound, slots⟩ :=
        savedCallerGCSlots k handler size nonGC gc tail targetHandler stack length bitmaps
          frame lens relation
      obtain ⟨lower, upper, slot⟩ := slots key value found
      exact ⟨bitmap, rest, shape, bound, lower, upper, slot⟩
  obtain ⟨bitmap, rest, shape, _, lower, upper, slot⟩ := recovered
  refine ⟨lower, upper, ?_⟩
  rw [CallReturnSupport.llookupTake _ _ stack (by omega), shape,
    show frame - (key / 2 - k) = (frame - 1 - (key / 2 - k)) + 1 by omega,
    List.getElem?_cons_succ]
  rwa [CallReturnSupport.llookupTake _ frame rest (by omega)] at slot

/-- Execute the actual no-handler return wrapper and recover every popped
caller local outside the return-name range. Original canonical names and the
full saved-frame relation discharge unchanged-region selection internally;
there is no successful target run or target-slot correspondence premise.
This remains case-local restoration infrastructure, not full comp_correct. -/
theorem copyReturnPreservesPoppedLocals {width : Nat} [NeZero width] {C F : Type}
    (k frame handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (values : List Nat) (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (useStack : target.useStack = true)
    (bound : frame + 1 ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      (target.store.lookup .handler)
      (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
      target.stack.length target.bitmaps (frame :: lens)) :
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      ∀ key value,
        sptLookup key (sptUnion (sptFromAList gc) (sptFromAList nonGC)) = some value →
        key % 2 = 0 → 0 < key → key ∉ values →
        k ≤ key / 2 ∧ key / 2 < k + frame ∧
        ((restored.stack.drop restored.stackSpace).take (frame + 1))[frame - (key / 2 - k)]? =
          some value := by
  let count := Compiler.Backend.WordToStack.numStackRet k values
  obtain ⟨restored, stack, regs, execution, shape, _, _, _, live, _⟩ :=
    evaluateReturnCopyFreeLookup k (frame + 1) frame values target useStack (by omega) bound
  refine ⟨restored, execution, ?_⟩
  intro key value lookup physical positive absent
  obtain ⟨lower, upper, slot⟩ := poppedCallerSlot k handler size nonGC gc tail
    (target.store.lookup .handler) (target.stack.drop (target.stackSpace + count))
    target.stack.length target.bitmaps frame lens relation key value lookup
  have past := callerKeyPastReturns values key canonical physical positive absent
  have unchanged : frame - (key / 2 - k) < frame + 1 - count := by
    dsimp [count, Compiler.Backend.WordToStack.numStackRet]; omega
  have preserved := live (frame - (key / 2 - k)) unchanged
  refine ⟨lower, upper, ?_⟩
  rw [shape]
  simp only
  rw [CallReturnSupport.llookupTake _ _ _ (by omega)]
  rw [CallReturnSupport.llookupTake _ _ _ (by omega)] at slot
  rw [Nat.add_comm target.stackSpace count] at slot
  simpa only [Nat.add_comm] using preserved.trans slot

/-- Recover the actual returned value's position from first-match lookup
in canonical return names. The source Return length test supplies lengthEq;
no target placement or index bound is assumed. This is case-local source
lookup infrastructure for the returned-value caller-local branch. -/
theorem returnedCallerLookupIndex {width : Nat} [NeZero width]
    (values : List Nat) (returned : List (WordLocW width)) (key : Nat) (value : WordLocW width)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (lengthEq : returned.length = values.length)
    (lookup : holAlookup (values.zip returned) key = some value) :
    ∃ index, index < returned.length ∧ key = 2 * (index + 1) ∧ returned[index]? = some value := by
  have membership : ∀ entries : List (Nat × WordLocW width),
      holAlookup entries key = some value → (key, value) ∈ entries := by
    intro entries
    induction entries with
    | nil => simp [holAlookup]
    | cons entry entries ih =>
      obtain ⟨name, item⟩ := entry
      simp only [holAlookup]
      by_cases same : name = key
      · subst name
        simp only [if_true, Option.some.injEq]
        intro equality
        subst item
        exact List.mem_cons_self
      · rw [if_neg same]
        exact fun found => List.mem_cons_of_mem _ (ih found)
  obtain ⟨index, indexBound, pair⟩ := List.mem_iff_getElem.mp (membership _ lookup)
  have namesBound : index < values.length := by
    rw [List.length_zip] at indexBound; omega
  have returnedBound : index < returned.length := by omega
  rw [List.getElem_zip] at pair
  have name := congrArg Prod.fst pair
  have item := congrArg Prod.snd pair
  simp only at name item
  have nameOption : values[index]? = some key :=
    List.getElem?_eq_some_iff.mpr ⟨namesBound, name⟩
  rw [canonical] at nameOption
  simp only [List.getElem?_map, List.getElem?_range namesBound, Option.map_some,
    Option.some.injEq] at nameOption
  exact ⟨index, returnedBound, nameOption.symm,
    List.getElem?_eq_some_iff.mpr ⟨returnedBound, item⟩⟩

/-- Factor the unchanged fields of the full caller relation after actual
pop/setVars and return-copy updates. The existing full relation supplies every
cold field, code/oracle obligation and dimension constraint. The conclusion
keeps all changed frame/local/stack obligations explicit on the right of an
iff; it does not assume the restored relation or prove it from weakened
semantics. Target store is unchanged here, so handler-store restoration needs
its own proof. Case-local infrastructure, with no separate HOL declaration. -/
theorem callerStateRelUpdates {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k oldSize oldFrame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (oldLens : List Nat) (oldExtra : Nat)
    (locals : Spt (WordLocW width)) (sourceStack : List (WordSemStackFrame width))
    (localsSize : Option Nat) (handler : Nat) (stack : List (WordLocW width))
    (regs : HolFiniteMapExact Nat (WordLocW width)) (space f frame : Nat)
    (lens : List Nat) (extra : Nat)
    (related : stateRel ac k oldSize oldFrame source target oldLens oldExtra)
    (length : stack.length = target.stack.length) :
    stateRel ac k f frame
      {source with locals := locals, stack := sourceStack, localsSize := localsSize, handler := handler}
      {target with stack := stack, regs := regs, stackSpace := space} lens extra ↔
      space + f ≤ stack.length ∧
      (if frame = 0 then f = 0 else f = frame + 1) ∧ sptWf locals = true ∧
      stackSizeRel f localsSize source.stackLimit source.stackMax sourceStack stack space extra ∧
      (let active := stack.drop (space + extra)
       let currentFrame := active.take f
       let restOfStack := active.drop f
       stackRel k handler sourceStack (target.store.lookup .handler) restOfStack
         stack.length target.bitmaps lens ∧
       ∀ name value, sptLookup name locals = some value →
         name % 2 = 0 ∧
         if name / 2 < k then regs.lookup (name / 2) = some value
         else currentFrame[f - 1 - (name / 2 - k)]? = some value ∧ name / 2 < k + frame) := by
  unfold stateRel at related
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31,
    h32, _, h34, _, _, _, _⟩ := related
  simp only [stateRel, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h18, h19, h20, h21, h22, h23, h24, h26, h27, h28, h29,
    h30, h31, h32, length, h34, true_and]
  constructor
  · rintro ⟨_, _, _, residual⟩
    exact residual
  · intro residual
    refine ⟨h17, ?_, h25, residual⟩
    intro n zero
    have oracle := h23 n
    change (source.compileOracle n).1.1 = target.bitmaps.length
    generalize source.compileOracle n = call at oracle ⊢
    obtain ⟨⟨bm, cfg⟩, progs⟩ := call
    exact oracle.2.2.2.2 zero

/-- Restore the original stack-size relation after popping a saved NONE
caller frame and freeing the return payload. The full saved stack relation
derives the Option-sized caller-frame identity. The callee resource relation
then supplies the actual source stack sum, including its unknown/known maximum
cases. No target run, new resource relation or frame-size identity is assumed.
This is case-local infrastructure for normal-return comp_correct restoration. -/
theorem callerStackSizeAfterPop {width handlerWidth : Nat}
    [NeZero width] [NeZero handlerWidth]
    (k handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (targetHandler : Option (WordLocW handlerWidth)) (stack : List (WordLocW width))
    (bitmaps : List (BitVec width)) (frame : Nat) (lens : List Nat)
    (space count : Nat) (calleeLocalsSize : Option Nat) (limit : Nat) (maximum : Option Nat)
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      targetHandler (stack.drop (space + count)) stack.length bitmaps (frame :: lens))
    (resource : stackSizeRel 0 calleeLocalsSize limit maximum
      (.stackFrame size nonGC gc none :: tail) stack space count) :
    stackSizeRel (frame + 1) size limit maximum tail stack (space + count) 0 := by
  have sizeIdentity := CallReturnSupport.stackRelConsLocalsSize k handler size nonGC gc none tail
    targetHandler (stack.drop (space + count)) stack.length bitmaps frame lens relation
  obtain ⟨_, limitEq, resourceMaximum⟩ := resource
  refine ⟨fun _ => sizeIdentity, limitEq, ?_⟩
  intro knownMaximum known
  obtain ⟨maximumBound, _, total, stackSum, totalEq⟩ := resourceMaximum knownMaximum known
  change wordSemOptionAdd size (wordSemStackSize tail) = some total at stackSum
  cases size with
  | none => simp only [wordSemOptionAdd] at stackSum; contradiction
  | some callerSize =>
    simp only [Option.getD_some] at sizeIdentity
    rw [sizeIdentity] at stackSum
    cases tailSize : wordSemStackSize tail with
    | none => simp only [tailSize, wordSemOptionAdd] at stackSum; contradiction
    | some tailCount =>
      simp only [tailSize, wordSemOptionAdd, Option.some.injEq] at stackSum
      exact ⟨by omega, rfl, tailCount, rfl, by omega⟩

/-- Execute return-copy/free and derive its restored caller stack-size
relation from the original callee and saved-frame relations. The new stack
length and space are outputs of the actual wrapper execution, not hypotheses.
This case-local assembly is not a separate HOL port or the full caller stateRel. -/
theorem copyReturnRestoresStackSize {width : Nat} [NeZero width] {C F : Type}
    (k frame handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (values : List Nat) (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (calleeLocalsSize : Option Nat) (limit : Nat) (maximum : Option Nat)
    (useStack : target.useStack = true)
    (bound : frame + 1 ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      (target.store.lookup .handler)
      (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
      target.stack.length target.bitmaps (frame :: lens))
    (resource : stackSizeRel 0 calleeLocalsSize limit maximum
      (.stackFrame size nonGC gc none :: tail) target.stack target.stackSpace
      (Compiler.Backend.WordToStack.numStackRet k values)) :
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      stackSizeRel (frame + 1) size limit maximum tail restored.stack restored.stackSpace 0 := by
  obtain ⟨restored, stack, regs, execution, shape, length, _, _, _, _⟩ :=
    evaluateReturnCopyFree k (frame + 1) frame values target useStack (by omega) bound
  have caller := callerStackSizeAfterPop k handler size nonGC gc tail
    (target.store.lookup .handler) target.stack target.bitmaps frame lens target.stackSpace
    (Compiler.Backend.WordToStack.numStackRet k values) calleeLocalsSize limit maximum relation resource
  refine ⟨restored, execution, ?_⟩
  rw [shape]
  unfold stackSizeRel at caller ⊢
  simpa only [length] using caller

/-- The same actual return-copy/free run restores both original stack
relations. Saved-frame removal proves the tail relation, actual copy outputs
preserve its target suffix, and the resource component derives stack size.
No restored stack/resource relation or target run is assumed. This remains
case-local assembly; returned locals and full caller stateRel are separate. -/
theorem copyReturnRestoresStackRelations {width : Nat} [NeZero width] {C F : Type}
    (k frame handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (values : List Nat) (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (calleeLocalsSize : Option Nat) (limit : Nat) (maximum : Option Nat)
    (useStack : target.useStack = true)
    (bound : frame + 1 ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      (target.store.lookup .handler)
      (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
      target.stack.length target.bitmaps (frame :: lens))
    (resource : stackSizeRel 0 calleeLocalsSize limit maximum
      (.stackFrame size nonGC gc none :: tail) target.stack target.stackSpace
      (Compiler.Backend.WordToStack.numStackRet k values)) :
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      stackSizeRel (frame + 1) size limit maximum tail restored.stack restored.stackSpace 0 ∧
      stackRel k handler tail (restored.store.lookup .handler)
        ((restored.stack.drop restored.stackSpace).drop (frame + 1))
        restored.stack.length restored.bitmaps lens := by
  obtain ⟨restored, stack, regs, execution, shape, length, suffix, _, _, _⟩ :=
    evaluateReturnCopyFree k (frame + 1) frame values target useStack (by omega) bound
  obtain ⟨resourceRestored, resourceRun, restoredResource⟩ :=
    copyReturnRestoresStackSize k frame handler size nonGC gc tail values target lens
      calleeLocalsSize limit maximum useStack bound relation resource
  have same : resourceRestored = restored := (Prod.mk.inj (resourceRun.symm.trans execution)).2
  subst resourceRestored
  have tailRelation := CallReturnSupport.stackRelDropNone k handler size nonGC gc tail
    (target.store.lookup .handler)
    (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    target.stack.length target.bitmaps frame lens relation
  refine ⟨restored, execution, restoredResource, ?_⟩
  rw [shape]
  simp only [List.drop_drop, length]
  simp only [List.drop_drop] at tailRelation
  have suffixEq :
      stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values + (frame + 1)) =
        target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values + (frame + 1)) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using suffix
  rw [suffixEq]
  exact tailRelation

/-- Transport the original callee Return placement clause through the actual
no-handler copy/free wrapper to every returned caller local. Canonical names,
the source length test and original caller name bound supply the index/range
arithmetic. No restored relation or successful wrapper execution is assumed.
This is untagged case-local assembly of the original normal-return branch. -/
theorem copyReturnPlacesReturnedLocals {width : Nat} [NeZero width] {C F : Type}
    (k frame : Nat) (values : List Nat) (returned : List (WordLocW width))
    (target : StackSemStateFiniteExact width C F)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (lengthEq : returned.length = values.length)
    (nameBound : returned.length < k + frame)
    (useStack : target.useStack = true)
    (bound : frame + 1 ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    (placements : ∀ index, index < returned.length →
      if index + 1 < k then target.regs.lookup (index + 1) = some (holEl index returned)
      else (target.stack.drop target.stackSpace)[returned.length - (index + 1)]? =
        some (holEl index returned)) :
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      ∀ key value, holAlookup (values.zip returned) key = some value →
        key % 2 = 0 ∧
        if key / 2 < k then restored.regs.lookup (key / 2) = some value
        else ((restored.stack.drop restored.stackSpace).take (frame + 1))[frame - (key / 2 - k)]? =
          some value ∧ key / 2 < k + frame := by
  let count := Compiler.Backend.WordToStack.numStackRet k values
  obtain ⟨restored, stack, regs, execution, shape, _, _, registers, _, copied⟩ :=
    evaluateReturnCopyFreeLookup k (frame + 1) frame values target useStack (by omega) bound
  refine ⟨restored, execution, ?_⟩
  intro key value lookup
  obtain ⟨index, indexBound, keyEq, item⟩ :=
    returnedCallerLookupIndex values returned key value canonical lengthEq lookup
  have valueEq : holEl index returned = value := by
    rw [holEl_eq_getElem index returned indexBound]
    exact (List.getElem?_eq_some_iff.mp item).2
  have keyHalf : key / 2 = index + 1 := by omega
  have placement := placements index indexBound
  refine ⟨by omega, ?_⟩
  rw [keyHalf]
  by_cases register : index + 1 < k
  · rw [if_pos register] at placement ⊢
    rw [shape]
    simp only
    rw [registers (index + 1) (by omega)]
    simpa only [valueEq] using placement
  · rw [if_neg register] at placement ⊢
    refine ⟨?_, by omega⟩
    have countEq : count = returned.length + 1 - k := by
      dsimp [count, Compiler.Backend.WordToStack.numStackRet]
      omega
    have copiedIndex : returned.length - (index + 1) < count := by omega
    have slot := copied (returned.length - (index + 1)) copiedIndex
    have position : count + (frame - (index + 1 - k)) =
        returned.length - (index + 1) + (frame + 1) := by omega
    rw [shape]
    simp only
    rw [CallReturnSupport.llookupTake _ _ _ (by omega)]
    rw [List.getElem?_drop]
    change stack[target.stackSpace + count + (frame - (index + 1 - k))]? = some value
    rw [Nat.add_assoc, position]
    simpa only [List.getElem?_drop] using
      slot.trans (by simpa only [valueEq] using placement)

/-- Assemble every caller-local placement and local-tree well-formedness
through the actual NONE return wrapper. The callee's original Return placement
clause supplies returned values; the full saved-frame relation supplies old
values. The physical-key premise is the original cut-set convention obligation,
not a target observation. This remains case-local infrastructure until that
obligation and the other caller-relation clauses are discharged from the full
Call premises; it is not a tagged full comp_correct case. -/
theorem copyReturnRestoresCallerLocals {width : Nat} [NeZero width] {C F : Type}
    (k frame handler : Nat) (size : Option Nat)
    (nonGC gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
    (values : List Nat) (returned : List (WordLocW width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (lengthEq : returned.length = values.length)
    (nameBound : returned.length < k + frame)
    (physical : ∀ key value,
      sptLookup key (sptUnion (sptFromAList gc) (sptFromAList nonGC)) = some value →
      key % 2 = 0 ∧ 0 < key)
    (useStack : target.useStack = true)
    (bound : frame + 1 ≤ target.stack.length -
      (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
    (relation : stackRel k handler (.stackFrame size nonGC gc none :: tail)
      (target.store.lookup .handler)
      (target.stack.drop (target.stackSpace + Compiler.Backend.WordToStack.numStackRet k values))
      target.stack.length target.bitmaps (frame :: lens))
    (placements : ∀ index, index < returned.length →
      if index + 1 < k then target.regs.lookup (index + 1) = some (holEl index returned)
      else (target.stack.drop target.stackSpace)[returned.length - (index + 1)]? =
        some (holEl index returned)) :
    let locals := LoopSemStateFiniteExact.sptAlistInsert values returned
      (sptUnion (sptFromAList gc) (sptFromAList nonGC))
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      sptWf locals = true ∧
      ∀ key value, sptLookup key locals = some value →
        key % 2 = 0 ∧
        if key / 2 < k then restored.regs.lookup (key / 2) = some value
        else ((restored.stack.drop restored.stackSpace).take (frame + 1))[frame - (key / 2 - k)]? =
          some value ∧ key / 2 < k + frame := by
  dsimp only
  obtain ⟨restored, execution, returns⟩ := copyReturnPlacesReturnedLocals
    k frame values returned target canonical lengthEq nameBound useStack bound placements
  obtain ⟨preservedState, preservedRun, preserved⟩ := copyReturnPreservesPoppedLocals
    k frame handler size nonGC gc tail values target lens canonical useStack bound relation
  have same := (Prod.mk.inj (preservedRun.symm.trans execution)).2
  subst preservedState
  refine ⟨restored, execution, wfAlistInsert values returned _
    (sptWfUnion _ _ ⟨sptWfFromAList gc, sptWfFromAList nonGC⟩), ?_⟩
  intro key value lookup
  rw [lookup_alist_insert_any] at lookup
  cases found : holAlookup (values.zip returned) key with
  | some item =>
      rw [found] at lookup
      have equality := Option.some.inj lookup
      subst item
      exact returns key value found
  | none =>
      rw [found] at lookup
      have absent : ∀ (xs : List Nat) (ys : List (WordLocW width)) (key : Nat),
          xs.length = ys.length → holAlookup (xs.zip ys) key = none → key ∉ xs := by
        intro xs
        induction xs with
        | nil => simp
        | cons name xs ih =>
            intro ys key lengths missing
            cases ys with
            | nil => simp at lengths
            | cons item ys =>
                simp only [List.zip_cons_cons, holAlookup] at missing
                split at missing
                · cases missing
                · rename_i different
                  simp only [List.mem_cons, not_or]
                  exact ⟨fun equality => different equality.symm,
                    ih ys key (by simpa using lengths) missing⟩
      obtain ⟨even, positive⟩ := physical key value lookup
      obtain ⟨lower, upper, slot⟩ := preserved key value lookup even positive
        (absent values returned key lengthEq.symm found)
      refine ⟨even, ?_⟩
      rw [if_neg (by omega)]
      exact ⟨slot, upper⟩

/-- Assemble the full NONE caller state relation after actual return copying.
The incoming full callee relation and saved source frame derive every target
bound/resource/tail clause; original return placements derive new locals.
Canonical names, their original maximum bound and cut-set physical keys are
explicit source-side obligations still to be discharged by the enclosing Call
assembly. No target execution or restored relation is a premise. This is
untagged case-local infrastructure, not the full guarded Call case. -/
theorem copyReturnRestoresCallerState {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (size : Option Nat) (nonGC gc : List (Nat × WordLocW width))
    (tail : List (WordSemStackFrame width)) (lens : List Nat)
    (values : List Nat) (returned : List (WordLocW width))
    (positive : frame ≠ 0)
    (canonical : values = (List.range values.length).map (fun index => 2 * (index + 1)))
    (lengthEq : returned.length = values.length)
    (nameBound : returned.length < k + frame)
    (physical : ∀ key value,
      sptLookup key (sptUnion (sptFromAList gc) (sptFromAList nonGC)) = some value →
      key % 2 = 0 ∧ 0 < key)
    (sourceFrame : source.stack = .stackFrame size nonGC gc none :: tail)
    (related : stateRel ac k 0 0 source target (frame :: lens)
      (Compiler.Backend.WordToStack.numStackRet k values))
    (placements : ∀ index, index < returned.length →
      if index + 1 < k then target.regs.lookup (index + 1) = some (holEl index returned)
      else (target.stack.drop target.stackSpace)[returned.length - (index + 1)]? =
        some (holEl index returned)) :
    let locals := LoopSemStateFiniteExact.sptAlistInsert values returned
      (sptUnion (sptFromAList gc) (sptFromAList nonGC))
    ∃ restored, StackSemEvaluate.evaluate
      (copyRetNative false false (k, frame + 1, frame) values .skip, target) = (none, restored) ∧
      stateRel ac k (frame + 1) frame
        {source with locals := locals, stack := tail, localsSize := size} restored lens 0 := by
  dsimp only
  let count := Compiler.Backend.WordToStack.numStackRet k values
  have useStack : target.useStack = true := by
    unfold stateRel at related
    aesop (config := { enableSimp := false })
  have saved : stackRel k source.handler (.stackFrame size nonGC gc none :: tail)
      (target.store.lookup .handler) (target.stack.drop (target.stackSpace + count))
      target.stack.length target.bitmaps (frame :: lens) := by
    have h := related
    unfold stateRel at h
    rw [sourceFrame] at h
    aesop (config := { enableSimp := false })
  have resource : stackSizeRel 0 source.localsSize source.stackLimit source.stackMax
      (.stackFrame size nonGC gc none :: tail) target.stack target.stackSpace count := by
    have h := related
    unfold stateRel at h
    rw [sourceFrame] at h
    aesop (config := { enableSimp := false })
  have bound := CallReturnSupport.stackRelConsLenNone k source.handler size nonGC gc tail
    (target.store.lookup .handler) (target.stack.drop (target.stackSpace + count))
    target.stack.length target.bitmaps frame lens saved
  rw [List.length_drop] at bound
  obtain ⟨restored, stack, regs, execution, shape, length, _, _, _, _⟩ :=
    evaluateReturnCopyFree k (frame + 1) frame values target useStack (by omega) bound
  obtain ⟨localState, localRun, wf, locals⟩ := copyReturnRestoresCallerLocals
    k frame source.handler size nonGC gc tail values returned target lens
    canonical lengthEq nameBound physical useStack bound saved placements
  have same := (Prod.mk.inj (localRun.symm.trans execution)).2
  subst localState
  obtain ⟨stackState, stackRun, restoredResource, restoredTail⟩ :=
    copyReturnRestoresStackRelations k frame source.handler size nonGC gc tail
      values target lens source.localsSize source.stackLimit source.stackMax
      useStack bound saved resource
  have same := (Prod.mk.inj (stackRun.symm.trans execution)).2
  subst stackState
  refine ⟨restored, execution, ?_⟩
  rw [shape] at restoredResource restoredTail locals ⊢
  apply (callerStateRelUpdates ac k 0 0 source target (frame :: lens) count
    (LoopSemStateFiniteExact.sptAlistInsert values returned
      (sptUnion (sptFromAList gc) (sptFromAList nonGC)))
    tail size source.handler stack regs (target.stackSpace + count) (frame + 1) frame
    lens 0 related length).mpr
  refine ⟨by omega, by simp only [positive, ↓reduceIte], wf, restoredResource, ?_⟩
  simpa only [Nat.add_zero, Nat.add_sub_cancel] using And.intro restoredTail locals

/-- Discharge normal-return caller name/physical-key obligations from the
original whole-Call conventions, maximum and successful cut operation. The
domain equality is the actual source stack-swap/pop invariant, not a target
relation premise. This is case-local source arithmetic for full restoration. -/
theorem returningCallerLocalObligations {width : Nat} [NeZero width] {C F : Type}
    (k frame : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (locals : Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (kPositive : 0 < k) (domain : sptDomainEqUnion locals envs.1 envs.2) :
    0 < frame ∧
    values = (List.range values.length).map (fun index => 2 * (index + 1)) ∧
    values.length < k + frame ∧
    ∀ key value, sptLookup key locals = some value → key % 2 = 0 ∧ 0 < key := by
  have positive := positiveCallerFrame k frame values names retCode l1 l2 dest args
    source xs args1 prog ss envs guards conventions maximum
  obtain ⟨_, _, canonical, names1, names2⟩ :=
    returningConventions k values names retCode l1 l2 dest args conventions
  refine ⟨positive, canonical, ?_, ?_⟩
  · by_cases empty : values.length = 0
    · omega
    · have member : 2 * values.length ∈ values := by
        rw [canonical]
        simp only [List.length_map, List.length_range]
        apply List.mem_map.mpr
        refine ⟨values.length - 1, List.mem_range.mpr (by omega), ?_⟩
        congr 1
        omega
      have upper := maxList_ge_of_mem _ (2 * values.length) member
      rw [maxVarHOL] at maximum
      simp only [Flapjack.WordAlloc.max3Eq] at maximum
      omega
  · intro key value lookup
    have live : sptMem key locals := by
      unfold sptMem sptDomain
      rw [lookup]
      simp
    have selected := (domain key).mp live
    obtain ⟨env1, env2⟩ := AllocStateRel.cutEnvs_eq guards.2.2.2.2
    rcases selected with selected | selected
    · have member : sptDomain names.1 key := by
        rw [env1] at selected
        unfold sptMem sptDomain at selected
        unfold sptDomain
        rw [sptLookup_sptInterCases] at selected
        cases a : sptLookup key source.locals <;>
          cases b : sptLookup key names.1 <;>
            simp only [a, b, Option.isSome, Bool.false_eq_true] at selected ⊢
      obtain ⟨even, lower⟩ := names1 key member
      exact ⟨even, by omega⟩
    · have member : sptDomain names.2 key := by
        rw [env2] at selected
        unfold sptMem sptDomain at selected
        unfold sptDomain
        rw [sptLookup_sptInterCases] at selected
        cases a : sptLookup key source.locals <;>
          cases b : sptLookup key names.2 <;>
            simp only [a, b, Option.isSome, Bool.false_eq_true] at selected ⊢
      obtain ⟨even, lower⟩ := names2 key member
      exact ⟨even, by omega⟩

/-- Normal-return restoration from the original Call premises and the full
matching Return result supplied by the already-discharged callee IH. Source
frame/domain, canonical names, name maximum, physical cut keys, copy bounds and
the entire restored caller relation are derived here. The original guarded
continuation IH and actual source continuation run are retained. This is
untagged assembly infrastructure: enclosing target Call clocks/outcomes and
continuation execution still need composition for the full original case. -/
theorem restoreCallerFromBodyReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values returned popped) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      stateRel ac k callerSize frame
        (WordSemStateFiniteExact.setVars values returned popped) restored lens 0 := by
  obtain ⟨gc, tail, popped, sourceFrame, _, _, _, popShape, popRun, domain,
    valid, continuationRun, continuationIH⟩ :=
    sourceReturningContinuation ac values names retCode l1 l2 dest args source sourcePost
      bodyPost result xs args1 prog ss envs location returned guards ih nonzero execution
      notError bodyRun
  have kBound : 4 < k := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  obtain ⟨positive, canonical, nameBound, physical⟩ :=
    returningCallerLocalObligations k frame values names retCode l1 l2 dest args source
      xs args1 prog ss envs popped.locals guards conventions maximum (by omega) domain
  have callerShape : if frame = 0 then callerSize = 0 else callerSize = frame + 1 := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  have callerSizeEq : callerSize = frame + 1 := by
    rw [if_neg (by omega)] at callerShape
    exact callerShape
  have lengthEq := (not_or.mp valid).2
  have countEq : returned.length - (k - 1) =
      Compiler.Backend.WordToStack.numStackRet k values := by
    unfold Compiler.Backend.WordToStack.numStackRet
    omega
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at bodyConclusion
  obtain ⟨bodyRelation, placements⟩ := bodyConclusion
  rw [countEq] at bodyRelation
  subst popped
  obtain ⟨restored, copyRun, restoredRelation⟩ :=
    copyReturnRestoresCallerState ac k frame bodyPost target source.localsSize
      (sptToAList envs.1) gc tail lens values returned (by omega) canonical
      (by omega) (by omega) physical sourceFrame bodyRelation placements
  refine ⟨_, restored, popRun, continuationRun, continuationIH, ?_, ?_⟩
  · rwa [callerSizeEq]
  · rw [callerSizeEq]
    exact restoredRelation

/-- Compose actual guarded callee simulation with full caller restoration.
All body executions/results/resource contracts remain existential outputs;
only the matching Return branch enters restoration. The original source
continuation run and guarded IH are preserved for subsequent target
continuation/whole-Call clock composition. Untagged case-local assembly, not
full comp_correct; no callee target run or body postrelation is assumed. -/
theorem simulateCalleeAndRestoreCaller {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (returnedLocation : WordLocW width) (returned : List (WordLocW width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result returnedLocation returned), bodyPost)) :
    ∃ (calleeSize calleeFrame : Nat) (body : HolProg width) (codeLocation : Nat),
      sptLookup codeLocation source.code = some (args1.length, prog) ∧
      sptLookup codeLocation saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      (calleeSize ≤ saved.stackSpace →
        ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost (some (.result returnedLocation returned)) targetResult
            (callerFrame :: lens) ∧
          (targetResult = some (.result returnedLocation) →
            ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
              (restored : StackSemStateFiniteExact width C F),
              WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
              WordSemStateFiniteExact.evaluate retCode
                (WordSemStateFiniteExact.setVars values returned popped) = (result, sourcePost) ∧
              Seq.Simulation ac retCode (WordSemStateFiniteExact.setVars values returned popped) ∧
              StackSemEvaluate.evaluate
                (copyRetNative false false (k, callerSize, callerFrame) values .skip, targetPost) =
                (none, restored) ∧
              stateRel ac k callerSize callerFrame
                (WordSemStateFiniteExact.setVars values returned popped) restored lens 0)) := by
  obtain ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, simulate⟩ :=
    simulateCalleeBody ac k callerSize callerFrame values names retCode l1 l2 dest args source
      sourcePost bodyPost result (some (.result returnedLocation returned)) saved lens xs args1
      prog ss envs destinationCode destination guards callerRelation pushedRelation conventions
      maximum destinationCompile ih nonzero execution notError bodyRun
  refine ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, ?_⟩
  intro space
  obtain ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion⟩ := simulate space
  refine ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion, ?_⟩
  intro targetReturn
  rw [targetReturn] at conclusion
  exact restoreCallerFromBodyReturn ac k callerSize callerFrame calleeSize calleeFrame
    values names retCode l1 l2 dest args source sourcePost bodyPost result returnedLocation
    returned saved targetPost lens xs args1 prog ss envs guards callerRelation conventions
    maximum ih nonzero execution notError bodyRun conclusion

/-- Derive continuation compiler obligations from the original whole Call
compilation and metadata. Bitmap offset conservation is the original wLive
length result; label inclusion traverses the actual compiled Call/copy wrapper.
This is untagged case-local assembly. Subsequent evaluator monotonicity still
transports these initial-state obligations to the derived restored caller. -/
theorem continuationCompilationFacts {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (target : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg width) (destination : Sum Nat Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    postAllocConventionsHOL k retCode = true ∧ flatExpConventions retCode = true ∧
    maxVarHOL retCode < 2 * frame + 2 * k ∧
    (appListAppend savedBitmaps).length ≤ savedIndex ∧
    savedIndex - (appListAppend savedBitmaps).length ≤ target.bitmaps.length ∧
    (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (savedIndex - (appListAppend savedBitmaps).length)) ∧
    ∀ loc, StackSem.getLabelsExact returnCode loc → StackSem.locCheckExact target.code loc := by
  obtain ⟨savedLength, offset⟩ := wLiveLength names (bs, n) (k, f, frame)
    savedCode (savedBitmaps, savedIndex) ⟨savedCompile, lengthBound⟩
  have retMaximum : maxVarHOL retCode < 2 * frame + 2 * k := by
    rw [maxVarHOL] at maximum
    simp only [Flapjack.WordAlloc.max3Eq] at maximum
    omega
  refine ⟨(returningConventions k values names retCode l1 l2 dest args conventions).1,
    by simpa only [flatExpConventions, Bool.and_true] using flat,
    retMaximum, savedLength, ?_, ?_, ?_⟩
  · rwa [← offset]
  · rwa [← offset]
  · intro loc member
    apply labels loc
    simp only [compNative, destinationCompile, savedCompile, returnCompile,
      Bool.false_eq_true, if_false, Prod.mk.injEq] at compilation
    obtain ⟨rfl, _⟩ := compilation
    simp only [StackSem.getLabelsExact]
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply Or.inr
    rw [getLabelsCopyRet]
    exact member

/-- The actual NONE return-copy/free wrapper is clock-independent for every
outcome, including disabled-stack and stack-bound errors. This composes the
original copy-aux clock theorem with literal StackFree; no successful run or
resource bound is required. Case-local infrastructure without a separate HOL
declaration for the complete wrapper. -/
theorem returnCopyClockFree {width : Nat} [NeZero width] {C F : Type}
    (k f frame : Nat) (values : List Nat) :
    CallReturnEval.ClockFree (C := C) (F := F)
      (copyRetNative false false (k, f, frame) values .skip : HolProg width) := by
  have free : ∀ count : Nat, CallReturnEval.ClockFree (C := C) (F := F)
      (.stackFree count : HolProg width) := by
    intro count target clock
    rw [StackSemEvaluate.evaluate_stackFree, StackSemEvaluate.evaluate_stackFree]
    by_cases enabled : target.useStack = true
    · by_cases outside : target.stack.length < target.stackSpace + count
      · simp [enabled, outside, StackSemStateOps.emptyEnv]
      · simp [enabled, outside]
    · simp [enabled]
  by_cases zero : Compiler.Backend.WordToStack.numStackRet k values = 0
  · simpa only [copyRetNative, zero, if_true] using
      (CallReturnEval.clockFree_skip (width := width) (C := C) (F := F))
  · simp only [copyRetNative, if_false, seqStackFreeNative, zero]
    exact CallReturnEval.clockFree_seq _ _
      (by intro state clock
          exact CallReturnEval.evaluateCopyRetAuxClock k f
            (Compiler.Backend.WordToStack.numStackRet k values) clock state)
      (CallReturnEval.clockFree_seq _ _ (free _) CallReturnEval.clockFree_skip)

/-- Apply the original guarded continuation IH and execute it through the
actual return-copy/free wrapper, carrying the IH's existential extra clock.
All continuation outcomes and the full original result/resource predicate are
retained. Inputs are previously derived source/metadata/restoration facts and
the actual copy run; no continuation target run is assumed. Untagged component
assembly, with whole-Call history/clock/outcome composition still required. -/
theorem executeReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target restored : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (ih : Seq.Simulation ac retCode source)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true)
    (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate
      (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored)) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, f, frame) values compiled,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨extraClock, targetPost, targetResult, continuationRun, conclusion⟩ :=
    ih k f frame sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceRun, notError, related, conventions, flat, compilation, lengthBound,
        bitmapBound, bitmapPrefix, labels, maximum⟩
  have clockFree := returnCopyClockFree (width := width) (C := C) (F := F) k f frame values
  have sameClock := clockFree target target.clock
  rw [show {target with clock := target.clock} = target from rfl, copyRun] at sameClock
  simp only [Prod.map, id_eq, Prod.mk.injEq] at sameClock
  have clockEq : restored.clock = target.clock := by
    have projected := congrArg
      (fun state : StackSemStateFiniteExact width C F => state.clock) sameClock.2
    exact projected
  have clockedCopy := clockFree target (target.clock + extraClock)
  rw [copyRun] at clockedCopy
  simp only [Prod.map, id_eq] at clockedCopy
  have outputClock : {restored with clock := target.clock + extraClock} =
      {restored with clock := restored.clock + extraClock} := by rw [clockEq]
  rw [outputClock] at clockedCopy
  refine ⟨extraClock, targetPost, targetResult, ?_, conclusion⟩
  rw [CallReturnEval.evaluateCopyRetSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate, clockedCopy]
  simp only
  exact continuationRun

/-- Derive code/bitmap growth along the actual returning-call target history.
All runs are observations produced by prelude/callee/restoration assembly;
errors are not erased from the underlying evaluateMono theorem. Register-zero,
decClock and IH extra-clock updates preserve the relevant carrier fields.
Case-local history factoring, not a tagged full Call correctness theorem. -/
theorem returningHistoryGrowth {width : Nat} [NeZero width] {C F : Type}
    (initial saved moved target restored : StackSemStateFiniteExact width C F)
    (prelude arguments callee : HolProg width) (k f frame l1 l2 extraClock : Nat)
    (values : List Nat) (bodyResult : Option (StackSemResult width))
    (preludeRun : StackSemEvaluate.evaluate (prelude, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate (arguments, saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + extraClock}) = (bodyResult, target))
    (copyRun : StackSemEvaluate.evaluate
      (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored)) :
    initial.bitmaps.IsPrefix restored.bitmaps ∧ sptSubspt initial.code restored.code := by
  have preludeGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    prelude initial saved none preludeRun
  have argumentsGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    arguments saved moved none argumentsRun
  have calleeGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono callee
    {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
      clock := (StackSemStateOps.decClock moved).clock + extraClock} target bodyResult calleeRun
  change moved.bitmaps.IsPrefix target.bitmaps ∧ sptSubspt moved.code target.code at calleeGrowth
  have copyGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (copyRetNative false false (k, f, frame) values .skip) target restored none copyRun
  refine ⟨preludeGrowth.1.trans (argumentsGrowth.1.trans (calleeGrowth.1.trans copyGrowth.1)), ?_⟩
  exact sptSubsptTrans _ _ _ ⟨preludeGrowth.2,
    sptSubsptTrans _ _ _ ⟨argumentsGrowth.2,
      sptSubsptTrans _ _ _ ⟨calleeGrowth.2, copyGrowth.2⟩⟩⟩

/-- In the original normal-return result lift, the initial source state
occurs in compCorrectResult only through its handler depth for the exception
lens. Equality of that original field preserves the ENTIRE result predicate,
including mismatched resource outcomes. Case-local infrastructure for the
source continuation/whole Call composition, without a separate HOL original. -/
theorem returningResultInitialHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (initial continuation sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (sourceResult : Option (WordSemResult width)) (targetResult : Option (StackSemResult width))
    (lens : List Nat) (handler : continuation.handler = initial.handler) :
    compCorrectResult ac k f frame continuation sourcePost target sourceResult targetResult lens =
      compCorrectResult ac k f frame initial sourcePost target sourceResult targetResult lens := by
  unfold compCorrectResult
  rw [handler]

/-- Compose original Call/source/compilation obligations with the actual
prelude, callee and restoration history to execute the original guarded
continuation IH. Initial code/bitmap obligations are transported internally;
source handler equality is derived from actual source Return/pop, so the full
conclusion uses the original Call state, for every continuation outcome.
This is untagged normal-return assembly. The actual history/body contract are
outputs of preceding callee simulation; enclosing whole-Call clock/result
transport and other body branches remain to be assembled, not assumed here. -/
theorem simulateReturningContinuationFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨popped, restored, popRun, sourceContinuation, continuationIH, copyRun, restoredRelation⟩ :=
    restoreCallerFromBodyReturn ac k callerSize frame calleeSize calleeFrame values names
      retCode l1 l2 dest args source sourcePost bodyPost result location returned saved target
      lens xs args1 prog ss envs guards callerRelation conventions maximum ih nonzero
      execution notError bodyRun bodyConclusion
  obtain ⟨retConventions, retFlat, retMaximum, retLength, retBitmapBound, retBitmapPrefix, retLabels⟩ :=
    continuationCompilationFacts ac k callerSize frame values names retCode l1 l2 dest args
      initial bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode compiled destination conventions flat maximum destinationCompile savedCompile
      returnCompile compilation lengthBound bitmapBound bitmapPrefix labels
  obtain ⟨bitmapGrowth, codeGrowth⟩ := returningHistoryGrowth initial saved moved target restored
    (.seq destinationCode savedCode)
    (stackArgsNative destination (args.length + 1) (k, callerSize, frame)) callee
    k callerSize frame l1 l2 bodyExtraClock values (some (.result location))
    preludeRun argumentsRun calleeRun copyRun
  have restoredLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset initial.code restored.code codeGrowth loc (retLabels loc member)
  obtain ⟨extraClock, targetPost, targetResult, targetContinuation, conclusion⟩ :=
    executeReturningContinuation ac k callerSize frame values retCode
      (WordSemStateFiniteExact.setVars values returned popped) sourcePost target restored result
      savedBitmaps finalBitmaps savedIndex finalIndex returnCode lens continuationIH
      sourceContinuation notError restoredRelation retConventions retFlat returnCompile retLength
      (retBitmapBound.trans bitmapGrowth.length_le)
      (retBitmapPrefix.trans (bitmapGrowth.drop _)) restoredLabels retMaximum copyRun
  obtain ⟨gc, tail, sourceFrame, _, _, sourceHandler, _, _⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  have poppedHandler : popped.handler = bodyPost.handler := by
    have pop := popRun
    rw [WordSemStateFiniteExact.popEnv, sourceFrame] at pop
    have shape := Option.some.inj pop
    rw [← shape]
  have handler : (WordSemStateFiniteExact.setVars values returned popped).handler = source.handler :=
    poppedHandler.trans sourceHandler
  rw [returningResultInitialHandler ac k callerSize frame source
    (WordSemStateFiniteExact.setVars values returned popped) sourcePost targetPost
    result targetResult lens handler] at conclusion
  exact ⟨popped, restored, extraClock, targetPost, targetResult, popRun, copyRun,
    targetContinuation, conclusion⟩

/-- Derive actual callee and continuation target runs from the original
guarded Call IHs and original compilation/source premises. The matching Return
branch internally assembles source pop, full caller restoration, history
metadata and the continuation IH's existential run/full original-source result.
Every other callee outcome remains in the full body contract. This is untagged
normal-return assembly, not the enclosing all-outcome Call theorem: prelude
execution/relations are outputs of earlier setup and whole-Call clock transport
still needs composition. No callee/continuation target run is assumed. -/
theorem simulateCalleeAndContinueCaller {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (returnedLocation : WordLocW width) (returned : List (WordLocW width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result returnedLocation returned), bodyPost))
    (initial : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (savedCode returnCode compiled : HolProg width)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, callerFrame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex)
      (k, callerSize, callerFrame) = (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n)
      (k, callerSize, callerFrame) = (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved)) :
    ∃ (calleeSize calleeFrame : Nat) (body : HolProg width) (codeLocation : Nat),
      sptLookup codeLocation source.code = some (args1.length, prog) ∧
      sptLookup codeLocation saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      (calleeSize ≤ saved.stackSpace →
        ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost (some (.result returnedLocation returned)) targetResult
            (callerFrame :: lens) ∧
          (targetResult = some (.result returnedLocation) →
            ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
              (restored : StackSemStateFiniteExact width C F)
              (continuationClock : Nat) (finalTarget : StackSemStateFiniteExact width C F)
              (finalResult : Option (StackSemResult width)),
              WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
              StackSemEvaluate.evaluate
                (copyRetNative false false (k, callerSize, callerFrame) values .skip, targetPost) =
                (none, restored) ∧
              StackSemEvaluate.evaluate
                (copyRetNative false false (k, callerSize, callerFrame) values returnCode,
                  {targetPost with clock := targetPost.clock + continuationClock}) =
                (finalResult, finalTarget) ∧
              compCorrectResult ac k callerSize callerFrame source sourcePost
                finalTarget result finalResult lens)) := by
  obtain ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, simulate⟩ :=
    simulateCalleeBody ac k callerSize callerFrame values names retCode l1 l2 dest args source
      sourcePost bodyPost result (some (.result returnedLocation returned)) saved lens xs args1
      prog ss envs destinationCode destination guards callerRelation pushedRelation conventions
      maximum destinationCompile ih nonzero execution notError bodyRun
  refine ⟨calleeSize, calleeFrame, body, codeLocation, sourceCode, targetCode,
    calleeLocalsSize, calleeShape, ?_⟩
  intro space
  obtain ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion⟩ := simulate space
  refine ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    bodyTargetRun, calleeRun, conclusion, ?_⟩
  intro targetReturn
  rw [targetReturn] at conclusion calleeRun
  exact simulateReturningContinuationFromHistory ac k callerSize callerFrame calleeSize calleeFrame
    values names retCode l1 l2 dest args source sourcePost bodyPost result returnedLocation returned
    saved targetPost lens xs args1 prog ss envs guards callerRelation conventions maximum ih
    nonzero execution notError bodyRun conclusion initial moved bs savedBitmaps finalBitmaps
    n savedIndex finalIndex destinationCode savedCode returnCode compiled
    (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) destination extraClock
    flat destinationCompile savedCompile returnCompile compilation lengthBound bitmapBound
    bitmapPrefix labels preludeRun moveRun calleeRun

/-- Lift callee-body observations through the actual whole NONE Call source
evaluation. Every body result, invalid return, failed pop/domain test and
continuation outcome is retained. The trace lift and conditional resource lift
use the original evaluator monotonicity/resource theorems, without a target
run or narrowed successful-return premise. Case-local infrastructure for the
original unmatched-body branch at lines 8620-8648. -/
theorem sourceCallBodyPost {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost)) :
    bodyPost.ffi.ioEvents.IsPrefix sourcePost.ffi.ioEvents ∧
      (miscThe (bodyPost.stackLimit + 1) bodyPost.stackMax > bodyPost.stackLimit →
        miscThe (sourcePost.stackLimit + 1) sourcePost.stackMax > sourcePost.stackLimit) := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  cases bodyResult with
  | none =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact ⟨List.prefix_refl _, fun overflow => overflow⟩
  | some bodyResult =>
    cases bodyResult <;> try (
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact ⟨List.prefix_refl _, fun overflow => overflow⟩)
    case result location returned =>
      simp only at execution
      by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
      · rw [if_pos invalid] at execution
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
        exact ⟨List.prefix_refl _, fun overflow => overflow⟩
      rw [if_neg invalid] at execution
      cases pop : WordSemStateFiniteExact.popEnv bodyPost with
      | none =>
          rw [pop] at execution
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
          exact ⟨List.prefix_refl _, fun overflow => overflow⟩
      | some popped =>
        rw [pop] at execution
        simp only at execution
        have properties := WordSemStateFiniteExact.popEnvConst bodyPost popped pop
        have poppedFfi : popped.ffi = bodyPost.ffi := by
          aesop (config := { enableSimp := false })
        have poppedLimit : popped.stackLimit = bodyPost.stackLimit := by
          aesop (config := { enableSimp := false })
        have poppedMaximum : popped.stackMax = bodyPost.stackMax := by
          aesop (config := { enableSimp := false })
        by_cases domain : sptDomainEqUnion popped.locals envs.1 envs.2
        · rw [if_pos domain] at execution
          constructor
          · have events := WordSemStateFiniteExact.evaluate_io_events_mono retCode
              (WordSemStateFiniteExact.setVars values returned popped) result sourcePost execution
            change popped.ffi.ioEvents.IsPrefix sourcePost.ffi.ioEvents at events
            rwa [poppedFfi] at events
          · intro overflow
            apply WordSemStateFiniteExact.evaluate_stack_limit_stack_max retCode
              (WordSemStateFiniteExact.setVars values returned popped) result sourcePost
            refine ⟨execution, ?_⟩
            change miscThe (popped.stackLimit + 1) popped.stackMax > popped.stackLimit
            rwa [poppedLimit, poppedMaximum]
        · rw [if_neg domain] at execution
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
          rw [poppedFfi, poppedLimit, poppedMaximum]
          exact ⟨List.prefix_refl _, fun overflow => overflow⟩

/-- Lift the unmatched callee-body branch through the actual NONE source
Call. The body contract supplies Halt 2, its trace prefix and exceeded
resource; sourceCallBodyPost transports both observations through every
source continuation outcome. This is the original 8620-8648 branch factoring,
not a full comp_correct port or an assumption of whole target execution. -/
theorem bodyMismatchResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (initial targetPost : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost targetPost bodyResult targetResult (callerFrame :: lens))
    (bodyMismatch : bodyResult.map compileResult ≠ targetResult) :
    compCorrectResult ac k callerSize callerFrame source sourcePost targetPost
      result targetResult lens := by
  unfold compCorrectResult at bodyConclusion
  rw [if_pos bodyMismatch] at bodyConclusion
  obtain ⟨halt, events, overflow⟩ := bodyConclusion
  obtain ⟨traceLift, resourceLift⟩ := sourceCallBodyPost values names retCode l1 l2 dest args
    source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun
  have bodyOverflow : miscThe (bodyPost.stackLimit + 1) bodyPost.stackMax > bodyPost.stackLimit := by
    cases maximum : bodyPost.stackMax <;>
      simpa only [maximum, miscThe, Option.getD_some, Option.getD_none] using overflow
  have finalOverflow := resourceLift bodyOverflow
  unfold stateRel at callerRelation
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    dimension, _⟩ := callerRelation
  have mismatch : result.map compileResult ≠ targetResult := by
    rw [halt]
    cases result with
    | none => simp
    | some value =>
      intro same
      exact CallHelpers.compileResultNot2 value dimension (Option.some.inj same)
  unfold compCorrectResult
  rw [if_pos mismatch]
  refine ⟨halt, events.trans traceLift, ?_⟩
  cases maximum : sourcePost.stackMax <;>
    simpa only [maximum, miscThe, Option.getD_some, Option.getD_none] using finalOverflow

/-- Actual source Call propagation for the original terminal callee branches.
Timeout, resource halt and final FFI retain the exact source post-state; no
continuation is executed. This is case-local evaluator factoring for the
8620-8666 comp_correct split, with no standalone HOL declaration. -/
theorem sourceCallTerminal {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (terminal : bodyResult = some .timeOut ∨ bodyResult = some .notEnoughSpace ∨
      ∃ event, bodyResult = some (.finalFfi event)) :
    result = bodyResult ∧ sourcePost = bodyPost := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  rcases terminal with rfl | rfl | ⟨event, rfl⟩ <;>
    exact ⟨(Prod.mk.inj execution).1.symm, (Prod.mk.inj execution).2.symm⟩

/-- Lift the matching terminal body IH to the entire original caller result
predicate. Exact source terminal propagation discharges the whole Call result
and post-state; the unchanged FFI/clock contract is obtained from the original
body IH. Mismatches use bodyMismatchResult separately. This is an untagged
branch component, not the full native Call execution theorem. -/
theorem bodyTerminalResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (targetPost : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (terminal : bodyResult = some .timeOut ∨ bodyResult = some .notEnoughSpace ∨
      ∃ event, bodyResult = some (.finalFfi event))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost targetPost bodyResult targetResult (callerFrame :: lens))
    (matching : bodyResult.map compileResult = targetResult) :
    compCorrectResult ac k callerSize callerFrame source sourcePost targetPost result targetResult lens := by
  obtain ⟨rfl, rfl⟩ := sourceCallTerminal values names retCode l1 l2 dest args
    source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun terminal
  rcases terminal with rfl | rfl | ⟨event, rfl⟩ <;>
    simpa only [compCorrectResult, matching, ne_eq, not_true_eq_false, ↓reduceIte] using bodyConclusion

/-- Derive the original no-handler exception depth bound from the actual
callee exception run. evaluate_stack_swap locates a SOME-handler frame;
the newly pushed NONE frame cannot be that frame. No depth bound or handler
frame is assumed. Case-local factoring of original lines 8998-9020. -/
theorem exceptionHandlerBelowSavedFrame {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (source bodyPost : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (args1 : List (WordLocW width)) (ss : Option Nat)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value), bodyPost)) :
    source.handler < source.stack.length := by
  have invariant := WordSemStackEq.evaluateStackSwap prog
    (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
  unfold WordSemStackEq.stackSwapPost at invariant
  rw [bodyRun] at invariant
  obtain ⟨bound, nonGC, gc, handler, tail, size, locals, head, _⟩ := invariant
  change source.handler <
    (.stackFrame source.localsSize (sptToAList envs.1)
      (wordSemEnvToList envs.2 source.permute).1 none :: source.stack).length at bound
  change wordSemLastN (source.handler + 1)
    (.stackFrame source.localsSize (sptToAList envs.1)
      (wordSemEnvToList envs.2 source.permute).1 none :: source.stack) =
    .stackFrame size nonGC gc (some handler) :: tail at head
  by_contra outside
  have depth : source.handler = source.stack.length := by
    simp only [List.length_cons] at bound
    omega
  rw [WordSemStackEq.lastNLengthCond _ _ (by simp only [List.length_cons]; omega)] at head
  simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq, reduceCtorEq,
    and_false, false_and] at head

/-- The actual NONE source Call propagates an exception without changing its
post-state or evaluating a continuation. This is evaluator clause factoring,
not a separate HOL declaration. -/
theorem sourceCallException {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width)) (location value : WordLocW width)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value), bodyPost)) :
    result = some (.exception location value) ∧ sourcePost = bodyPost := by
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  exact ⟨(Prod.mk.inj execution).1.symm, (Prod.mk.inj execution).2.symm⟩

/-- Full original NONE exception result contract from the matching callee IH.
The actual source run derives the exception frame depth; the original caller
state relation derives the lens length. Removing the pushed NONE frame from
LASTN therefore preserves every pushLocals relation, local-union and register-1
obligation. No exception relation or depth bound is added. Untagged case-local
assembly for 8998-9020; actual enclosing target Call is assembled separately. -/
theorem bodyExceptionResult {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width)) (location value : WordLocW width)
    (initial targetPost : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost targetPost (some (.exception location value)) (some (.exception location))
      (callerFrame :: lens)) :
    compCorrectResult ac k callerSize callerFrame source sourcePost targetPost result
      (some (.exception location)) lens := by
  have bound := exceptionHandlerBelowSavedFrame prog source bodyPost envs args1 ss location value bodyRun
  have lengthEq := CallReturnSupport.stateRelImpLength ac k callerSize callerFrame source initial
    lens 0 callerRelation
  have depth : source.handler + 1 ≤ lens.length := by omega
  have dropEq : (callerFrame :: lens).drop
      ((callerFrame :: lens).length - (source.handler + 1)) =
      lens.drop (lens.length - (source.handler + 1)) := by
    have subtract : lens.length + 1 - (source.handler + 1) =
        (lens.length - (source.handler + 1)) + 1 := by omega
    simp only [List.length_cons, subtract, List.drop_succ_cons]
  obtain ⟨rfl, postEq⟩ := sourceCallException values names retCode l1 l2 dest args source sourcePost
    bodyPost result location value xs args1 prog ss envs guards nonzero execution bodyRun
  subst sourcePost
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at bodyConclusion ⊢
  change (∃ nonGC gc, stateRel ac k 0 0 (pushLocals nonGC gc bodyPost) targetPost
      ((callerFrame :: lens).drop ((callerFrame :: lens).length - (source.handler + 1))) 0 ∧
      bodyPost.locals = sptUnion (sptFromAList gc) (sptFromAList nonGC) ∧
      targetPost.regs.lookup 1 = some value) at bodyConclusion
  rw [dropEq] at bodyConclusion
  exact bodyConclusion

/-- Exhaustive source callee outcome split derived from the original whole
Call non-error premise. NONE, Break, Continue and Error are rejected by the
actual source Call evaluator; Return, Exception and every terminal constructor
remain. This is untagged case-local evaluator factoring, not a restriction
added to the full correctness theorem. -/
theorem calleeOutcomeCases {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
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

/-- Preserve the actual direct/indirect source code location when extracting
find_code. The original guard determines either the direct destination or the
zero-offset location in the last argument; equal source bodies at different
locations cannot substitute for that location. Untagged case-local evaluator
factoring for actual callee witness selection, with all arity/size guards. -/
theorem sourceCalleeLocation {width : Nat} [NeZero width] (dest : Option Nat)
    (xs : List (WordLocW width)) (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (ssize : Spt Nat) (args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (h : wordSemFindCode dest xs code ssize = some (args1, prog, ss)) :
    ∃ p, sptLookup p code = some (args1.length, prog) ∧ ss = sptLookup p ssize ∧
      (dest = none → args1 = xs.dropLast) ∧ (dest ≠ none → args1 = xs) ∧
      (dest = some p ∨ dest = none ∧ ∃ nonempty : xs ≠ [], xs.getLast nonempty = .loc p 0) := by
  rcases dest with _ | p
  · simp only [wordSemFindCode] at h
    split at h
    · cases h
    rename_i hne
    rcases hv : xs.getLast hne with w | ⟨q, off⟩
    · rw [hv] at h; cases h
    rw [hv] at h
    rcases off with _ | off
    · rcases hp : sptLookup q code with _ | ⟨arity, body⟩
      · simp only [hp] at h; cases h
      simp only [hp] at h
      split at h
      · rename_i hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨q, ?_, rfl, (fun _ => rfl), (fun h => absurd rfl h),
          Or.inr ⟨rfl, hne, hv⟩⟩
        rw [hp, List.length_dropLast, hl]; rfl
      · cases h
    · simp at h
  · simp only [wordSemFindCode] at h
    rcases hp : sptLookup p code with _ | ⟨arity, body⟩
    · rw [hp] at h; cases h
    rw [hp] at h
    simp only at h
    split at h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨p, by rw [hp, hl], rfl, (fun h => absurd h (by simp)), (fun _ => rfl), Or.inl rfl⟩
    · cases h

/-- Extract compilation, callee bounds and bitmap/label context at the actual
source find_code key. The key is supplied by sourceCalleeLocation, not chosen
from any same-body lookup. The full original caller code relation supplies
all compilation/conventions/frame facts at that key. Untagged case-local
infrastructure for the guarded returning-Call body IH setup. -/
theorem calleeCompilationAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat)
    (location : Nat)
    (sourceCode : sptLookup location source.code = some (args1.length, prog))
    (sourceSize : ss = sptLookup location source.stackSize)
    (related : stateRel ac k callerSize callerFrame source target lens 0) :
    ∃ (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
      (body : HolProg width) (calleeSize calleeFrame : Nat),
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location target.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) = (body, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) := by
  unfold stateRel at related
  obtain ⟨_, _, _, _, _, _, _, _, _, kPositive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, code, _⟩ := related
  obtain ⟨conventions, flat, bs, n, bsPost, nPost, calleeSize, stackProg,
    compiled, bitmapLength, bitmapBound, bitmapPrefix, targetCode, localSize⟩ :=
    code location prog args1.length sourceCode
  simp only [compileProgNative] at compiled
  set calleeFrame := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) with frameDef
  rcases bodyCompile : compNative ac false prog (bs, n)
      (k, if calleeFrame = 0 then 0 else calleeFrame + 1, calleeFrame) with ⟨body, bitmaps⟩
  rw [bodyCompile] at compiled
  simp only [Prod.mk.injEq] at compiled
  obtain ⟨rfl, sizeDef, bitmapsDef⟩ := compiled
  subst bitmaps
  rw [sizeDef] at targetCode bodyCompile
  have shape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1 := by
    split_ifs at sizeDef ⊢ <;> omega
  have argumentBound : args1.length - k ≤ calleeFrame := by
    rw [frameDef]
    exact Nat.le_max_right _ _
  have maximumBound : maxVarHOL prog < 2 * calleeFrame + 2 * k := by
    have variableBound := Nat.le_max_left (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
    rw [← frameDef] at variableBound
    omega
  refine ⟨bs, bsPost, n, nPost, body, calleeSize, calleeFrame,
    sourceCode, targetCode, conventions, flat, bodyCompile, bitmapLength,
    bitmapBound, bitmapPrefix, ?_, shape, argumentBound, maximumBound, frameDef⟩
  rwa [sourceSize]

/-- Identify native find_code with lookup at the actual selected source key
after the real call-destination preamble. Direct calls retain their literal
key; indirect calls read the same zero-offset location from the original
register or stack slot. Bounds and useStack come from the full caller relation.
This case-local infrastructure preserves code identity independently of equal
bodies stored at other keys; no target callee execution is assumed. -/
theorem destinationFindAtSourceLocation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (initial destinationTarget : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs : List (WordLocW width)) (location : Nat)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (bad : ¬ wordSemBadDestArgs dest args = true)
    (related : stateRel ac k f frame source initial lens 0)
    (get : WordSemStateFiniteExact.getVars args source = some xs)
    (compiled : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (execution : StackSemEvaluate.evaluate (destinationCode, initial) = (none, destinationTarget))
    (selected : dest = some location ∨ dest = none ∧
      ∃ nonempty : wordSemAddRetLoc ret xs ≠ [],
        (wordSemAddRetLoc ret xs).getLast nonempty = .loc location 0) :
    StackSemControl.findCode destination destinationTarget.regs destinationTarget.code =
      sptLookup location destinationTarget.code := by
  cases dest with
  | some direct =>
    have same : direct = location := by
      rcases selected with same | ⟨impossible, _⟩
      · exact Option.some.inj same
      · cases impossible
    subst direct
    simp only [callDestNative, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    rfl
  | none =>
    have argsNonempty : args ≠ [] := by
      rintro rfl
      simp [wordSemBadDestArgs] at bad
    obtain ⟨xsNonempty, lastVar⟩ := CallDest.getVars_getLast source args xs get argsNonempty
    have lastLocation : xs.getLast xsNonempty = .loc location 0 := by
      rcases selected with impossible | ⟨_, nonempty, lastLocation⟩
      · cases impossible
      · cases ret with
        | none => exact lastLocation
        | some data =>
          rcases data with ⟨values, names, code, l1, l2⟩
          simpa only [wordSemAddRetLoc, List.getLast_cons xsNonempty] using lastLocation
    have localPlacement := StateRelGetVar.stateRel_locals related _ _ lastVar
    have argsLength : ¬ args.length = 0 := by simpa using argsNonempty
    simp only [callDestNative, dif_neg argsLength, Prod.mk.injEq] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    by_cases register : args.getLast argsNonempty / 2 < k
    · rw [if_pos register] at localPlacement
      have read : Compiler.Backend.WordToStackRegFormat.wReg2 (args.getLast argsNonempty) (k, f, frame) =
          ([], args.getLast argsNonempty / 2) := by simp [Compiler.Backend.WordToStackRegFormat.wReg2, register]
      simp only [read, wStackLoadNative] at execution ⊢
      rw [StackSemEvaluate.evaluate_skip] at execution
      obtain ⟨_, rfl⟩ := Prod.mk.inj execution
      simp only [StackSemControl.findCode, localPlacement.2, lastLocation]
    · rw [if_neg register] at localPlacement
      obtain ⟨_, slot, _⟩ := localPlacement
      have read : Compiler.Backend.WordToStackRegFormat.wReg2 (args.getLast argsNonempty) (k, f, frame) =
          ([(k + 1, f - 1 - (args.getLast argsNonempty / 2 - k))], k + 1) := by
        simp [Compiler.Backend.WordToStackRegFormat.wReg2, register]
      simp only [read, wStackLoadNative] at execution ⊢
      have useStack : initial.useStack = true := by
        unfold stateRel at related
        aesop (config := { enableSimp := false })
      set index := f - 1 - (args.getLast argsNonempty / 2 - k) with indexEq
      rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at slot
      split at slot
      swap
      · cases slot
      have bound : initial.stackSpace + index < initial.stack.length :=
        (List.getElem?_eq_some_iff.mp slot).1
      have value : initial.stack[initial.stackSpace + index] = xs.getLast xsNonempty :=
        (List.getElem?_eq_some_iff.mp slot).2
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackLoad,
        if_neg (by simp [useStack]), dif_pos bound] at execution
      simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self] at execution
      rw [StackSemEvaluate.evaluate_skip] at execution
      obtain ⟨_, rfl⟩ := Prod.mk.inj execution
      simp only [StackSemControl.findCode, HolFiniteMapExact.updateEq, FUPDATE_HOL,
        if_true, value, lastLocation]

/-- Complete actual destination/save/argument setup with the original body
IH context tied to the dispatched callee. Source key selection, compilation
at that key, actual destination read and native register/code preservation
construct the final erased-link find_code witness for this exact body. All
original compiler/frame/bitmap/convention/max-var facts are supplied together;
no callee target run, substituted same-body key or body relation is assumed.
This is untagged setup assembly for the original guarded Call case. -/
theorem prepareCalleeDestinationAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (location calleeSize calleeFrame : Nat) (body : HolProg width)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      compNative ac false prog (calleeBs, calleeIndex) (k, calleeSize, calleeFrame) =
        (body, (calleeBsPost, calleeIndexPost)) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code =
        some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      saved.stackSpace = target.stackSpace ∧
      ∃ (stack : List (WordLocW width)) (regs : HolFiniteMapExact Nat (WordLocW width)),
        moved = {saved with
          stackSpace := saved.stackSpace -
            Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k,
          stack := stack, regs := regs} := by
  have originalGuards := guards
  obtain ⟨get, bad, find, _, _⟩ := originalGuards
  obtain ⟨location, sourceCode, sourceSize, _, _, selected⟩ := sourceCalleeLocation dest _
    source.code source.stackSize args1 prog ss find
  obtain ⟨calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, body, calleeSize, calleeFrame,
    _, targetCode, bodyConventions, bodyFlat, bodyCompile, calleeBitmapLength, calleeBitmapBound,
    calleeBitmapPrefix, calleeLocalsSize, calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq⟩ :=
    calleeCompilationAt ac k f frame source target lens args1 prog ss location sourceCode
      sourceSize related
  obtain ⟨destinationTarget, destinationRun, destinationRelation,
    destinationLength, destinationSpace, _⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens destinationCode destination xs
      (some (values, names, retCode, l1, l2)) ⟨bad, related, destinationCompile, get⟩
  obtain ⟨destinationBitmaps, destinationCodeEq⟩ := CallDest.callDest_preserves dest args (k, f, frame)
    destinationCode destination target destinationTarget destinationCompile destinationRun
  have found := destinationFindAtSourceLocation ac k f frame dest args source target
    destinationTarget lens xs location (some (values, names, retCode, l1, l2)) destinationCode
    destination bad related get destinationCompile destinationRun selected
  have destinationLookup : sptLookup location destinationTarget.code =
      some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) := by
    rw [destinationCodeEq]
    exact targetCode
  rw [destinationLookup] at found
  obtain ⟨saved, savedRun, pushedRelation, savedRelation, savedLength, savedSpace, savedRegisters⟩ :=
    evaluateSavedFrame ac k f frame values names retCode l1 l2 dest args source destinationTarget lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex savedCode guards destinationRelation
      conventions maximum savedCompile bitmapLength (by rwa [destinationBitmaps])
      (by rwa [destinationBitmaps])
  have useStack : saved.useStack = true := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have frameBound : saved.stackSpace + f ≤ saved.stack.length := by
    unfold stateRel at savedRelation
    aesop (config := { enableSimp := false })
  have moveBound := stackArgumentFrameBound ac k f frame values names retCode l1 l2 dest args
    source saved lens xs args1 prog ss envs destinationCode destination guards savedRelation
    conventions maximum destinationCompile
  obtain ⟨moved, stack, regs, moveRun, movedState, moveRegisters, _, _, _, _⟩ :=
    evaluateStackArguments k f frame destination (args.length + 1) saved useStack frameBound
      moveBound (by rw [savedSpace, destinationSpace]; exact space)
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono savedCode
    destinationTarget saved none savedRun).2
  have savedLookup : sptLookup location saved.code =
      some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) := by
    exact ((savedGrowth location ((sptMem_iff_lookup _ _).2 ⟨_, destinationLookup⟩)).2).trans destinationLookup
  have movedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, f, frame)) saved moved none moveRun).2
  have registers : ∀ register, register ≠ k → moved.regs.lookup register =
      destinationTarget.regs.lookup register := by
    intro register notScratch
    exact (moveRegisters register notScratch).trans (savedRegisters register notScratch)
  have finalFound := findCodePreserved k destination destinationTarget.regs moved.regs
    destinationTarget.code moved.code
    (.seq (.stackAlloc (calleeSize - (args1.length - k))) body)
    (destinationRegisterBound k f frame values names retCode l1 l2 dest args destinationCode destination
      conventions destinationCompile)
    registers (sptSubsptTrans _ _ _ ⟨savedGrowth, movedGrowth⟩) found
  exact ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions, bodyFlat,
    calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize, calleeShape,
    calleeArgumentBound, bodyMaximum, calleeFrameEq, finalFound, savedSpace.trans destinationSpace, stack, regs,
    movedState⟩

/-- Apply the original guarded callee-body IH to the SAME compiled body,
location and metadata returned by actual returning-Call setup. The original
callee entry relation and existential body execution are proved here, for
all source/target outcomes. Inputs are compilation/setup facts, never a target
body run or assumed post-state relation. Untagged case-local IH composition;
the complete original Call theorem remains to be assembled. -/
theorem simulateCalleeBodyAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens) := by
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  obtain ⟨extraClock, targetPost, targetResult, targetRun, conclusion⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩ k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩
  have allocationClock : ∀ extra : Nat,
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
            clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (none, {entry with clock := entry.clock + extra}) := by
    intro extra
    have success := allocationRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_, rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc, if_neg disabled, if_neg insufficient]
    rfl
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
      (targetResult, targetPost) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extraClock]
    exact targetRun
  exact ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, conclusion⟩


/-- Construct the actual returning-Call prelude and apply the original guarded
body IH to its SAME callee witness. No target evaluation or body result contract
is assumed: both are existential conclusions for every original body outcome.
The callee-capacity implication is the original allocation split; its failing
branch is handled separately by compiledCalleeFrameFailure. Untagged full-case infrastructure. -/
theorem simulatePreparedCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (location calleeSize calleeFrame : Nat) (body : HolProg width)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      compNative ac false prog (calleeBs, calleeIndex) (k, calleeSize, calleeFrame) =
        (body, (calleeBsPost, calleeIndexPost)) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code =
        some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      saved.stackSpace = target.stackSpace ∧
      (calleeSize ≤ target.stackSpace →
        ∃ (entry : StackSemStateFiniteExact width C F) (extraClock : Nat)
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (frame :: lens)) := by
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, movedState⟩ :=
    prepareCalleeDestinationAt ac k f frame values names retCode l1 l2 dest args source target
      lens xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      bitmapPrefix space
  refine ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, ?_⟩
  intro calleeSpace
  have destinationGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun).1
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun).1
  have bitmapGrowth : target.bitmaps.IsPrefix saved.bitmaps :=
    destinationGrowth.trans savedGrowth
  obtain ⟨movedAgain, entry, extraClock, targetPost, targetResult, moveAgain,
    allocationRun, targetRun, calleeRun, conclusion⟩ :=
    simulateCalleeBodyAt ac k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile ih nonzero
      execution notError bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  exact ⟨entry, extraClock, targetPost, targetResult, allocationRun, targetRun, calleeRun,
    conclusion⟩

end Flapjack.WordToStackProofs.CompCorrect.CallReturning
