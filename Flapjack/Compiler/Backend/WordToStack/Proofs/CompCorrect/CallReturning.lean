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
  refine ⟨calleeSize, calleeLocalsSize, ?_⟩
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

end Flapjack.WordToStackProofs.CompCorrect.CallReturning
