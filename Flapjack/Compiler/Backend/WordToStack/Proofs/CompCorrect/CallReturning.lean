import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.StackProps.EvaluateMono
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
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode := by
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
    calleeCompile, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize, finalFound⟩

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

end Flapjack.WordToStackProofs.CompCorrect.CallReturning
