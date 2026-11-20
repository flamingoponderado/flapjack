module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StringCmpLoop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StringCompareMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.BackendCommon

namespace StringCmpAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end StringCmpAssignmentWitness

/- The following private evaluator and stack facts factor the original proof;
   they are Flapjack infrastructure rather than separate HOL declarations. -/

/-- Sequence a successful assignment; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (WordSemStateFiniteExact.setVar key v s) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Sequence an assignment nested on the left; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalNestedSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (body tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.seq (.assign key expr) body) tail) s =
      WordSemStateFiniteExact.evaluate (.seq body tail) (WordSemStateFiniteExact.setVar key v s) := by
  simp only [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar, Nat.lt_irrefl, if_false]

/-- Select the equal-word branch inside a sequence; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalSeqIteEqual {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (k1 k2 : Nat) (x : BitVec width)
    (yes tail : WordLangProgHOL (BitVec width))
    (h1 : WordSemStateFiniteExact.getVar k1 s = some (.word x))
    (h2 : WordSemStateFiniteExact.getVar k2 s = some (.word x)) :
    WordSemStateFiniteExact.evaluate (.seq (.ite .equal k1 (.reg k2) yes .skip) tail) s =
      WordSemStateFiniteExact.evaluate (.seq yes tail) s := by
  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
    h1, h2, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]

/-- Expose sequential evaluation using the proved clock theorem; local infrastructure with no separate HOL declaration. -/
private theorem evalSeq {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl
/-- Reassociate word-program evaluation; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalSeqAssoc {width : Nat} [NeZero width] {C F : Type}
    (p q r : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq (.seq p q) r) s =
      WordSemStateFiniteExact.evaluate (.seq p (.seq q r)) s := by
  rw [evalSeq, evalSeq, evalSeq]
  cases e : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 =>
    cases res <;> simp [evalSeq]
/-- Select the unsigned-lower branch inside a sequence; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalSeqIteLower {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (k1 k2 : Nat) (x y : BitVec width)
    (yes tail : WordLangProgHOL (BitVec width))
    (h1 : WordSemStateFiniteExact.getVar k1 s = some (.word x))
    (h2 : WordSemStateFiniteExact.getVar k2 s = some (.word y)) :
    WordSemStateFiniteExact.evaluate (.seq (.ite .lower k1 (.reg k2) yes .skip) tail) s =
      if x.toNat < y.toNat then WordSemStateFiniteExact.evaluate (.seq yes tail) s
      else WordSemStateFiniteExact.evaluate tail s := by
  by_cases h : x.toNat < y.toNat <;>
    simp [evalSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
      h1, h2, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, h]

/-- Cancel an already included optional stack maximum; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem maxStable (a b c : Option Nat) :
    Option.map₂ max (wordSemOptionMax a (wordSemOptionAdd b c)) (Option.map₂ (· + ·) b c) =
      wordSemOptionMax a (wordSemOptionAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [wordSemOptionMax, wordSemOptionAdd]

/-- Bound the optional stack maximum used for the loop call; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem optionBound (a b c d : Option Nat) (h : optionLe a d) :
    optionLe (Option.map₂ max (Option.map₂ max a b) (Option.map₂ (· + ·) b c))
      (Option.map₂ max d (Option.map₂ (· + ·) c b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [optionLe]
  all_goals omega

/-- Reconstruct both well-formed cut trees after list conversion; local infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem restoredCuts {width : Nat} [NeZero width] (names : WordLangCutsetsHOL)
    (env first second : Spt (WordLocW width)) (p permute : Nat → Nat → Nat)
    (entries : List (Nat × WordLocW width))
    (cut : wordSemCutEnvs names env = some (first, second))
    (run : wordSemEnvToList second p = (entries, permute)) :
    sptFromAList (sptToAList first) = first ∧ sptFromAList entries = second := by
  have wf := cutEnvs_wf names env first second cut
  constructor
  · apply (sptEqThm _ _ ⟨sptWfFromAList _, wf.1⟩).2
    intro key
    exact sptLookup_sptFromAList_sptToAList key first
  · apply (sptEqThm _ _ ⟨sptWfFromAList _, wf.2⟩).2
    intro key
    rw [sptLookup_sptFromAList]
    exact (wordSemEnvToListLookupEquiv second p entries permute run).1 key

/-- Restore a saved call frame and its stack maximum. This factors the HOL proof and has no separate HOL declaration. -/
private theorem callReturnSetup {width : Nat} [NeZero width] {C F : Type}
    (base : WordSemStateFiniteExact width C F) (first second : Spt (WordLocW width))
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (inputs : List (WordLocW width)) (clock : Nat) (peak : Option Nat)
    (envEq : wordSemEnvToList second base.permute = (entries, permute))
    (firstEq : sptFromAList (sptToAList first) = first)
    (secondEq : sptFromAList entries = second)
    (entry : WordSemStateFiniteExact width C F)
    (entryEq : entry = WordSemStateFiniteExact.callEnv inputs (sptLookup stringCmpLoopLocation base.stackSize)
      (WordSemStateFiniteExact.pushEnv (first,second) none base))
    (bound : peak ≠ entry.stackMax → peak = Option.map₂ max entry.stackMax
      (Option.map₂ (· + ·) (wordSemStackSize entry.stack) (sptLookup stringCmpLoopLocation entry.stackSize))) :
    let returned := {entry with clock := clock, stackMax := peak, locals := .ln, localsSize := some 0}
    let restored := {returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList first)), stack := base.stack, localsSize := base.localsSize}
    WordSemStateFiniteExact.popEnv returned = some restored ∧
      sptDomainEqUnion restored.locals first second ∧ peak = entry.stackMax := by
  subst entry
  let entry := WordSemStateFiniteExact.callEnv inputs (sptLookup stringCmpLoopLocation base.stackSize)
    (WordSemStateFiniteExact.pushEnv (first,second) none base)
  let returned := {entry with clock := clock, stackMax := peak, locals := .ln, localsSize := some 0}
  let restored := {returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList first)), stack := base.stack, localsSize := base.localsSize}
  change WordSemStateFiniteExact.popEnv returned = some restored ∧
    sptDomainEqUnion restored.locals first second ∧ peak = entry.stackMax
  refine ⟨?_, ?_, ?_⟩
  · simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv, envEq]
  · intro key
    change sptMem key (sptUnion (sptFromAList entries) (sptFromAList (sptToAList first))) ↔ _
    rw [secondEq, firstEq, sptMem_sptUnion]
    exact or_comm
  · by_contra ne
    have eq := bound ne
    have stable := maxStable (WordSemStateFiniteExact.pushEnv (first,second) none base).stackMax
      (wordSemStackSize (WordSemStateFiniteExact.pushEnv (first,second) none base).stack)
      (sptLookup stringCmpLoopLocation base.stackSize)
    have sizeEq : entry.stackSize = base.stackSize := by
      simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envEq]
    have cancel : Option.map₂ max entry.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize entry.stack)
          (sptLookup stringCmpLoopLocation entry.stackSize)) = entry.stackMax := by
      rw [sizeEq]
      simpa [entry, WordSemStateFiniteExact.callEnv] using stable
    exact ne (eq.trans cancel)

/-- Preserve the state relation when a byte-comparison call accounts for its stack. This factors the HOL proof and has no separate HOL declaration. -/
private theorem callStackRelation {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (cut : DataSem.State C F)
    (target base : WordSemStateFiniteExact width C F) (wordCut first second : Spt (WordLocW width))
    (locs : List (Nat × Nat)) (fast : Bool) (cmp : Flapjack.Opb) (values : List DataSem.Value)
    (baseStack : base.stack = target.stack) (baseSize : base.localsSize = target.localsSize)
    (baseFrames : base.stackSize = target.stackSize) (baseMax : base.stackMax = target.stackMax)
    (related : stateRel conf l1 l2 cut {target with locals := wordCut} none locs) :
    stateRel conf l1 l2 (DataSem.doStack (.memOp (.stringCmp fast cmp)) values
      (DataSem.doLimSafe cut (.memOp (.stringCmp fast cmp)) values))
      {target with locals := wordCut, stackMax :=
        (WordSemStateFiniteExact.callEnv [] (sptLookup stringCmpLoopLocation base.stackSize)
          (WordSemStateFiniteExact.pushEnv (first,second) none base)).stackMax} none locs := by
  let sourceNext := DataSem.doStack (.memOp (.stringCmp fast cmp)) values
    (DataSem.doLimSafe cut (.memOp (.stringCmp fast cmp)) values)
  let pushed := WordSemStateFiniteExact.pushEnv (first,second) none base
  let entry := WordSemStateFiniteExact.callEnv [] (sptLookup stringCmpLoopLocation base.stackSize) pushed
  change stateRel conf l1 l2 sourceNext {target with locals := wordCut, stackMax := entry.stackMax} none locs
  have sourceStackEq := stackRel_sizeOfStack related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have frameSizes := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have localSizes := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have oldMax := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have pushedStack : wordSemStackSize pushed.stack =
      Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize := by
    cases h : wordSemEnvToList second base.permute with
    | mk entries permute =>
      simp only [pushed, WordSemStateFiniteExact.pushEnv, h, wordSemStackSize,
        List.foldr_cons, wordSemStackSizeFrame, baseSize, baseStack]
      change wordSemOptionAdd target.localsSize (wordSemStackSize target.stack) =
        Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize
      cases target.localsSize <;> cases wordSemStackSize target.stack <;>
        simp [wordSemOptionAdd, Nat.add_comm]
  have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
    cases x <;> cases y <;> rfl
  have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
    cases x <;> cases y <;> rfl
  have targetMaxEq : entry.stackMax =
      Option.map₂ max (Option.map₂ max target.stackMax (wordSemStackSize pushed.stack))
        (Option.map₂ (· + ·) (wordSemStackSize pushed.stack)
          (sptLookup stringCmpLoopLocation target.stackSize)) := by
    cases h : wordSemEnvToList second base.permute with
    | mk entries permute =>
      simp only [entry, WordSemStateFiniteExact.callEnv, pushed, WordSemStateFiniteExact.pushEnv, h,
        baseFrames, baseMax, optMax, optAdd]
  have sourceMaxEq : sourceNext.stackMax = Option.map₂ max cut.stackMax
      (Option.map₂ (· + ·) (sptLookup stringCmpLoopLocation target.stackSize)
        (Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize)) := by
    simp only [sourceNext, DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed]
    rw [frameSizes, localSizes, sourceStackEq]
  have sourceMaxBound : optionLe entry.stackMax sourceNext.stackMax := by
    rw [targetMaxEq, pushedStack, sourceMaxEq]
    exact optionBound target.stackMax _ _ cut.stackMax oldMax
  have usageBound : optionLe
      (Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize) entry.stackMax := by
    rw [targetMaxEq, pushedStack, optionLe_max_right, optionLe_max_right]
    exact Or.inl (Or.inr (optionLe_refl _))
  have preRel : stateRel conf l1 l2 sourceNext {target with locals := wordCut} none locs :=
    stateRel_doStack conf l1 l2 _ _ locs _ _ (stateRel_doLimSafe conf l1 l2 cut _ locs _ _ related)
  rcases preRel with ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, _, _, p, q, r, s⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, usageBound, sourceMaxBound, p, q, r, s⟩

/-- Evaluate a returning direct call from its established guards, callee result and restored frame. This factors the original proof and has no separate HOL declaration. -/
private theorem evalDirectReturningCall {width : Nat} [NeZero width] {C F : Type}
    (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (n l location : Nat) (regs : List Nat)
    (values : List (WordLocW width)) (body : WordLangProgHOL (BitVec width)) (r1 r2 : WordLocW width)
    (args : WordSemStateFiniteExact.getVars regs s = some values)
    (code : sptLookup location s.code = some (values.length + 1, body))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate body
      (WordSemStateFiniteExact.callEnv (.loc n l :: values) (sptLookup location s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [r1,r2]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([5,7], names, .skip, n, l)) (some location) regs none) s =
      (none, WordSemStateFiniteExact.setVars [5,7] [r1,r2] restored) := by
  rw [WordSemStateFiniteExact.evaluate]
  simp only [args, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    wordSemFindCode, code, List.length_cons, if_true, live, not_false_eq_true,
    List.nodup_cons, List.mem_cons, List.mem_nil_iff, cut, clock]
  simp
  rw [WordSemStateFiniteExact.fix_clock_evaluate, run]
  simp only [List.length_cons, List.length_nil, not_true_eq_false, false_or, if_false]
  rw [pop]
  simp [domain, WordSemStateFiniteExact.evaluate]

/-- String comparison satisfies the complete original assignment simulation.
The word evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_StringCmp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignStringCmp_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ fast cmp, op = .memOp (.stringCmp fast cmp))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨fast, cmp, rfl⟩ := opIs
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨wordCut, words, cutWord, getWord, lens1, lens2, relCut, relCutWord⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, argsEq, cutEq⟩
    have refsEq : cut.refs = source.refs := by
      rw [cutStateOpt_some_eq names source cut cutEq]
    have shape : ∃ b1 p1 b2 p2, values = [.refPtr b1 p1, .refPtr b2 p2] := by
      cases values with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | cons v vs =>
        cases vs with
        | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | cons w ws =>
          cases ws with
          | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi] at run
          | nil =>
            cases v <;> cases w <;>
              simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi]
    obtain ⟨b1, p1, b2, p2, rfl⟩ := shape
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
    have nextRefs : (DataSem.doStack (.memOp (.stringCmp fast cmp))
        [.refPtr b1 p1, .refPtr b2 p2]
        (DataSem.doLimSafe cut (.memOp (.stringCmp fast cmp)) [.refPtr b1 p1, .refPtr b2 p2])).refs = source.refs := by
      exact refsEq
    rw [nextRefs] at run
    cases leftLookup : sptLookup p1 source.refs with
    | none => simp [leftLookup] at run
    | some left =>
      cases left with
      | byteArray leftFlag leftBytes =>
        cases rightLookup : sptLookup p2 source.refs with
        | none => simp [leftLookup, rightLookup] at run
        | some right =>
          cases right with
          | byteArray rightFlag rightBytes =>
            simp [leftLookup, rightLookup] at run
            obtain ⟨rfl, rfl⟩ := run
            have argShape : ∃ a1 a2, args = [a1, a2] := by
              cases args with
              | nil => simp at lens1
              | cons a rest =>
                cases rest with
                | nil => simp at lens1
                | cons b rest =>
                  cases rest with
                  | nil => exact ⟨a, b, rfl⟩
                  | cons c tail => simp at lens1
            obtain ⟨a1, a2, rfl⟩ := argShape
            have wordShape : ∃ v1 v2, words = [v1, v2] := by
              cases words with
              | nil => simp at lens2
              | cons a rest =>
                cases rest with
                | nil => simp at lens2
                | cons b rest =>
                  cases rest with
                  | nil => exact ⟨a, b, rfl⟩
                  | cons c tail => simp at lens2
            obtain ⟨v1, v2, rfl⟩ := wordShape
            let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
              flatStack source.stack target.stack
            have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
              target.store target.memory target.mdomain target envs [a1, a2]
              [.refPtr b1 p1, .refPtr b2 p2] [v1, v2] (by
                refine ⟨?_, argsEq, getWord⟩
                simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            have good := related.2.2.2.2.2.2.1
            obtain ⟨w1, adr1, w2, adr2, r1, r2, rfl, rfl, real1, real2, wordCmp, comparison⟩ :=
              memoryRelStrCmp conf target.be (holThe source.tstamps)
                source.refs source.space target.store target.memory target.mdomain b1 b2 p1 p2 v1 v2
                (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
                leftFlag rightFlag leftBytes rightBytes fast cmp (by simpa using roots) leftLookup rightLookup good
            simp [WordSemStateFiniteExact.getVars] at getWord
            have reads : WordSemStateFiniteExact.getVar (adjustVar a1) target = some (.word w1) ∧
                WordSemStateFiniteExact.getVar (adjustVar a2) target = some (.word w2) := by
              cases h1 : WordSemStateFiniteExact.getVar (adjustVar a1) target with
              | none => simp [h1] at getWord
              | some v1 =>
                cases h2 : WordSemStateFiniteExact.getVar (adjustVar a2) target with
                | none => simp [h1,h2] at getWord
                | some v2 =>
                  simp [h1,h2] at getWord
                  obtain ⟨rfl,rfl⟩ := getWord
                  exact ⟨rfl,rfl⟩
            have stubMem : (stringCmpLoopLocation, 6, stringCmpLoopCode) ∈ stubs (width := width) conf := by
              simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
                fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
                replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
                divLocation, modLocation, compare1Location, compareLocation, equal1Location,
                equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
                byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
                installLocation, installCodeLocation, installDataLocation, dummyLocation,
                appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
                unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
            have codeLookup : sptLookup stringCmpLoopLocation target.code = some (6, stringCmpLoopCode) :=
              related.2.2.2.2.1.2.1 _ stubMem
            simp [wordStrCmp] at wordCmp
            obtain ⟨⟨⟨⟨dm1, dm2⟩, is1⟩, is2⟩, cmpRun⟩ := wordCmp
            cases mem1 : target.memory adr1 with
            | loc l1 l2 => simp [mem1, wordSemIsWordLoc] at is1
            | word hd1 =>
              cases mem2 : target.memory adr2 with
              | loc l1 l2 => simp [mem2, wordSemIsWordLoc] at is2
              | word hd2 =>
                let sourceNext := DataSem.doStack (.memOp (.stringCmp fast cmp))
                  [.refPtr b1 p1, .refPtr b2 p2]
                  (DataSem.doLimSafe cut (.memOp (.stringCmp fast cmp)) [.refPtr b1 p1, .refPtr b2 p2])
                have nextRel : stateRel conf l1 l2 sourceNext target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 cut target locs _ _ relCut)
                let t1 := WordSemStateFiniteExact.setVar 1 (.word adr1) target
                let t3 := WordSemStateFiniteExact.setVar 3 (.word adr2) t1
                let t5 := WordSemStateFiniteExact.setVar 5 (.word (hd1 >>> (width - conf.lenSize - wordShiftAmount width))) t3
                let t7 := WordSemStateFiniteExact.setVar 7 (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) t5
                have rel1 : stateRel conf l1 l2 sourceNext t1 none locs := by
                  simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using nextRel
                have rel3 : stateRel conf l1 l2 sourceNext t3 none locs := by
                  simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel1
                have rel5 : stateRel conf l1 l2 sourceNext t5 none locs := by
                  simpa [t5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel3
                have rel7 : stateRel conf l1 l2 sourceNext t7 none locs := by
                  simpa [t7, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel5
                have shiftBound := related.2.2.2.2.2.2.2.1
                have exp1 := Bignum.getRealAddr_lemma conf (adjustVar a1) target w1 adr1
                  ⟨shiftBound, good, reads.1, real1⟩
                have exp2 : WordSemStateFiniteExact.wordExp t1 (realAddr conf (adjustVar a2)) = some (.word adr2) := by
                  apply wordExpRealAddr conf target w2 adr2 a2
                    ⟨real2, shiftBound, good, reads.2⟩ adr1
                have offsetBound : width - conf.lenSize - wordShiftAmount width < width := by
                  rcases good with h | h <;> subst width <;> simp [wordShiftAmount] <;> omega
                have widthBound : width < 2 ^ width := by
                  rcases good with h | h <;> subst width <;> decide
                have offsetWord : (BitVec.ofNat width (width - conf.lenSize - wordShiftAmount width)).toNat =
                    width - conf.lenSize - wordShiftAmount width := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans offsetBound widthBound)]
                have exp5 : WordSemStateFiniteExact.wordExp t3
                    (shiftN .lsr (.load (.var 1)) (width - conf.lenSize - wordShiftAmount width)) =
                      some (.word (hd1 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                  simp [t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.memLoad, shiftN,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same, dm1, mem1, wordShiftHOL,
                    offsetWord, Nat.not_le_of_gt offsetBound]
                have exp7 : WordSemStateFiniteExact.wordExp t5
                    (shiftN .lsr (.load (.var 3)) (width - conf.lenSize - wordShiftAmount width)) =
                      some (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                  simp [t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.memLoad, shiftN,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same, dm2, mem2, wordShiftHOL,
                    offsetWord, Nat.not_le_of_gt offsetBound]
                cases fast with
                | false =>
                  simp [mem1,mem2,wordSemTheWord] at cmpRun
                  obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
                    cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
                  cases envEq : wordSemEnvToList cutSecond target.permute with
                  | mk entries permutation =>

                    obtain ⟨firstRestored, secondRestored⟩ := restoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permutation entries cutPair envEq
                    let t11 := WordSemStateFiniteExact.setVar 11 (.word (adr1 + wordSemBytesInWord)) t7
                    let t13 := WordSemStateFiniteExact.setVar 13 (.word (adr2 + wordSemBytesInWord)) t11
                    let t9 := WordSemStateFiniteExact.setVar 9 (.word (BitVec.ofNat width (min
                      (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                      (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat))) t13
                    let initial := {t9 with clock := wordSemMustTerminateLimit width, termdep := t9.termdep - 1}
                    let callEntry := WordSemStateFiniteExact.callEnv
                      [.loc n l, .word (adr1 + wordSemBytesInWord), .word (adr2 + wordSemBytesInWord),
                        .word (BitVec.ofNat width (min (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat)),
                        .word (hd1 >>> (width - conf.lenSize - wordShiftAmount width)),
                        .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))]
                      (sptLookup stringCmpLoopLocation target.stackSize)
                      (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
                    have clockBound : 2 ^ width < callEntry.clock := by
                      change 2 ^ width < wordSemMustTerminateLimit width - 1
                      have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
                      simp only [wordSemMustTerminateLimit]
                      omega
                    have callCode : sptLookup stringCmpLoopLocation callEntry.code = some (6, stringCmpLoopCode) := by
                      simpa [callEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                        WordSemStateFiniteExact.decClock, initial, t9, t13, t11, t7, t5, t3, t1,
                        WordSemStateFiniteExact.setVar] using codeLookup
                    have loopRun := evaluateStringCmpLoop (adr1 + wordSemBytesInWord) (adr2 + wordSemBytesInWord)
                      (hd1 >>> (width - conf.lenSize - wordShiftAmount width))
                      (hd2 >>> (width - conf.lenSize - wordShiftAmount width))
                      (BitVec.ofNat width (min (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat)) target.be (2 ^ width)
                      target.mdomain target.memory n l callEntry r1 r2 (by
                        refine ⟨by simpa using cmpRun, ?_, ?_, ?_, clockBound, good, callCode, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        all_goals simp [callEntry, WordSemStateFiniteExact.callEnv,
                          WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, initial,
                          t9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
                          sptLookup_sptInsert_same])
                    obtain ⟨returnedClock, returnedMax, loopEval, maxBound⟩ := loopRun
                    let returned := { callEntry with clock := returnedClock, stackMax := returnedMax, locals := .ln, localsSize := some 0 }
                    let restored := { returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst)), stack := initial.stack, localsSize := initial.localsSize }
                    have envInitial : wordSemEnvToList cutSecond initial.permute = (entries, permutation) := by
                      change wordSemEnvToList cutSecond target.permute = (entries, permutation)
                      exact envEq
                    have ⟨popRun, domEq, fixedMax⟩ := callReturnSetup
                      (WordSemStateFiniteExact.decClock initial) cutFirst cutSecond entries permutation _
                      returnedClock returnedMax envInitial firstRestored secondRestored callEntry (by rfl) maxBound
                    have increasedRel : stateRel conf l1 l2 sourceNext
                        {target with locals := wordCut, stackMax := callEntry.stackMax} none locs := by
                      exact callStackRelation conf l1 l2 cut target (WordSemStateFiniteExact.decClock initial)
                        wordCut cutFirst cutSecond locs false cmp [.refPtr b1 p1, .refPtr b2 p2]
                        rfl rfl rfl rfl relCutWord
                    have normalized : {restored with clock := target.clock, termdep := target.termdep, permute := target.permute} =
                        {target with locals := wordCut, stackMax := callEntry.stackMax} := by
                      simp only [restored, returned, fixedMax, callEntry, WordSemStateFiniteExact.callEnv,
                        WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, 
                        initial, t9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        secondRestored, firstRestored, ← cutUnion]
                    let afterReturn := {restored with clock := target.clock, termdep := target.termdep}
                    have afterRel : stateRel conf l1 l2 sourceNext afterReturn none locs := by
                      rw [← normalized] at increasedRel
                      exact increasedRel
                    let r5 := WordSemStateFiniteExact.setVar 5 (.word r1) afterReturn
                    let r7 := WordSemStateFiniteExact.setVar 7 (.word r2) r5
                    have r5Rel : stateRel conf l1 l2 sourceNext r5 none locs := by
                      simpa [r5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using afterRel
                    have r7Rel : stateRel conf l1 l2 sourceNext r7 none locs := by
                      simpa [r7, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using r5Rel
                    have boolMatch : strCmp false cmp (.implode leftBytes) (.implode rightBytes) =
                        numCmp cmp r1.toNat r2.toNat := by
                      simp only [BitVec.ofNat_toNat] at comparison
                      cases h1 : strCmp false cmp (.implode leftBytes) (.implode rightBytes) <;>
                        cases h2 : numCmp cmp r1.toNat r2.toNat <;> simp_all
                    let out := if numCmp cmp r1.toNat r2.toNat then (18 : BitVec width) else 2
                    let vars := joinEnv sourceNext.locals (sptToAList (sptInter r7.locals (adjustSet sourceNext.locals))) ++
                      [(theGlobal sourceNext.global, holFapply r7.store .globals)] ++ flatStack sourceNext.stack r7.stack
                    have root : memoryRel conf r7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                        r7.store r7.memory r7.mdomain
                        ((DataSem.boolValue (strCmp false cmp (.implode leftBytes) (.implode rightBytes)), .word out) :: vars) := by
                      apply memoryRel_bool conf r7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                        r7.store r7.memory r7.mdomain vars _ _
                      refine ⟨?_, good, ?_, ?_⟩
                      · simpa [vars] using r7Rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                      · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, if_true]
                      · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, Bool.false_eq_true, if_false]
                    have finalRel := stateRel_insertRoot conf l1 l2 sourceNext r7 locs dest
                      (DataSem.boolValue (strCmp false cmp (.implode leftBytes) (.implode rightBytes))) (.word out)
                      r7Rel (by simpa [vars] using root)
                    have exp11 : WordSemStateFiniteExact.wordExp t7 (.op .add [.var 1, .const wordSemBytesInWord]) =
                        some (.word (adr1 + wordSemBytesInWord)) := by
                      simp [t7, t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                        WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                        theWords, wordOpHOL, wordOp]
                    have exp13 : WordSemStateFiniteExact.wordExp t11 (.op .add [.var 3, .const wordSemBytesInWord]) =
                        some (.word (adr2 + wordSemBytesInWord)) := by
                      simp [t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                        WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                        theWords, wordOpHOL, wordOp]
                    have cutAt : wordSemCutEnvs (adjustSets names) initial.locals = some (cutFirst, cutSecond) := by
                      simpa [initial, t9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        cutEnvs_adjustSets_insertOdd] using cutPair
                    have argsAt : WordSemStateFiniteExact.getVars [11,13,9,5,7] initial =
                        some [.word (adr1 + wordSemBytesInWord), .word (adr2 + wordSemBytesInWord),
                          .word (BitVec.ofNat width (min (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                            (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat)),
                          .word (hd1 >>> (width - conf.lenSize - wordShiftAmount width)),
                          .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))] := by
                      simp [initial, t9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                    have neClock : initial.clock ≠ 0 := by
                      change wordSemMustTerminateLimit width ≠ 0
                      have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
                      simp only [wordSemMustTerminateLimit]
                      omega
                    have namesNonempty : ¬sptDomainEmpty (adjustSets names).1 := by
                      intro empty
                      have absent := empty 0
                      exact absent ((sptMem_iff_lookup 0 _).mpr ⟨(), rfl⟩)
                    have callEval : WordSemStateFiniteExact.evaluate
                        (.call (some ([5,7], adjustSets names, .skip, n, l)) (some stringCmpLoopLocation)
                          [11,13,9,5,7] none) initial =
                        (none, WordSemStateFiniteExact.setVars [5,7] [.word r1,.word r2] restored) := by
                      refine evalDirectReturningCall initial returned restored (adjustSets names) cutFirst cutSecond n l
                        stringCmpLoopLocation [11,13,9,5,7] _ stringCmpLoopCode (.word r1) (.word r2)
                        argsAt ?_ cutAt namesNonempty neClock ?_ popRun domEq
                      · change sptLookup stringCmpLoopLocation target.code = _
                        simpa using codeLookup
                      · change WordSemStateFiniteExact.evaluate stringCmpLoopCode callEntry =
                          (some (.result (.loc n l) [.word r1, .word r2]), returned) at loopEval
                        exact loopEval
                    have varsEq : WordSemStateFiniteExact.setVars [5,7] [.word r1,.word r2] restored =
                        WordSemStateFiniteExact.setVar 7 (.word r2) (WordSemStateFiniteExact.setVar 5 (.word r1) restored) := by
                      simp only [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
                        WordSemStateFiniteExact.setVar]
                      rw [sptInsert_swap 5 7 (.word r1) (.word r2) restored.locals (by decide)]
                    have termNe : t9.termdep ≠ 0 := by
                      change target.termdep ≠ 0
                      omega
                    have wrapped : WordSemStateFiniteExact.evaluate
                        (.mustTerminate (.call (some ([5,7], adjustSets names, .skip, n, l))
                          (some stringCmpLoopLocation) [11,13,9,5,7] none)) t9 = (none, r7) := by
                      rw [WordSemStateFiniteExact.evaluate]
                      simp only [termNe]
                      change (match WordSemStateFiniteExact.evaluate
                        (.call (some ([5,7], adjustSets names, .skip, n, l)) (some stringCmpLoopLocation)
                          [11,13,9,5,7] none) initial with
                        | (res, s1) => match res with
                          | some .timeOut => (some .error, t9)
                          | _ => (res, {s1 with clock := t9.clock, termdep := t9.termdep})) = (none, r7)
                      rw [callEval, varsEq]
                      simp [r7, r5, afterReturn, WordSemStateFiniteExact.setVar, t9, t13, t11, t7, t5, t3, t1]
                    have fixedReturn : WordSemStateFiniteExact.fixClock t9 ((none : Option (WordSemResult width)), r7) = (none, r7) := by
                      simp [WordSemStateFiniteExact.fixClock, r7, r5, afterReturn, t9, t13, t11, t7, t5, t3, t1,
                        WordSemStateFiniteExact.setVar]
                    let tmp9 := WordSemStateFiniteExact.setVar 9 (.word (hd1 >>> (width - conf.lenSize - wordShiftAmount width))) t13
                    have exp9 : WordSemStateFiniteExact.wordExp t13 (.var 5) =
                        some (.word (hd1 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                      simp [t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
                        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                    have r5at : WordSemStateFiniteExact.getVar 5 tmp9 =
                        some (.word (hd1 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                      simp [tmp9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                    have r7at : WordSemStateFiniteExact.getVar 7 tmp9 =
                        some (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                      simp [tmp9, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                        WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                    let callProgram : WordLangProgHOL (BitVec width) := WordLangProgHOL.mustTerminate (.call
                      (some ([5,7], adjustSets names, .skip, n, l)) (some stringCmpLoopLocation) [11,13,9,5,7] none)
                    let tail := WordLangProgHOL.seq callProgram (assignCmp (adjustVar dest) cmp 5 7)
                    have minSelect : WordSemStateFiniteExact.evaluate
                        (.seq (.ite .lower 7 (.reg 5) (.assign 9 (.var 7)) .skip) tail) tmp9 =
                          WordSemStateFiniteExact.evaluate tail t9 := by
                      rw [evalSeqIteLower tmp9 7 5 _ _ _ _ r7at r5at]
                      by_cases less : (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat <
                          (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                      · simp only [less, if_true]
                        have exp : WordSemStateFiniteExact.wordExp tmp9 (.var 7) =
                            some (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                          simpa [WordSemStateFiniteExact.wordExp] using r7at
                        rw [evalSeqAssign tmp9 9 _ _ _ exp]
                        have same : WordSemStateFiniteExact.setVar 9
                            (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) tmp9 = t9 := by
                          have minEq : BitVec.ofNat width (min (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                              (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat) =
                                (hd2 >>> (width - conf.lenSize - wordShiftAmount width)) := by
                            rw [Nat.min_eq_right (Nat.le_of_lt less), BitVec.ofNat_toNat]
                            simp
                          simp only [t9, tmp9, minEq, WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
                        rw [same]
                      · simp only [less, if_false]
                        have same : tmp9 = t9 := by
                          have le : (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat ≤
                              (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat := Nat.le_of_not_gt less
                          have minEq : BitVec.ofNat width (min (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                              (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat) =
                                (hd1 >>> (width - conf.lenSize - wordShiftAmount width)) := by
                            rw [Nat.min_eq_left le, BitVec.ofNat_toNat]
                            simp
                          simp only [t9, tmp9, minEq]
                        rw [same]
                    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word out) r7, ?_, by simp, ?_⟩
                    · change WordSemStateFiniteExact.evaluate
                        (assignStringCmp conf n l dest (some names) false cmp a1 a2).1 target = _
                      simp only [assignStringCmp, wordListSeq, Bool.false_eq_true, if_false]
                      rw [evalSeqAssign target 1 _ _ _ exp1]
                      rw [evalSeqAssign t1 3 _ _ _ exp2]
                      rw [evalSeqAssign t3 5 _ _ _ exp5]
                      rw [evalSeqAssign t5 7 _ _ _ exp7]
                      rw [evalSeqAssoc]
                      rw [evalSeqAssign t7 11 _ _ _ exp11]
                      rw [evalSeqAssoc]
                      rw [evalSeqAssign t11 13 _ _ _ exp13]
                      rw [evalSeqAssoc]
                      rw [evalSeqAssign t13 9 _ _ _ exp9]
                      rw [evalSeqAssoc]
                      change WordSemStateFiniteExact.evaluate
                        (.seq (.ite .lower 7 (.reg 5) (.assign 9 (.var 7)) .skip) tail) tmp9 = _
                      rw [minSelect]
                      change WordSemStateFiniteExact.evaluate
                        (.seq (.mustTerminate (.call (some ([5,7], adjustSets names, .skip, n, l))
                          (some stringCmpLoopLocation) [11,13,9,5,7] none))
                          (assignCmp (adjustVar dest) cmp 5 7)) t9 = _
                      rw [WordSemStateFiniteExact.evaluate, wrapped, fixedReturn]
                      simp only
                      rw [evaluateAssignCmp]
                      simp [WordSemStateFiniteExact.getVar, r7, r5, afterReturn,
                        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same, out]
                    · simpa [sourceNext] using finalRel
                | true =>
                  simp [mem1,mem2,wordSemTheWord] at cmpRun
                  by_cases equal : hd1 >>> (width - conf.lenSize - wordShiftAmount width) =
                      hd2 >>> (width - conf.lenSize - wordShiftAmount width)
                  · simp [equal] at cmpRun
                    obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
                      cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
                    cases envEq : wordSemEnvToList cutSecond target.permute with
                    | mk entries permutation =>

                      obtain ⟨firstRestored, secondRestored⟩ := restoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permutation entries cutPair envEq
                      let t11 := WordSemStateFiniteExact.setVar 11 (.word (adr1 + wordSemBytesInWord)) t7
                      let t13 := WordSemStateFiniteExact.setVar 13 (.word (adr2 + wordSemBytesInWord)) t11
                      let initial := {t13 with clock := wordSemMustTerminateLimit width, termdep := t13.termdep - 1}
                      let callEntry := WordSemStateFiniteExact.callEnv
                        [.loc n l, .word (adr1 + wordSemBytesInWord), .word (adr2 + wordSemBytesInWord),
                          .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width)),
                          .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width)),
                          .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))]
                        (sptLookup stringCmpLoopLocation target.stackSize)
                        (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
                      have clockBound : 2 ^ width < callEntry.clock := by
                        change 2 ^ width < wordSemMustTerminateLimit width - 1
                        have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
                        simp only [wordSemMustTerminateLimit]
                        omega
                      have callCode : sptLookup stringCmpLoopLocation callEntry.code = some (6, stringCmpLoopCode) := by
                        simpa [callEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, initial, t13, t11, t7, t5, t3, t1,
                          WordSemStateFiniteExact.setVar] using codeLookup
                      have loopRun := evaluateStringCmpLoop (adr1 + wordSemBytesInWord) (adr2 + wordSemBytesInWord)
                        (hd2 >>> (width - conf.lenSize - wordShiftAmount width))
                        (hd2 >>> (width - conf.lenSize - wordShiftAmount width))
                        (hd2 >>> (width - conf.lenSize - wordShiftAmount width)) target.be (2 ^ width)
                        target.mdomain target.memory n l callEntry r1 r2 (by
                          refine ⟨cmpRun, ?_, ?_, ?_, clockBound, good, callCode, ?_, ?_, ?_, ?_, ?_, ?_⟩
                          all_goals simp [callEntry, WordSemStateFiniteExact.callEnv,
                            WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, initial,
                            t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                            WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
                            sptLookup_sptInsert_same])
                      obtain ⟨returnedClock, returnedMax, loopEval, maxBound⟩ := loopRun
                      let returned := { callEntry with clock := returnedClock, stackMax := returnedMax, locals := .ln, localsSize := some 0 }
                      let restored := { returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst)), stack := initial.stack, localsSize := initial.localsSize }
                      have envInitial : wordSemEnvToList cutSecond initial.permute = (entries, permutation) := by
                        change wordSemEnvToList cutSecond target.permute = (entries, permutation)
                        exact envEq
                      have ⟨popRun, domEq, fixedMax⟩ := callReturnSetup
                        (WordSemStateFiniteExact.decClock initial) cutFirst cutSecond entries permutation _
                        returnedClock returnedMax envInitial firstRestored secondRestored callEntry (by rfl) maxBound
                      have increasedRel : stateRel conf l1 l2 sourceNext
                          {target with locals := wordCut, stackMax := callEntry.stackMax} none locs := by
                        exact callStackRelation conf l1 l2 cut target (WordSemStateFiniteExact.decClock initial)
                          wordCut cutFirst cutSecond locs true cmp [.refPtr b1 p1, .refPtr b2 p2]
                          rfl rfl rfl rfl relCutWord
                      have normalized : {restored with clock := target.clock, termdep := target.termdep, permute := target.permute} =
                          {target with locals := wordCut, stackMax := callEntry.stackMax} := by
                        simp only [restored, returned, fixedMax, callEntry, WordSemStateFiniteExact.callEnv,
                          WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, 
                          initial, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                          secondRestored, firstRestored, ← cutUnion]
                      let afterReturn := {restored with clock := target.clock, termdep := target.termdep}
                      have afterRel : stateRel conf l1 l2 sourceNext afterReturn none locs := by
                        rw [← normalized] at increasedRel
                        exact increasedRel
                      let r5 := WordSemStateFiniteExact.setVar 5 (.word r1) afterReturn
                      let r7 := WordSemStateFiniteExact.setVar 7 (.word r2) r5
                      have r5Rel : stateRel conf l1 l2 sourceNext r5 none locs := by
                        simpa [r5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using afterRel
                      have r7Rel : stateRel conf l1 l2 sourceNext r7 none locs := by
                        simpa [r7, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using r5Rel
                      have boolMatch : strCmp true cmp (.implode leftBytes) (.implode rightBytes) =
                          numCmp cmp r1.toNat r2.toNat := by
                        simp only [BitVec.ofNat_toNat] at comparison
                        cases h1 : strCmp true cmp (.implode leftBytes) (.implode rightBytes) <;>
                          cases h2 : numCmp cmp r1.toNat r2.toNat <;> simp_all
                      let out := if numCmp cmp r1.toNat r2.toNat then (18 : BitVec width) else 2
                      let vars := joinEnv sourceNext.locals (sptToAList (sptInter r7.locals (adjustSet sourceNext.locals))) ++
                        [(theGlobal sourceNext.global, holFapply r7.store .globals)] ++ flatStack sourceNext.stack r7.stack
                      have root : memoryRel conf r7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                          r7.store r7.memory r7.mdomain
                          ((DataSem.boolValue (strCmp true cmp (.implode leftBytes) (.implode rightBytes)), .word out) :: vars) := by
                        apply memoryRel_bool conf r7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                          r7.store r7.memory r7.mdomain vars _ _
                        refine ⟨?_, good, ?_, ?_⟩
                        · simpa [vars] using r7Rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                        · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, if_true]
                        · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, Bool.false_eq_true, if_false]
                      have finalRel := stateRel_insertRoot conf l1 l2 sourceNext r7 locs dest
                        (DataSem.boolValue (strCmp true cmp (.implode leftBytes) (.implode rightBytes))) (.word out)
                        r7Rel (by simpa [vars] using root)
                      have exp11 : WordSemStateFiniteExact.wordExp t7 (.op .add [.var 1, .const wordSemBytesInWord]) =
                          some (.word (adr1 + wordSemBytesInWord)) := by
                        simp [t7, t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                          theWords, wordOpHOL, wordOp]
                      have exp13 : WordSemStateFiniteExact.wordExp t11 (.op .add [.var 3, .const wordSemBytesInWord]) =
                          some (.word (adr2 + wordSemBytesInWord)) := by
                        simp [t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                          theWords, wordOpHOL, wordOp]
                      have cutAt : wordSemCutEnvs (adjustSets names) initial.locals = some (cutFirst, cutSecond) := by
                        simpa [initial, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                          cutEnvs_adjustSets_insertOdd] using cutPair
                      have argsAt : WordSemStateFiniteExact.getVars [11,13,7,7,7] initial =
                          some [.word (adr1 + wordSemBytesInWord), .word (adr2 + wordSemBytesInWord),
                            .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width)),
                            .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width)),
                            .word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))] := by
                        simp [initial, t13, t11, t7, t5, t3, t1, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
                          sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word out) r7, ?_, by simp, ?_⟩
                      · change WordSemStateFiniteExact.evaluate
                          (assignStringCmp conf n l dest (some names) true cmp a1 a2).1 target = _
                        simp only [assignStringCmp, wordListSeq, if_true]
                        rw [evalSeqAssign target 1 _ _ _ exp1]
                        rw [evalSeqAssign t1 3 _ _ _ exp2]
                        rw [evalSeqAssign t3 5 _ _ _ exp5]
                        rw [evalSeqAssign t5 7 _ _ _ exp7]
                        have reg5 : WordSemStateFiniteExact.getVar 5 t7 =
                            some (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                          simp [t7, t5, t3, t1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne, sptLookup_sptInsert_same, equal]
                        have reg7 : WordSemStateFiniteExact.getVar 7 t7 =
                            some (.word (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) := by
                          simp [t7, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_same]
                        rw [evalSeqIteEqual t7 5 7 _ _ _ reg5 reg7]
                        rw [evalNestedSeqAssign t7 11 _ _ _ _ exp11]
                        rw [evalNestedSeqAssign t11 13 _ _ _ _ exp13]
                        have neClock : initial.clock ≠ 0 := by
                          change wordSemMustTerminateLimit width ≠ 0
                          have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
                          simp only [wordSemMustTerminateLimit]
                          omega
                        have namesNonempty : ¬sptDomainEmpty (adjustSets names).1 := by
                          intro empty
                          have absent := empty 0
                          exact absent ((sptMem_iff_lookup 0 _).mpr ⟨(), rfl⟩)
                        have callEval : WordSemStateFiniteExact.evaluate
                            (.call (some ([5,7], adjustSets names, .skip, n, l)) (some stringCmpLoopLocation)
                              [11,13,7,7,7] none) initial =
                            (none, WordSemStateFiniteExact.setVars [5,7] [.word r1,.word r2] restored) := by
                          refine evalDirectReturningCall initial returned restored (adjustSets names) cutFirst cutSecond n l
                            stringCmpLoopLocation [11,13,7,7,7] _ stringCmpLoopCode (.word r1) (.word r2)
                            argsAt ?_ cutAt namesNonempty neClock ?_ popRun domEq
                          · change sptLookup stringCmpLoopLocation target.code = _
                            simpa using codeLookup
                          · change WordSemStateFiniteExact.evaluate stringCmpLoopCode callEntry =
                              (some (.result (.loc n l) [.word r1, .word r2]), returned) at loopEval
                            exact loopEval
                        have varsEq : WordSemStateFiniteExact.setVars [5,7] [.word r1,.word r2] restored =
                            WordSemStateFiniteExact.setVar 7 (.word r2) (WordSemStateFiniteExact.setVar 5 (.word r1) restored) := by
                          simp only [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
                            WordSemStateFiniteExact.setVar]
                          rw [sptInsert_swap 5 7 (.word r1) (.word r2) restored.locals (by decide)]
                        have termNe : t13.termdep ≠ 0 := by
                          change target.termdep ≠ 0
                          omega
                        have wrapped : WordSemStateFiniteExact.evaluate
                            (.mustTerminate (.call (some ([5,7], adjustSets names, .skip, n, l))
                              (some stringCmpLoopLocation) [11,13,7,7,7] none)) t13 = (none, r7) := by
                          rw [WordSemStateFiniteExact.evaluate]
                          simp only [termNe]
                          change (match WordSemStateFiniteExact.evaluate
                            (.call (some ([5,7], adjustSets names, .skip, n, l)) (some stringCmpLoopLocation)
                              [11,13,7,7,7] none) initial with
                            | (res, s1) => match res with
                              | some .timeOut => (some .error, t13)
                              | _ => (res, {s1 with clock := t13.clock, termdep := t13.termdep})) = (none, r7)
                          rw [callEval, varsEq]
                          simp [r7, r5, afterReturn, WordSemStateFiniteExact.setVar, t13, t11, t7, t5, t3, t1]
                        have fixedReturn : WordSemStateFiniteExact.fixClock t13 ((none : Option (WordSemResult width)), r7) = (none, r7) := by
                          simp [WordSemStateFiniteExact.fixClock, r7, r5, afterReturn, t13, t11, t7, t5, t3, t1,
                            WordSemStateFiniteExact.setVar]
                        change WordSemStateFiniteExact.evaluate
                          (.seq (.mustTerminate (.call (some ([5,7], adjustSets names, .skip, n, l))
                            (some stringCmpLoopLocation) [11,13,7,7,7] none))
                            (assignCmp (adjustVar dest) cmp 5 7)) t13 = _
                        rw [WordSemStateFiniteExact.evaluate, wrapped, fixedReturn]
                        simp only
                        rw [evaluateAssignCmp]
                        simp [WordSemStateFiniteExact.getVar, r7, r5, afterReturn,
                          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same, out]
                      · simpa [sourceNext] using finalRel
                  · simp [equal] at cmpRun
                    obtain ⟨rfl,rfl⟩ := cmpRun
                    have boolMatch : strCmp true cmp (.implode leftBytes) (.implode rightBytes) =
                        numCmp cmp (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                          (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat := by
                      simp only [BitVec.ofNat_toNat] at comparison
                      cases h1 : strCmp true cmp (.implode leftBytes) (.implode rightBytes) <;>
                        cases h2 : numCmp cmp (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                          (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat <;> simp_all
                    let out := if numCmp cmp (hd1 >>> (width - conf.lenSize - wordShiftAmount width)).toNat
                      (hd2 >>> (width - conf.lenSize - wordShiftAmount width)).toNat then (18 : BitVec width) else 2
                    let vars := joinEnv sourceNext.locals (sptToAList (sptInter t7.locals (adjustSet sourceNext.locals))) ++
                      [(theGlobal sourceNext.global, holFapply t7.store .globals)] ++ flatStack sourceNext.stack t7.stack
                    have root : memoryRel conf t7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                        t7.store t7.memory t7.mdomain
                        ((DataSem.boolValue (strCmp true cmp (.implode leftBytes) (.implode rightBytes)), .word out) :: vars) := by
                      apply memoryRel_bool conf t7.be (holThe sourceNext.tstamps) sourceNext.refs sourceNext.space
                        t7.store t7.memory t7.mdomain vars _ _
                      refine ⟨?_, good, ?_, ?_⟩
                      · simpa [vars] using rel7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                      · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, if_true]
                      · intro h; have eq := boolMatch.symm.trans h; simp only [out, eq, Bool.false_eq_true, if_false]
                    have finalRel := stateRel_insertRoot conf l1 l2 sourceNext t7 locs dest
                      (DataSem.boolValue (strCmp true cmp (.implode leftBytes) (.implode rightBytes))) (.word out)
                      rel7 (by simpa [vars] using root)
                    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word out) t7, ?_, by simp, ?_⟩
                    · change WordSemStateFiniteExact.evaluate
                        (assignStringCmp conf n l dest (some names) true cmp a1 a2).1 target = _
                      simp only [assignStringCmp, wordListSeq]
                      simp only [t1, t3, t5, WordSemStateFiniteExact.setVar] at exp2 exp5 exp7
                      simp only [if_true, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fixClock,
                        WordSemStateFiniteExact.setVar, Nat.lt_irrefl, if_false, exp1, exp2, exp5, exp7]
                      have boolNe : ((hd1 >>> (width - conf.lenSize - wordShiftAmount width)) ==
                          (hd2 >>> (width - conf.lenSize - wordShiftAmount width))) = false := by
                        exact beq_eq_false_iff_ne.mpr equal
                      simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVarImm,
                        sptLookup_sptInsert_ne, sptLookup_sptInsert_same, wordSemWordCmp,
                        Compiler.Encoders.Asm.wordCmpHOL, boolNe]
                      rw [evaluateAssignCmp]
                      simp [WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne,
                        sptLookup_sptInsert_same, WordSemStateFiniteExact.setVar, t7, t5, t3, t1, out]
                    · simpa [sourceNext] using finalRel
          | _ => simp [leftLookup, rightLookup] at run
      | _ => simp [leftLookup] at run
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
