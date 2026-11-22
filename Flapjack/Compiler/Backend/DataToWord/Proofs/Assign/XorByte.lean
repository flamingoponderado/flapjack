module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.XorLoop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SetGlobal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SmallStateLemmas
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteXorCorrect
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
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

namespace XorByteAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end XorByteAssignmentWitness

/- The following private evaluator and stack facts factor the original proof;
   they are Flapjack infrastructure rather than separate HOL declarations. -/

/-- Sequence a successful assignment; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorEvalSeqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (WordSemStateFiniteExact.setVar key v s) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Cancel an already included optional stack maximum; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorMaxStable (a b c : Option Nat) :
    Option.map₂ max (wordSemOptionMax a (wordSemOptionAdd b c)) (Option.map₂ (· + ·) b c) =
      wordSemOptionMax a (wordSemOptionAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [wordSemOptionMax, wordSemOptionAdd]

/-- Bound the optional stack maximum used for the loop call; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorOptionBound (a b c d : Option Nat) (h : optionLe a d) :
    optionLe (Option.map₂ max (Option.map₂ max a b) (Option.map₂ (· + ·) b c))
      (Option.map₂ max d (Option.map₂ (· + ·) c b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [optionLe]
  all_goals omega

/-- Reconstruct both well-formed cut trees after list conversion; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorRestoredCuts {width : Nat} [NeZero width] (names : WordLangCutsetsHOL)
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

/-- Restore the saved call frame and its stack maximum after the XOR loop; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorCallReturnSetup {width : Nat} [NeZero width] {C F : Type}
    (base : WordSemStateFiniteExact width C F) (first second : Spt (WordLocW width))
    (entries : List (Nat × WordLocW width)) (permute : Nat → Nat → Nat)
    (inputs : List (WordLocW width)) (clock : Nat) (peak : Option Nat)
    (memory : BitVec width → WordLocW width)
    (envEq : wordSemEnvToList second base.permute = (entries, permute))
    (firstEq : sptFromAList (sptToAList first) = first)
    (secondEq : sptFromAList entries = second)
    (entry : WordSemStateFiniteExact width C F)
    (entryEq : entry = WordSemStateFiniteExact.callEnv inputs (sptLookup xorLoopLocation base.stackSize)
      (WordSemStateFiniteExact.pushEnv (first,second) none base))
    (bound : peak ≠ entry.stackMax → peak = Option.map₂ max entry.stackMax
      (Option.map₂ (· + ·) (wordSemStackSize entry.stack) (sptLookup xorLoopLocation entry.stackSize))) :
    let returned := {entry with memory := memory, clock := clock, stackMax := peak, locals := .ln, localsSize := some 0}
    let restored := {returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList first)), stack := base.stack, localsSize := base.localsSize}
    WordSemStateFiniteExact.popEnv returned = some restored ∧
      sptDomainEqUnion restored.locals first second ∧ peak = entry.stackMax := by
  subst entry
  let entry := WordSemStateFiniteExact.callEnv inputs (sptLookup xorLoopLocation base.stackSize)
    (WordSemStateFiniteExact.pushEnv (first,second) none base)
  let returned := {entry with memory := memory, clock := clock, stackMax := peak, locals := .ln, localsSize := some 0}
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
    have stable := xorMaxStable (WordSemStateFiniteExact.pushEnv (first,second) none base).stackMax
      (wordSemStackSize (WordSemStateFiniteExact.pushEnv (first,second) none base).stack)
      (sptLookup xorLoopLocation base.stackSize)
    have sizeEq : entry.stackSize = base.stackSize := by
      simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envEq]
    have cancel : Option.map₂ max entry.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize entry.stack)
          (sptLookup xorLoopLocation entry.stackSize)) = entry.stackMax := by
      rw [sizeEq]
      simpa [entry, WordSemStateFiniteExact.callEnv] using stable
    exact ne (eq.trans cancel)

/-- Preserve the state relation when the XOR loop call accounts for its stack; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorCallStackRelation {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (cut : DataSem.State C F)
    (target base : WordSemStateFiniteExact width C F) (wordCut first second : Spt (WordLocW width))
    (locs : List (Nat × Nat)) (values : List DataSem.Value)
    (baseStack : base.stack = target.stack) (baseSize : base.localsSize = target.localsSize)
    (baseFrames : base.stackSize = target.stackSize) (baseMax : base.stackMax = target.stackMax)
    (related : stateRel conf l1 l2 cut {target with locals := wordCut} none locs) :
    stateRel conf l1 l2 (DataSem.doStack (.memOp .xorByte) values
      (DataSem.doLimSafe cut (.memOp .xorByte) values))
      {target with locals := wordCut, stackMax :=
        (WordSemStateFiniteExact.callEnv [] (sptLookup xorLoopLocation base.stackSize)
          (WordSemStateFiniteExact.pushEnv (first,second) none base)).stackMax} none locs := by
  let sourceNext := DataSem.doStack (.memOp .xorByte) values
    (DataSem.doLimSafe cut (.memOp .xorByte) values)
  let pushed := WordSemStateFiniteExact.pushEnv (first,second) none base
  let entry := WordSemStateFiniteExact.callEnv [] (sptLookup xorLoopLocation base.stackSize) pushed
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
          (sptLookup xorLoopLocation target.stackSize)) := by
    cases h : wordSemEnvToList second base.permute with
    | mk entries permute =>
      simp only [entry, WordSemStateFiniteExact.callEnv, pushed, WordSemStateFiniteExact.pushEnv, h,
        baseFrames, baseMax, optMax, optAdd]
  have sourceMaxEq : sourceNext.stackMax = Option.map₂ max cut.stackMax
      (Option.map₂ (· + ·) (sptLookup xorLoopLocation target.stackSize)
        (Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize)) := by
    simp only [sourceNext, DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed]
    rw [frameSizes, localSizes, sourceStackEq]
  have sourceMaxBound : optionLe entry.stackMax sourceNext.stackMax := by
    rw [targetMaxEq, pushedStack, sourceMaxEq]
    exact xorOptionBound target.stackMax _ _ cut.stackMax oldMax
  have usageBound : optionLe
      (Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize) entry.stackMax := by
    rw [targetMaxEq, pushedStack, optionLe_max_right, optionLe_max_right]
    exact Or.inl (Or.inr (optionLe_refl _))
  have preRel : stateRel conf l1 l2 sourceNext {target with locals := wordCut} none locs :=
    stateRel_doStack conf l1 l2 _ _ locs _ _ (stateRel_doLimSafe conf l1 l2 cut _ locs _ _ related)
  rcases preRel with ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, _, _, p, q, r, s⟩
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, usageBound, sourceMaxBound, p, q, r, s⟩

/-- Evaluate a direct call returning one value from its established guards, callee result and restored frame; local proof infrastructure for `assign_XorByte`, with no separate HOL declaration. -/
private theorem xorEvalDirectReturningCall {width : Nat} [NeZero width] {C F : Type}
    (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (key n l location : Nat) (regs : List Nat)
    (values : List (WordLocW width)) (body : WordLangProgHOL (BitVec width)) (r : WordLocW width)
    (args : WordSemStateFiniteExact.getVars regs s = some values)
    (code : sptLookup location s.code = some (values.length + 1, body))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate body
      (WordSemStateFiniteExact.callEnv (.loc n l :: values) (sptLookup location s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [r]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([key], names, .skip, n, l)) (some location) regs none) s =
      (none, WordSemStateFiniteExact.setVar key r restored) := by
  rw [WordSemStateFiniteExact.evaluate]
  simp only [args, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    wordSemFindCode, code, List.length_cons, if_true, live, not_false_eq_true,
    List.nodup_cons, List.mem_nil_iff, cut, clock]
  simp
  rw [WordSemStateFiniteExact.fix_clock_evaluate, run]
  simp only [List.length_cons, List.length_nil, not_true_eq_false, false_or, if_false]
  rw [pop]
  simp [domain, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.setVars,
    WordSemStateFiniteExact.setVar, LoopSemStateFiniteExact.sptAlistInsert]

/-- Bytewise XOR satisfies the complete original assignment simulation.
The word evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_XorByte"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignXorByte_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .xorByte)
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
  subst opIs
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨wordCut, words, cutWord, getWord, lens1, lens2, relCut, relCutWord⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, argsEq, cutEq⟩
    have cutShape := cutStateOpt_some_eq names source cut cutEq
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
    have refsEq : cut.refs = source.refs := by rw [cutShape]
    have nextRefs : (DataSem.doStack (.memOp .xorByte) [.refPtr b1 p1, .refPtr b2 p2]
        (DataSem.doLimSafe cut (.memOp .xorByte) [.refPtr b1 p1, .refPtr b2 p2])).refs = source.refs :=
      refsEq
    rw [nextRefs] at run
    cases srcLookup : sptLookup p2 source.refs with
    | none => simp [srcLookup] at run
    | some srcRef =>
      cases srcRef with
      | byteArray srcFlag srcBytes =>
        cases dstLookup : sptLookup p1 source.refs with
        | none => simp [srcLookup, dstLookup] at run
        | some dstRef =>
          cases dstRef with
          | byteArray dstFlag dstBytes =>
            cases xorEq : xorBytes srcBytes dstBytes with
            | none => simp [srcLookup, dstLookup, xorEq] at run
            | some updated =>
              simp [srcLookup, dstLookup, xorEq] at run
              let sourceNext := DataSem.doStack (.memOp .xorByte) [.refPtr b1 p1, .refPtr b2 p2]
                (DataSem.doLimSafe cut (.memOp .xorByte) [.refPtr b1 p1, .refPtr b2 p2])
              let newRefs := sptInsert p1 (.byteArray dstFlag updated) source.refs
              have resEq : resultState = {sourceNext with refs := newRefs} := run.2.symm
              obtain rfl := run.1
              subst resEq
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
              let vars := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs
              have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                target.store target.memory target.mdomain target envs [a1, a2]
                [.refPtr b1 p1, .refPtr b2 p2] [v1, v2] (by
                  refine ⟨?_, argsEq, getWord⟩
                  simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
              have swapped : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain ((.refPtr b2 p2, v2) :: (.refPtr b1 p1, v1) :: vars) :=
                memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ (by simpa [vars] using roots)
              have good := related.2.2.2.2.2.2.1
              obtain ⟨w2, adrS, w1, adrD, x1, m1, rfl, rfl, realS, realD, memS, dmS, xorRun, heapRel⟩ :=
                memoryRelXorBytes conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain b2 b1 p2 p1 v2 v1 vars srcFlag dstFlag
                  srcBytes dstBytes updated swapped srcLookup dstLookup xorEq good
              have heapVars : memoryRel conf target.be (holThe source.tstamps) newRefs source.space
                  target.store m1 target.mdomain vars :=
                memoryRel_tl _ _ _ _ _ _ _ _ _ _ (memoryRel_tl _ _ _ _ _ _ _ _ _ _ heapRel)
              have relNew : stateRel conf l1 l2 {source with refs := newRefs} {target with memory := m1} none locs :=
                stateRel_replaceMemory conf l1 l2 source target locs newRefs m1 related
                  (by simpa [vars, envs, List.append_assoc] using heapVars)
              -- Cut the updated state relation to the saved environments.
              cases envRun : DataSem.cutEnv names source.locals with
              | none => simp [DataSem.cutStateOpt, DataSem.cutState, envRun] at cutEq
              | some env =>
              have cutIs : cut = { source with locals := env } := by
                simpa [DataSem.cutStateOpt, DataSem.cutState, envRun] using cutEq.symm
              subst cutIs
              have relNewCut : stateRel conf l1 l2 {source with refs := newRefs, locals := env}
                  {target with memory := m1, locals := wordCut} none locs :=
                stateRel_cutEnv_cutEnv conf l1 l2 {source with refs := newRefs} {target with memory := m1}
                  locs names env wordCut ⟨relNew, envRun, cutWord⟩
              -- Word-side operands.
              simp [WordSemStateFiniteExact.getVars] at getWord
              have reads : WordSemStateFiniteExact.getVar (adjustVar a1) target = some (.word w1) ∧
                  WordSemStateFiniteExact.getVar (adjustVar a2) target = some (.word w2) := by
                cases h1 : WordSemStateFiniteExact.getVar (adjustVar a1) target with
                | none => simp [h1] at getWord
                | some u1 =>
                  cases h2 : WordSemStateFiniteExact.getVar (adjustVar a2) target with
                  | none => simp [h1,h2] at getWord
                  | some u2 =>
                    simp [h1,h2] at getWord
                    obtain ⟨rfl,rfl⟩ := getWord
                    exact ⟨rfl,rfl⟩
              have stubMem : (xorLoopLocation, 4, xorLoopCode) ∈ stubs (width := width) conf := by
                simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
                  fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
                  replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
                  divLocation, modLocation, compare1Location, compareLocation, equal1Location,
                  equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
                  byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
                  installLocation, installCodeLocation, installDataLocation, dummyLocation,
                  appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
                  unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
              have codeLookup : sptLookup xorLoopLocation target.code = some (4, xorLoopCode) :=
                related.2.2.2.2.1.2.1 _ stubMem
              have shiftBound := related.2.2.2.2.2.2.2.1
              have lenPos : 0 < conf.lenSize := by
                obtain ⟨heap, limit, ha, sp, sp1, gens, heapMem, _⟩ := heapRel
                have h := heapMem.2.2.2.1
                omega
              have offsetBound : width - conf.lenSize < width := by
                have positive := NeZero.pos width
                omega
              let len := x1 >>> (width - conf.lenSize)
              let bytes := (wordSemBytesInWord : BitVec width)
              let t1 := WordSemStateFiniteExact.setVar 1 (.word adrD) target
              let t3 := WordSemStateFiniteExact.setVar 3 (.word adrS) t1
              let t5 := WordSemStateFiniteExact.setVar 5 (.word len) t3
              let u1 := WordSemStateFiniteExact.setVar 1 (.word (adrD + bytes)) t5
              let u3 := WordSemStateFiniteExact.setVar 3 (.word (adrS + bytes)) u1
              have exp1 := Bignum.getRealAddr_lemma conf (adjustVar a1) target w1 adrD
                ⟨shiftBound, good, reads.1, realD⟩
              have exp3 : WordSemStateFiniteExact.wordExp t1 (realAddr conf (adjustVar a2)) = some (.word adrS) := by
                apply wordExpRealAddr conf target w2 adrS a2 ⟨realS, shiftBound, good, reads.2⟩ adrD
              have exp5 : WordSemStateFiniteExact.wordExp t3
                  (smallLsr (.load (.var 3)) (width - conf.lenSize)) = some (.word len) := by
                rw [wordExp_smallLsr _ _ _ offsetBound]
                have load : WordSemStateFiniteExact.wordExp t3 (.load (.var 3)) = some (.word x1) := by
                  simp [t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.memLoad,
                    sptLookup_sptInsert_same, dmS, memS]
                rw [load]
              have exp1' : WordSemStateFiniteExact.wordExp t5 (.op .add [.var 1, .const bytes]) =
                  some (.word (adrD + bytes)) := by
                simp [t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                  theWords, wordOpHOL, wordOp]
              have exp3' : WordSemStateFiniteExact.wordExp u1 (.op .add [.var 3, .const bytes]) =
                  some (.word (adrS + bytes)) := by
                simp [u1, t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                  theWords, wordOpHOL, wordOp]
              -- The returning call to the XOR loop.
              obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
                cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
              cases envEq : wordSemEnvToList cutSecond target.permute with
              | mk entries permutation =>
              obtain ⟨firstRestored, secondRestored⟩ := xorRestoredCuts (adjustSets names) target.locals
                cutFirst cutSecond target.permute permutation entries cutPair envEq
              let initial := {u3 with clock := wordSemMustTerminateLimit width, termdep := u3.termdep - 1}
              let callEntry := WordSemStateFiniteExact.callEnv
                [.loc n l, .word (adrD + bytes), .word (adrS + bytes), .word len]
                (sptLookup xorLoopLocation target.stackSize)
                (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
              have clockBound : len.toNat < callEntry.clock := by
                change len.toNat < wordSemMustTerminateLimit width - 1
                have lt := len.isLt
                have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
                simp only [wordSemMustTerminateLimit]
                omega
              have callCode : sptLookup xorLoopLocation callEntry.code = some (4, xorLoopCode) := by
                simpa [callEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                  WordSemStateFiniteExact.decClock, initial, u3, u1, t5, t3, t1,
                  WordSemStateFiniteExact.setVar] using codeLookup
              have loopRun := evaluateXorLoop (adrS + bytes) (adrD + bytes) len target.mdomain target.memory
                n l callEntry m1 (by
                  refine ⟨xorRun, ?_, ?_, clockBound, good, callCode, ?_, ?_, ?_, ?_⟩
                  all_goals simp [callEntry, WordSemStateFiniteExact.callEnv,
                    WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, initial,
                    u3, u1, t5, t3, t1, WordSemStateFiniteExact.setVar,
                    WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
                    sptLookup_sptInsert_same])
              obtain ⟨returnedClock, returnedMax, loopEval, maxBound⟩ := loopRun
              let returned := { callEntry with memory := m1, clock := returnedClock, stackMax := returnedMax, locals := .ln, localsSize := some 0 }
              let restored := { returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst)), stack := initial.stack, localsSize := initial.localsSize }
              have envInitial : wordSemEnvToList cutSecond initial.permute = (entries, permutation) := by
                change wordSemEnvToList cutSecond target.permute = (entries, permutation)
                exact envEq
              have ⟨popRun, domEq, fixedMax⟩ := xorCallReturnSetup
                (WordSemStateFiniteExact.decClock initial) cutFirst cutSecond entries permutation _
                returnedClock returnedMax m1 envInitial firstRestored secondRestored callEntry (by rfl) maxBound
              have increasedRel : stateRel conf l1 l2 {sourceNext with refs := newRefs}
                  {target with memory := m1, locals := wordCut, stackMax := callEntry.stackMax} none locs := by
                exact xorCallStackRelation conf l1 l2 {source with refs := newRefs, locals := env}
                  {target with memory := m1} (WordSemStateFiniteExact.decClock initial)
                  wordCut cutFirst cutSecond locs [.refPtr b1 p1, .refPtr b2 p2]
                  rfl rfl rfl rfl relNewCut
              have normalized : {restored with clock := target.clock, termdep := target.termdep, permute := target.permute} =
                  {target with memory := m1, locals := wordCut, stackMax := callEntry.stackMax} := by
                simp only [restored, returned, fixedMax, callEntry, WordSemStateFiniteExact.callEnv,
                  WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
                  initial, u3, u1, t5, t3, t1, WordSemStateFiniteExact.setVar,
                  secondRestored, firstRestored, ← cutUnion]
              let afterReturn := {restored with clock := target.clock, termdep := target.termdep}
              have afterRel : stateRel conf l1 l2 {sourceNext with refs := newRefs} afterReturn none locs := by
                rw [← normalized] at increasedRel
                exact increasedRel
              have root : memoryRel conf afterReturn.be (holThe {sourceNext with refs := newRefs}.tstamps)
                  {sourceNext with refs := newRefs}.refs {sourceNext with refs := newRefs}.space
                  afterReturn.store afterReturn.memory afterReturn.mdomain
                  ((DataSem.unitValue, .word 2) ::
                    (joinEnv {sourceNext with refs := newRefs}.locals
                      (sptToAList (sptInter afterReturn.locals (adjustSet {sourceNext with refs := newRefs}.locals))) ++
                    [(theGlobal {sourceNext with refs := newRefs}.global, holFapply afterReturn.store .globals)] ++
                    flatStack {sourceNext with refs := newRefs}.stack afterReturn.stack)) :=
                memoryRel_unit _ _ _ _ _ _ _ _ _ ⟨by simpa using afterRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, good⟩
              have finalRel := stateRel_insertRoot conf l1 l2 {sourceNext with refs := newRefs} afterReturn locs dest
                DataSem.unitValue (.word 2) afterRel root
              have cutAt : wordSemCutEnvs (adjustSets names) initial.locals = some (cutFirst, cutSecond) := by
                simpa [initial, u3, u1, t5, t3, t1, WordSemStateFiniteExact.setVar,
                  cutEnvs_adjustSets_insertOdd] using cutPair
              have argsAt : WordSemStateFiniteExact.getVars [1,3,5] initial =
                  some [.word (adrD + bytes), .word (adrS + bytes), .word len] := by
                simp [initial, u3, u1, t5, t3, t1, WordSemStateFiniteExact.setVar,
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
                  (.call (some ([adjustVar dest], adjustSets names, .skip, n, l)) (some xorLoopLocation)
                    [1,3,5] none) initial =
                  (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) restored) := by
                refine xorEvalDirectReturningCall initial returned restored (adjustSets names) cutFirst cutSecond
                  (adjustVar dest) n l xorLoopLocation [1,3,5] _ xorLoopCode (.word 2)
                  argsAt ?_ cutAt namesNonempty neClock ?_ popRun domEq
                · change sptLookup xorLoopLocation target.code = _
                  simpa using codeLookup
                · change WordSemStateFiniteExact.evaluate xorLoopCode callEntry =
                    (some (.result (.loc n l) [.word 2]), returned) at loopEval
                  exact loopEval
              have termNe : u3.termdep ≠ 0 := by
                change target.termdep ≠ 0
                omega
              have wrapped : WordSemStateFiniteExact.evaluate
                  (.mustTerminate (.call (some ([adjustVar dest], adjustSets names, .skip, n, l))
                    (some xorLoopLocation) [1,3,5] none)) u3 =
                  (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) afterReturn) := by
                rw [WordSemStateFiniteExact.evaluate]
                simp only [termNe]
                change (match WordSemStateFiniteExact.evaluate
                  (.call (some ([adjustVar dest], adjustSets names, .skip, n, l)) (some xorLoopLocation)
                    [1,3,5] none) initial with
                  | (res, s1) => match res with
                    | some .timeOut => (some .error, u3)
                    | _ => (res, {s1 with clock := u3.clock, termdep := u3.termdep})) =
                  (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) afterReturn)
                rw [callEval]
                simp [afterReturn, WordSemStateFiniteExact.setVar, u3, u1, t5, t3, t1]
              refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) afterReturn, ?_, by simp, ?_⟩
              · change WordSemStateFiniteExact.evaluate
                  (assignXorByte conf n l dest (some names) a1 a2).1 target = _
                simp only [assignXorByte, wordListSeq, Option.getD_some]
                rw [xorEvalSeqAssign target 1 _ _ _ exp1]
                rw [xorEvalSeqAssign t1 3 _ _ _ exp3]
                rw [xorEvalSeqAssign t3 5 _ _ _ exp5]
                rw [xorEvalSeqAssign t5 1 _ _ _ exp1']
                rw [xorEvalSeqAssign u1 3 _ _ _ exp3']
                exact wrapped
              · simpa [sourceNext] using finalRel
          | _ => simp [srcLookup, dstLookup] at run
      | _ => simp [srcLookup] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
