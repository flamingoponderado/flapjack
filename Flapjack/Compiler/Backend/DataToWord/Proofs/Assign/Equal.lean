module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.EqualCode
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StringCmpCorrect
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Bool
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Termination

@[expose] public section

/-! Full equality-assignment simulation for the data-to-word pass. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace EqualAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EqualAssignmentWitness

/- These private facts factor the HOL assignment proof; they have no separate HOL declarations. -/
/-- Extract the equality operands and source transition for the assignment proof. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalitySource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp .equal) values source = .val (result, resultState)) :
    ∃ a b flag next, values = [a, b] ∧
      DataSem.doSpace (.blockOp .equal) values source = some next ∧
      DataSem.doEq source.refs a b = .val flag ∧
      result = DataSem.boolValue flag ∧
      resultState = DataSem.doStack (.blockOp .equal) values
        (DataSem.doLimSafe next (.blockOp .equal) values) := by
  cases space : DataSem.doSpace (.blockOp .equal) values source with
  | none => simp [DataSem.doApp, space] at run
  | some next =>
    have refs : next.refs = source.refs := by
      simp [DataSem.doSpace, DataLang.opSpaceReset] at space
      subst next
      rfl
    cases values with
    | nil => simp [DataSem.doApp, space, DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons a rest =>
      cases rest with
      | nil => simp [DataSem.doApp, space, DataSem.doAppAux, DataSem.applyNonFfi] at run
      | cons b rest =>
        cases rest with
        | cons extra rest => simp [DataSem.doApp, space, DataSem.doAppAux, DataSem.applyNonFfi] at run
        | nil =>
          simp only [DataSem.doApp, space, DataSem.doAppAux, DataSem.applyNonFfi] at run
          have refs2 : (DataSem.doStack (.blockOp .equal) [a,b]
            (DataSem.doLimSafe next (.blockOp .equal) [a,b])).refs = source.refs := refs
          rw [refs2] at run
          cases cmp : DataSem.doEq source.refs a b with
          | typeError => simp [cmp] at run
          | val flag =>
            simp [cmp] at run
            exact ⟨a, b, flag, next, rfl, rfl, cmp, run.1.symm, run.2.symm⟩

/-- Sequence a successful assignment in the word evaluator. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalAssignSeq {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (WordSemStateFiniteExact.setVar key v s) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Evaluate the equality compiler’s three scratch-register assignments. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalPrefix {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y)) :
    let t1 := target.setVar 1 (.word x)
    let t3 := t1.setVar 3 (.word y)
    let t5 := t3.setVar 5 (.word (x &&& y))
    WordSemStateFiniteExact.evaluate (assignEqual conf n l dest names a1 a2).1 target =
      WordSemStateFiniteExact.evaluate
        (.seq (.ite .test 5 (.imm 1) .skip
          (.ite .equal 1 (.reg 3) .skip
            (.seq (.mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, n, l))
              (some equalLocation) [1,3] none)) (.assign 3 (.const 1)))))
          (setBool (adjustVar dest) .equal 1 (.reg 3))) t5 := by
  dsimp only
  simp only [assignEqual, wordListSeq]
  rw [evalAssignSeq target 1 (.var (adjustVar a1)) (.word x) _ (by simpa [WordSemStateFiniteExact.wordExp] using hx)]
  have hne : adjustVar a2 ≠ 1 := by simp [adjustVar]
  rw [evalAssignSeq _ 3 (.var (adjustVar a2)) (.word y) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hne] at hy ⊢
    exact hy)]
  rw [evalAssignSeq _ 5 (.op .and [.var 1, .var 3]) (.word (x &&& y)) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne, wordOpHOL, wordOp, theWords, AndOp.and, BitVec.and_allOnes])]
  rfl

/-- Expose sequential evaluation using the evaluator clock theorem. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalSeqLocal {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- Select a word conditional using established operand and comparison results. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalIfLocal {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (cmp : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (yes no : WordLangProgHOL (BitVec width))
    (v1 v2 : WordLocW width) (b : Bool)
    (hr : s.getVar r = some v1) (hi : s.getVarImm ri = some v2)
    (hc : wordSemWordCmp cmp v1 v2 = some b) :
    WordSemStateFiniteExact.evaluate (.ite cmp r ri yes no) s =
      WordSemStateFiniteExact.evaluate (if b then yes else no) s := by
  rw [WordSemStateFiniteExact.evaluate, hr, hi]
  simp only [hc]
  cases b <;> rfl

/-- Evaluate the immediate-value or identical-pointer equality path. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalFastEval {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y))
    (fast : (x &&& y) &&& 1 = 0 ∨ x = y) :
    WordSemStateFiniteExact.evaluate (assignEqual conf n l dest names a1 a2).1 target =
      (none, (((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x &&& y))).setVar
        (adjustVar dest) (.word (if x = y then 18 else 2))) := by
  rw [equalPrefix conf n l dest a1 a2 names target x y hx hy]
  let t := ((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x &&& y))
  have t5 : t.getVar 5 = some (.word (x &&& y)) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have t1 : t.getVar 1 = some (.word x) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  have t3 : t.getVar 3 = some (.word y) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  change WordSemStateFiniteExact.evaluate (.seq _ _) t = _
  rw [evalSeqLocal]
  by_cases hb : (x &&& y) &&& 1 = 0
  · have test : wordSemWordCmp .test (.word (x &&& y)) (.word (1 : BitVec width)) = some true := by
      simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
      change (((x &&& y) &&& (1 : BitVec width)) == 0) = true
      exact beq_iff_eq.mpr hb
    rw [evalIfLocal t .test 5 (.imm 1) _ _ _ _ true t5 (by rfl) test]
    simp only [ite_true, WordSemStateFiniteExact.evaluate]
    simp only [setBool]
    rw [evalIfLocal t .equal 1 (.reg 3) _ _ _ _ (decide (x = y)) t1 (by simpa [WordSemStateFiniteExact.getVarImm] using t3) (by
      simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
      exact beq_eq_decide x y)]
    by_cases hxy : x = y <;> simp [hxy, t, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
  · have xy : x = y := fast.resolve_left hb
    subst y
    have test : wordSemWordCmp .test (.word (x &&& x)) (.word (1 : BitVec width)) = some false := by
      simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
      change (((x &&& x) &&& (1 : BitVec width)) == 0) = false
      exact beq_eq_false_iff_ne.mpr hb
    rw [evalIfLocal t .test 5 (.imm 1) _ _ _ _ false t5 (by rfl) test]
    simp only [Bool.false_eq_true, if_false]
    rw [evalIfLocal t .equal 1 (.reg 3) _ _ _ _ true t1 (by simpa [WordSemStateFiniteExact.getVarImm] using t3) (by
      simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ite_true, WordSemStateFiniteExact.evaluate]
    simp only [setBool]
    rw [evalIfLocal t .equal 1 (.reg 3) _ _ _ _ true t1 (by simpa [WordSemStateFiniteExact.getVarImm] using t3) (by
      simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL])]
    simp [t, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]

/-- Translate a clear low operand bit to the generated test mask. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem lowAndZero {width : Nat} (x y : BitVec width)
    (h : x.getLsbD 0 = false ∨ y.getLsbD 0 = false) :
    (x &&& y) &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  match i with
  | 0 => rcases h with h | h <;> simp [h]
  | j + 1 => simp [Nat.testBit_succ]

/-- Insert the Boolean equality result into related source and target states. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalInsertBool {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (answer : Bool) (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 (DataSem.setVar dest (DataSem.boolValue answer) source)
      (target.setVar (adjustVar dest) (.word (if answer then 18 else 2))) none locs := by
  apply stateRel_insertRoot conf l1 l2 source target locs dest _ _ related
  apply memoryRel_bool conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ _ _
  refine ⟨related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, related.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro h; simp [h]
  · intro h; simp [h]

/-- Reconstruct both cut environments after saving a call frame. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalRestoredCuts {width : Nat} [NeZero width] (names : WordLangCutsetsHOL)
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

/-- Evaluate the returning equality stub call from its established premises. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalDirectCall {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (n l : Nat) (x y res : BitVec width)
    (args : s.getVars [1,3] = some [.word x, .word y])
    (code : sptLookup equalLocation s.code = some (3, equalCode conf))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate (equalCode conf)
      (WordSemStateFiniteExact.callEnv [.loc n l, .word x, .word y] (sptLookup equalLocation s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [.word res]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([1], names, .skip, n, l)) (some equalLocation) [1,3] none) s =
      (none, WordSemStateFiniteExact.setVars [1] [.word res] restored) := by
  rw [WordSemStateFiniteExact.evaluate]
  simp only [args, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    wordSemFindCode, code, List.length_cons, live, not_false_eq_true,
    List.nodup_cons, List.mem_nil_iff, cut, clock]
  simp
  rw [WordSemStateFiniteExact.fix_clock_evaluate, run]
  simp only [List.length_cons, List.length_nil, not_true_eq_false, false_or, if_false]
  rw [pop]
  simp [domain, WordSemStateFiniteExact.evaluate]

/-- Bound the target call stack maximum by the source operation budget. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalStackAlgebra (targetMax sourceMax used frame budget : Option Nat)
    (oldMax : optionLe targetMax sourceMax) (usedMax : optionLe used targetMax)
    (frameBudget : optionLe frame budget) :
    optionLe
      (Option.map₂ max (Option.map₂ max (Option.map₂ max targetMax used)
        (Option.map₂ (· + ·) used frame)) (Option.map₂ (· + ·) used budget))
      (Option.map₂ max sourceMax (Option.map₂ (· + ·) budget used)) := by
  cases targetMax <;> cases sourceMax <;> cases used <;> cases frame <;> cases budget <;>
    simp_all [optionLe]; omega

/-- Bound the equality stub’s frame size by its recursive stack budget. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem equalFrameBound (depth : Nat) (sizes : Spt Nat) :
    optionLe (sptLookup equalLocation sizes) (DataSem.eqCodeStackMax (depth + 1) sizes) := by
  rw [eqCodeStackMax_sub1 (depth + 1) sizes (by omega)]
  cases he : sptLookup equalLocation sizes <;>
    cases h1 : sptLookup equal1Location sizes <;>
    cases hc : sptLookup compare1Location sizes <;>
    cases ht : DataSem.eqCodeStackMax (depth + 1 - 1) sizes <;>
    simp_all [optionLe]; omega

/-- General equality satisfies the complete HOL assignment simulation.
The word evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Equal"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignEqual_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .blockOp .equal)
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
  subst op
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some names =>
    obtain ⟨wordCut, words, cutWord, getWord, lens1, lens2, relCut, relCutWord⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, argsEq, cutEq⟩
    have refsEq : cut.refs = source.refs := by
      rw [cutStateOpt_some_eq names source cut cutEq]
    obtain ⟨a, b, flag, next, valuesEq, spaceEq, compare, resultEq, stateEq⟩ :=
      equalitySource values cut resultState result run
    subst values
    subst result
    subst resultState
    rw [refsEq] at compare
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
    have wordShape : ∃ w1 w2, words = [w1, w2] := by
      cases words with
      | nil => simp at lens2
      | cons a rest =>
        cases rest with
        | nil => simp at lens2
        | cons b rest =>
          cases rest with
          | nil => exact ⟨a, b, rfl⟩
          | cons c tail => simp at lens2
    obtain ⟨w1, w2, rfl⟩ := wordShape
    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
      flatStack source.stack target.stack
    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
      target.store target.memory target.mdomain target envs [a1, a2] [a, b] [w1, w2] (by
        refine ⟨?_, argsEq, getWord⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have good := related.2.2.2.2.2.2.1
    obtain ⟨x, y, rfl, rfl, immediate⟩ :=
      memoryRel_simpleEq conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain a b w1 w2 flag
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
        ⟨by simpa using roots, compare, good⟩
    simp [WordSemStateFiniteExact.getVars] at getWord
    have reads : WordSemStateFiniteExact.getVar (adjustVar a1) target = some (.word x) ∧
        WordSemStateFiniteExact.getVar (adjustVar a2) target = some (.word y) := by
      cases h1 : WordSemStateFiniteExact.getVar (adjustVar a1) target with
      | none => simp [h1] at getWord
      | some v1 =>
        cases h2 : WordSemStateFiniteExact.getVar (adjustVar a2) target with
        | none => simp [h1, h2] at getWord
        | some v2 =>
          simp [h1, h2] at getWord
          obtain ⟨rfl, rfl⟩ := getWord
          exact ⟨rfl, rfl⟩
    obtain ⟨wordResult, remaining, remainingClock, wordRun, wordCorrect⟩ :=
      wordEqThm conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain a b x y
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
        flag ⟨by simpa using roots, compare, good⟩
    have codeMembership :
        (equalLocation, 3, equalCode conf) ∈ stubs (width := width) conf ∧
        (equal1Location, 4, equal1Code) ∈ stubs (width := width) conf ∧
        (compare1Location, 4, compare1Code) ∈ stubs (width := width) conf := by
      simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
        fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
        replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
        divLocation, modLocation, compare1Location, compareLocation, equal1Location,
        equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
        byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
        installLocation, installCodeLocation, installDataLocation, dummyLocation,
        appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
        unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
    have codeEqual : sptLookup equalLocation target.code = some (3, equalCode conf) :=
      related.2.2.2.2.1.2.1 _ codeMembership.1
    have codeEqual1 : sptLookup equal1Location target.code = some (4, equal1Code) :=
      related.2.2.2.2.1.2.1 _ codeMembership.2.1
    have codeCompare1 : sptLookup compare1Location target.code = some (4, compare1Code) :=
      related.2.2.2.2.1.2.1 _ codeMembership.2.2
    have nextRel : stateRel conf l1 l2 next target none locs := by
      simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
      subst next
      rcases relCut with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
        htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
      refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
        hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
      exact memoryRel_zeroSpace conf target.be (holThe cut.tstamps) cut.refs
        cut.space target.store target.memory target.mdomain _ hmem
    have finalSourceRel : stateRel conf l1 l2
        (DataSem.doStack (.blockOp .equal) [a,b] (DataSem.doLimSafe next (.blockOp .equal) [a,b]))
        target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 next target locs _ _ nextRel)
    by_cases fast : (x.getLsbD 0 = false ∨ y.getLsbD 0 = false) ∨ x = y
    · have eqResult : (x = y) ↔ flag = true := by
        rcases fast with imm | same
        · exact immediate imm
        · have truth : flag = true := by
            subst y
            exact memoryRel_pointerEq conf target.be (holThe source.tstamps) source.refs source.space
              target.store target.memory target.mdomain a b (.word x) flag
              (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
              ⟨by simpa using roots, good, compare⟩
          exact ⟨fun _ => truth, fun _ => same⟩
      have flagResult : (if x = y then (18 : BitVec width) else 2) =
          (if flag then 18 else 2) := by
        cases flag <;> simp_all
      let src := DataSem.doStack (.blockOp .equal) [a,b] (DataSem.doLimSafe next (.blockOp .equal) [a,b])
      change stateRel conf l1 l2 src target none locs at finalSourceRel
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x &&& y))
      have rel1 : stateRel conf l1 l2 src t1 none locs := by
        simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using finalSourceRel
      have rel3 : stateRel conf l1 l2 src t3 none locs := by
        simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel1
      have rel5 : stateRel conf l1 l2 src t5 none locs := by
        simpa [t5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel3
      have outputRel := equalInsertBool conf l1 l2 src t5 locs dest flag rel5
      refine ⟨none, t5.setVar (adjustVar dest) (.word (if flag then 18 else 2)), ?_, ?_, ?_⟩
      · have eval := equalFastEval conf n l dest a1 a2 (some names) target x y reads.1 reads.2
          (fast.elim (fun h => Or.inl (lowAndZero x y h)) Or.inr)
        rw [flagResult] at eval
        simpa [compileAssign, arg2, t5, t3, t1] using eval
      · simp
      · intro _
        exact ⟨outputRel, rfl⟩
    · obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
        cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x &&& y))
      let initial := {t5 with clock := wordSemMustTerminateLimit width, termdep := t5.termdep - 1}
      let entry := WordSemStateFiniteExact.callEnv [.loc n l, .word x, .word y]
        (sptLookup equalLocation target.stackSize)
        (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
      have configBounds : conf.lenSize ≠ 0 ∧ conf.lenSize < width := by
        obtain ⟨heap, limit, addr, sp, sp1, gens, heapMem, _⟩ := roots
        have nonzero : conf.lenSize ≠ 0 := heapMem.2.2.2.1
        have bound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
        exact ⟨nonzero, by omega⟩
      have callEval := equalCode_correct conf target.store target.mdomain target.memory
        (wordSemMustTerminateLimit width - 1) (min (DataSem.valueDepth a) (DataSem.valueDepth b))
        x y entry n l wordResult remaining remainingClock (by
          refine ⟨wordRun, ?_, ?_, ?_, ?_, related.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, configBounds.1, configBounds.2, good⟩
          all_goals simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
            WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
            sptLookup_sptInsert_same, codeEqual, codeEqual1, codeCompare1])
      obtain ⟨returnedClock, returnedPermute, returnedMax, stubEval, stubMax, clockLeft⟩ := callEval
      cases envEq : wordSemEnvToList cutSecond target.permute with
      | mk entries permute =>
        obtain ⟨firstRestored, secondRestored⟩ :=
          equalRestoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permute entries cutPair envEq
        let returned := {entry with clock := returnedClock, locals := .ln, localsSize := some 0, permute := returnedPermute, stackMax := returnedMax}
        let restored := {returned with locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst)), stack := target.stack, localsSize := target.localsSize}
        have popRun : WordSemStateFiniteExact.popEnv returned = some restored := by
          simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
            WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar, envEq]
        have domain : sptDomainEqUnion restored.locals cutFirst cutSecond := by
          intro key
          change sptMem key (sptUnion (sptFromAList entries) (sptFromAList (sptToAList cutFirst))) ↔ _
          rw [secondRestored, firstRestored, sptMem_sptUnion]
          exact or_comm
        let used := Option.map₂ (· + ·) (wordSemStackSize target.stack) target.localsSize
        let budget := DataSem.eqCodeStackMax (min (DataSem.valueDepth a) (DataSem.valueDepth b) + 1) target.stackSize
        have oldUsage : optionLe used target.stackMax := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have oldMax : optionLe target.stackMax cut.stackMax := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have stackSizeEq := stackRel_sizeOfStack relCut.2.2.2.2.2.2.2.2.2.2.2.2.1
        have frameSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have localSizeEq := relCut.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have entryStack : wordSemStackSize entry.stack = used := by
          simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
            envEq, wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
          change wordSemOptionAdd target.localsSize (wordSemStackSize target.stack) = used
          cases hlocal : target.localsSize <;> cases hstack : wordSemStackSize target.stack <;>
            simp [used, wordSemOptionAdd, hlocal, hstack, Nat.add_comm]
        have entrySize : entry.stackSize = target.stackSize := by
          simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar, envEq]
        have optMax (a b : Option Nat) : wordSemOptionMax a b = Option.map₂ max a b := by
          cases a <;> cases b <;> rfl
        have optAdd (a b : Option Nat) : wordSemOptionAdd a b = Option.map₂ (· + ·) a b := by
          cases a <;> cases b <;> rfl
        have swapUsed : wordSemOptionAdd target.localsSize (wordSemStackSize target.stack) = used := by
          cases hlocal : target.localsSize <;> cases hstack : wordSemStackSize target.stack <;>
            simp [used, wordSemOptionAdd, hlocal, hstack, Nat.add_comm]
        have entryMaxEq : entry.stackMax =
            Option.map₂ max (Option.map₂ max target.stackMax used)
              (Option.map₂ (· + ·) used (sptLookup equalLocation target.stackSize)) := by
          simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar, envEq,
            wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
          change wordSemOptionMax
            (wordSemOptionMax target.stackMax (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack)))
            (wordSemOptionAdd (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack))
              (sptLookup equalLocation target.stackSize)) = _
          rw [swapUsed]
          simp only [optMax, optAdd]
        have sourceMaxEq : (DataSem.doStack (.blockOp .equal) [a,b]
            (DataSem.doLimSafe next (.blockOp .equal) [a,b])).stackMax =
            Option.map₂ max cut.stackMax (Option.map₂ (· + ·) budget used) := by
          simp only [DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed]
          have nextFields : next.stackFrameSizes = cut.stackFrameSizes ∧ next.stack = cut.stack ∧
              next.localsSize = cut.localsSize ∧ next.stackMax = cut.stackMax := by
            simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
            subst next
            exact ⟨rfl, rfl, rfl, rfl⟩
          rw [nextFields.1, nextFields.2.1, nextFields.2.2.1, nextFields.2.2.2,
            ← frameSizeEq, ← localSizeEq, ← stackSizeEq]
          have minEq : min (DataSem.valueDepth a + 1) (DataSem.valueDepth b + 1) =
              min (DataSem.valueDepth a) (DataSem.valueDepth b) + 1 := by omega
          simp [budget, used, minEq]
        have bound : optionLe returnedMax (DataSem.doStack (.blockOp .equal) [a,b]
            (DataSem.doLimSafe next (.blockOp .equal) [a,b])).stackMax := by
          apply optionLe_trans _ _ _ ⟨stubMax, ?_⟩
          rw [entryStack, entrySize, entryMaxEq, sourceMaxEq]
          exact equalStackAlgebra target.stackMax cut.stackMax used _ budget oldMax oldUsage
            (equalFrameBound (min (DataSem.valueDepth a) (DataSem.valueDepth b)) target.stackSize)
        have entryBelow : optionLe entry.stackMax returnedMax := by
          have growth := WordSemStateFiniteExact.evaluate_stack_max_le (equalCode conf) entry
            (some (.result (.loc n l) [.word wordResult])) returned stubEval
          exact growth
        have usedBelow : optionLe used returnedMax := by
          apply optionLe_trans _ _ _ ⟨?_, entryBelow⟩
          rw [entryMaxEq, optionLe_max_right, optionLe_max_right]
          exact Or.inl (Or.inr (optionLe_refl _))
        have cutNextRel : stateRel conf l1 l2 next {target with locals := wordCut} none locs := by
          simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
          subst next
          rcases relCutWord with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
            htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
          refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
            hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
          exact memoryRel_zeroSpace conf target.be (holThe cut.tstamps) cut.refs
            cut.space target.store target.memory target.mdomain _ hmem
        let src := DataSem.doStack (.blockOp .equal) [a,b] (DataSem.doLimSafe next (.blockOp .equal) [a,b])
        have preRel : stateRel conf l1 l2 src {target with locals := wordCut} none locs :=
          stateRel_doStack conf l1 l2 _ _ locs _ _
            (stateRel_doLimSafe conf l1 l2 next _ locs _ _ cutNextRel)
        have returnedRel : stateRel conf l1 l2 src
            {target with locals := wordCut, stackMax := returnedMax} none locs := by
          rcases preRel with ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, _, _, p, q, r, s⟩
          exact ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, usedBelow, bound, p, q, r, s⟩
        have cutAt : wordSemCutEnvs (adjustSets names) initial.locals = some (cutFirst, cutSecond) := by
          simpa [initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
            cutEnvs_adjustSets_insertOdd] using cutPair
        have argsAt : initial.getVars [1,3] = some [.word x, .word y] := by
          simp [initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
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
        have callRun : WordSemStateFiniteExact.evaluate
            (.call (some ([1], adjustSets names, .skip, n, l)) (some equalLocation) [1,3] none) initial =
            (none, WordSemStateFiniteExact.setVars [1] [.word wordResult] restored) := by
          refine equalDirectCall conf initial returned restored (adjustSets names) cutFirst cutSecond n l x y wordResult
            argsAt ?_ cutAt namesNonempty neClock ?_ popRun domain
          · change sptLookup equalLocation target.code = _
            exact codeEqual
          · change WordSemStateFiniteExact.evaluate (equalCode conf) entry =
              (some (.result (.loc n l) [.word wordResult]), returned) at stubEval
            exact stubEval
        let after := {restored with clock := target.clock, termdep := target.termdep}
        have normalized : {after with permute := target.permute} =
            {target with locals := wordCut, stackMax := returnedMax} := by
          simp only [after, restored, returned, entry, WordSemStateFiniteExact.callEnv,
            WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, initial,
            t5, t3, t1, WordSemStateFiniteExact.setVar, secondRestored, firstRestored, ← cutUnion, envEq]
        have afterRel : stateRel conf l1 l2 src after none locs := by
          rw [← normalized] at returnedRel
          exact returnedRel
        let r1 := after.setVar 1 (.word wordResult)
        have varsEq : WordSemStateFiniteExact.setVars [1] [.word wordResult] restored =
            restored.setVar 1 (.word wordResult) := by
          simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
            WordSemStateFiniteExact.setVar]
        have termNe : t5.termdep ≠ 0 := by
          change target.termdep ≠ 0
          omega
        have wrapped : WordSemStateFiniteExact.evaluate
            (.mustTerminate (.call (some ([1], adjustSets names, .skip, n, l))
              (some equalLocation) [1,3] none)) t5 = (none, r1) := by
          rw [WordSemStateFiniteExact.evaluate]
          simp only [termNe]
          change (match WordSemStateFiniteExact.evaluate
            (.call (some ([1], adjustSets names, .skip, n, l)) (some equalLocation) [1,3] none) initial with
            | (res, s1) => match res with
              | some .timeOut => (some .error, t5)
              | _ => (res, {s1 with clock := t5.clock, termdep := t5.termdep})) = (none, r1)
          rw [callRun, varsEq]
          simp [r1, after, WordSemStateFiniteExact.setVar, t5, t3, t1]
        have lowX : x.getLsbD 0 = true := by
          cases hx : x.getLsbD 0 <;> simp_all
        have lowY : y.getLsbD 0 = true := by
          cases hy : y.getLsbD 0 <;> simp_all
        have bits : (x &&& y) &&& (1 : BitVec width) ≠ 0 := by
          intro eq
          have eqBit := congrArg (fun z : BitVec width => z.getLsbD 0) eq
          have nz : 0 < width := NeZero.pos width
          simp [lowX, nz] at eqBit
          rw [BitVec.getLsbD_eq_getElem nz] at lowY
          simp_all
        have unequal : x ≠ y := fun eq => fast (Or.inr eq)
        have get1 : t5.getVar 1 = some (.word x) := by
          simp [t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have get3 : t5.getVar 3 = some (.word y) := by
          simp [t5, t3, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have get5 : t5.getVar 5 = some (.word (x &&& y)) := by
          simp [t5, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have eqTest : wordSemWordCmp .test (.word (x &&& y)) (.word (1 : BitVec width)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (((x &&& y) &&& (1 : BitVec width)) == 0) = false
          exact beq_eq_false_iff_ne.mpr bits
        have eqWords : wordSemWordCmp .equal (.word x) (.word y) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          exact beq_eq_false_iff_ne.mpr unequal
        let r3 := r1.setVar 3 (.word 1)
        have getR1 : r3.getVar 1 = some (.word wordResult) := by
          simp [r3, r1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have getR3 : r3.getVar 3 = some (.word 1) := by
          simp [r3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have slowEval : WordSemStateFiniteExact.evaluate (assignEqual conf n l dest (some names) a1 a2).1 target =
            (none, r3.setVar (adjustVar dest) (.word (if wordResult = 1 then 18 else 2))) := by
          rw [equalPrefix conf n l dest a1 a2 (some names) target x y reads.1 reads.2]
          change WordSemStateFiniteExact.evaluate (.seq _ _) t5 = _
          rw [evalSeqLocal, evalIfLocal t5 .test 5 (.imm 1) _ _ _ _ false get5 (by rfl) eqTest]
          simp only [Bool.false_eq_true, if_false]
          rw [evalIfLocal t5 .equal 1 (.reg 3) _ _ _ _ false get1
            (by simpa [WordSemStateFiniteExact.getVarImm] using get3) eqWords]
          simp only [Bool.false_eq_true, if_false]
          rw [evalSeqLocal]
          simp only [Option.getD_some]
          rw [wrapped]
          simp only
          have assignRun : WordSemStateFiniteExact.evaluate (.assign 3 (.const 1)) r1 = (none, r3) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, r3]
          rw [assignRun]
          simp only
          change WordSemStateFiniteExact.evaluate (setBool (adjustVar dest) .equal 1 (.reg 3)) r3 = _
          simp only [setBool]
          rw [evalIfLocal r3 .equal 1 (.reg 3) _ _ _ _ (decide (wordResult = 1)) getR1
            (by simpa [WordSemStateFiniteExact.getVarImm] using getR3) (by
              simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
              exact beq_eq_decide wordResult 1)]
          split <;> simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
        have r1Rel : stateRel conf l1 l2 src r1 none locs := by
          simpa [r1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using afterRel
        have r3Rel : stateRel conf l1 l2 src r3 none locs := by
          simpa [r3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using r1Rel
        have flagResult : (if wordResult = 1 then (18 : BitVec width) else 2) =
            (if flag then 18 else 2) := by
          cases flag <;> simp_all
        have outputRel := equalInsertBool conf l1 l2 src r3 locs dest flag r3Rel
        refine ⟨none, r3.setVar (adjustVar dest) (.word (if flag then 18 else 2)), ?_, ?_, ?_⟩
        · rw [flagResult] at slowEval
          simpa [compileAssign, arg2] using slowEval
        · simp
        · intro _
          exact ⟨outputRel, rfl⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
