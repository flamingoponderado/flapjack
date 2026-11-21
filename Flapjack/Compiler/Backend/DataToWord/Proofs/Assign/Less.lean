module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.ComparisonSetup
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CompareCode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CompareResult
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Equal
@[expose] public section

/-! Full integer less-than assignment simulation for the data-to-word pass. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataSem
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace LessAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LessAssignmentWitness

/- Private facts factor the HOL assignment proof and have no separate HOL declarations. -/

private theorem lessSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.intOp .less) values source = .val (result, resultState)) :
    ∃ a b next, values = [.number a, .number b] ∧
      DataSem.doSpace (.intOp .less) values source = some next ∧
      result = DataSem.boolValue (decide (a < b)) ∧
      resultState = DataSem.doStack (.intOp .less) values
        (DataSem.doLimSafe next (.intOp .less) values) := by
  cases sp : DataSem.doSpace (.intOp .less) values source with
  | none => simp [DataSem.doApp, sp] at run
  | some next =>
    cases intResult : DataSem.doIntApp .less values with
    | none => simp [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] at run
    | some v =>
      have r : result = v ∧ resultState = DataSem.doStack (.intOp .less) values
          (DataSem.doLimSafe next (.intOp .less) values) := by
        simpa [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] using run.symm
      cases values with
      | nil => simp [DataSem.doIntApp] at intResult
      | cons x xs =>
        cases xs with
        | nil => simp [DataSem.doIntApp] at intResult
        | cons y ys =>
          cases ys with
          | cons z zs => simp [DataSem.doIntApp] at intResult
          | nil =>
            cases x <;> cases y <;> simp [DataSem.doIntApp] at intResult
            rename_i a b
            subst v
            exact ⟨a, b, next, rfl, rfl, r.1, r.2⟩
private theorem evalAssignSeq {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : WordSemStateFiniteExact.wordExp s expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (WordSemStateFiniteExact.setVar key v s) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Evaluate the comparison compiler’s three scratch-register assignments. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem lessPrefix {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y)) :
    let t1 := target.setVar 1 (.word x)
    let t3 := t1.setVar 3 (.word y)
    let t5 := t3.setVar 5 (.word (x ||| y))
    WordSemStateFiniteExact.evaluate (assignLess conf n l dest names a1 a2).1 target =
      WordSemStateFiniteExact.evaluate
        (.seq (.ite .test 5 (.imm 1) .skip
          (.seq (.mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, n, l))
              (some compareLocation) [1,3] none)) (.assign 3 (.const 1))))
          (setBool (adjustVar dest) .less 1 (.reg 3))) t5 := by
  dsimp only
  simp only [assignLess, wordListSeq]
  rw [evalAssignSeq target 1 (.var (adjustVar a1)) (.word x) _ (by simpa [WordSemStateFiniteExact.wordExp] using hx)]
  have hne : adjustVar a2 ≠ 1 := by simp [adjustVar]
  rw [evalAssignSeq _ 3 (.var (adjustVar a2)) (.word y) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hne] at hy ⊢
    exact hy)]
  rw [evalAssignSeq _ 5 (.op .or [.var 1, .var 3]) (.word (x ||| y)) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne, wordOpHOL, wordOp, theWords, OrOp.or, BitVec.or_zero])]
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


private theorem lessFastEval {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y))
    (fast : (x ||| y) &&& 1 = 0) :
    WordSemStateFiniteExact.evaluate (assignLess conf n l dest names a1 a2).1 target =
      (none, (((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x ||| y))).setVar
        (adjustVar dest) (.word (if Compiler.Encoders.Asm.wordCmpHOL .less x y then 18 else 2))) := by
  rw [lessPrefix conf n l dest a1 a2 names target x y hx hy]
  let t := ((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x ||| y))
  have t5 : t.getVar 5 = some (.word (x ||| y)) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have t1 : t.getVar 1 = some (.word x) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  have t3 : t.getVar 3 = some (.word y) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  change WordSemStateFiniteExact.evaluate (.seq _ _) t = _
  rw [evalSeqLocal]
  have test : wordSemWordCmp .test (.word (x ||| y)) (.word (1 : BitVec width)) = some true := by
    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
    change (((x ||| y) &&& (1 : BitVec width)) == 0) = true
    exact beq_iff_eq.mpr fast
  rw [evalIfLocal t .test 5 (.imm 1) _ _ _ _ true t5 (by rfl) test]
  simp only [ite_true, WordSemStateFiniteExact.evaluate]
  simp only [setBool]
  rw [evalIfLocal t .less 1 (.reg 3) _ _ _ _ (Compiler.Encoders.Asm.wordCmpHOL .less x y)
    t1 (by simpa [WordSemStateFiniteExact.getVarImm] using t3) (by rfl)]
  cases h : Compiler.Encoders.Asm.wordCmpHOL .less x y <;>
    simp [t, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]

private theorem lessInsertBool {width : Nat} [NeZero width] {C F : Type}
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


private theorem lessRestoredCuts {width : Nat} [NeZero width] (names : WordLangCutsetsHOL)
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

/-- Evaluate the returning comparison stub call from its established premises. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem lessDirectCall {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (n l : Nat) (x y res : BitVec width)
    (args : s.getVars [1,3] = some [.word x, .word y])
    (code : sptLookup compareLocation s.code = some (3, compareCode conf))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate (compareCode conf)
      (WordSemStateFiniteExact.callEnv [.loc n l, .word x, .word y] (sptLookup compareLocation s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [.word res]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([1], names, .skip, n, l)) (some compareLocation) [1,3] none) s =
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

private theorem compareStackAlgebra (targetMax sourceMax used frame inner : Option Nat)
    (oldMax : optionLe targetMax sourceMax) (usedMax : optionLe used targetMax) :
    optionLe
      (Option.map₂ max (Option.map₂ max (Option.map₂ max targetMax used)
        (Option.map₂ (· + ·) used frame)) (Option.map₂ (· + ·) used inner))
      (Option.map₂ max sourceMax (Option.map₂ (· + ·) (Option.map₂ max frame inner) used)) := by
  cases targetMax <;> cases sourceMax <;> cases used <;> cases frame <;> cases inner <;>
    simp_all [optionLe]; omega

private theorem lowOrZero {width : Nat} (x y : BitVec width)
    (h : x.getLsbD 0 = false ∧ y.getLsbD 0 = false) :
    (x ||| y) &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat]
  match i with
  | 0 => simp [h.1, h.2]
  | j + 1 => simp [Nat.testBit_succ]

private theorem signedLessEq {width : Nat} (left right : BitVec width) (good : goodDimindex width) :
    Compiler.Encoders.Asm.holAsmSignedLess left right = left.slt right := by
  rcases good with h | h <;> subst width
  all_goals have bl := left.isLt
  all_goals have br := right.isLt
  all_goals simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide,
    BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

/-- Integer less-than satisfies the complete HOL assignment simulation.
The word evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Less"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLess_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .intOp .less)
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
    obtain ⟨a, b, next, valuesEq, spaceEq, resultEq, stateEq⟩ := lessSource values cut resultState result run
    subst values
    subst result
    subst resultState
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
      target.store target.memory target.mdomain target envs [a1, a2] [.number a, .number b] [w1, w2] (by
        refine ⟨?_, argsEq, getWord⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have good := related.2.2.2.2.2.2.1
    obtain ⟨x, y, rfl, rfl, cmp⟩ := memoryRel_numberCmp conf target.be (holThe source.tstamps)
      source.refs source.space target.store target.memory target.mdomain a b w1 w2
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
      ⟨by simpa using roots, good⟩
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
        (DataSem.doStack (.intOp .less) [.number a, .number b]
          (DataSem.doLimSafe next (.intOp .less) [.number a, .number b])) target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 next target locs _ _ nextRel)
    by_cases fast : x.getLsbD 0 = false ∧ y.getLsbD 0 = false
    · have cmpSmall : (a < b ↔ x.slt y = true) ∧ (a = b ↔ x = y) := by
        simpa [fast] using cmp
      have ordering := cmpSmall.1
      have flagResult : Compiler.Encoders.Asm.wordCmpHOL .less x y = decide (a < b) := by
        simp only [Compiler.Encoders.Asm.wordCmpHOL, signedLessEq x y good]
        cases h : x.slt y <;> simp_all
      let src := DataSem.doStack (.intOp .less) [.number a, .number b]
        (DataSem.doLimSafe next (.intOp .less) [.number a, .number b])
      change stateRel conf l1 l2 src target none locs at finalSourceRel
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x ||| y))
      have rel1 : stateRel conf l1 l2 src t1 none locs := by
        simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using finalSourceRel
      have rel3 : stateRel conf l1 l2 src t3 none locs := by
        simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel1
      have rel5 : stateRel conf l1 l2 src t5 none locs := by
        simpa [t5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel3
      have outputRel := lessInsertBool conf l1 l2 src t5 locs dest (decide (a < b)) rel5
      refine ⟨none, t5.setVar (adjustVar dest) (.word (if decide (a < b) then 18 else 2)), ?_, ?_, ?_⟩
      · have eval := lessFastEval conf n l dest a1 a2 (some names) target x y reads.1 reads.2
          (lowOrZero x y fast)
        rw [flagResult] at eval
        simpa [compileAssign, arg2, t5, t3, t1] using eval
      · simp
      · intro _
        exact ⟨outputRel, rfl⟩
    · obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
        cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x ||| y))
      let initial := {t5 with clock := wordSemMustTerminateLimit width, termdep := t5.termdep - 1}
      let entry := WordSemStateFiniteExact.callEnv [.loc n l, .word x, .word y]
        (sptLookup compareLocation target.stackSize)
        (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
      have configBounds : conf.lenSize ≠ 0 ∧ conf.lenSize < width := by
        obtain ⟨heap, limit, addr, sp, sp1, gens, heapMem, _⟩ := roots
        have nonzero : conf.lenSize ≠ 0 := heapMem.2.2.2.1
        have bound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
        exact ⟨nonzero, by omega⟩
      have codeMembership :
          (compareLocation, 3, compareCode conf) ∈ stubs (width := width) conf ∧
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
      have codeCompare : sptLookup compareLocation target.code = some (3, compareCode conf) :=
        related.2.2.2.2.1.2.1 _ codeMembership.1
      have codeCompare1 : sptLookup compare1Location target.code = some (4, compare1Code) :=
        related.2.2.2.2.1.2.1 _ codeMembership.2
      have bitImp : x.getLsbD 0 = false → y.getLsbD 0 = true := by
        intro hx
        cases hy : y.getLsbD 0 <;> simp_all
      have clockBound : 2 ^ width < wordSemMustTerminateLimit width - 1 := by
        exact dimwordLessMustTerminateLimit width good
      have callEval := compareCode_correct conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain a b x y
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
        entry n l (by
          refine ⟨by simpa using roots, ?_, ?_, ?_, bitImp, related.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, configBounds.1, configBounds.2, good⟩
          all_goals simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
            WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
            sptLookup_sptInsert_same, codeCompare1, clockBound])
      obtain ⟨returnedClock, returnedMax, stubEval, stubMax⟩ := callEval
      cases envEq : wordSemEnvToList cutSecond target.permute with
      | mk entries permute =>
        obtain ⟨firstRestored, secondRestored⟩ :=
          lessRestoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permute entries cutPair envEq
        let returned := {entry with clock := returnedClock, locals := .ln, localsSize := some 0, permute := entry.permute, stackMax := returnedMax}
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
        let budget := Option.map₂ max (sptLookup compareLocation target.stackSize) (sptLookup compare1Location target.stackSize)
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
              (Option.map₂ (· + ·) used (sptLookup compareLocation target.stackSize)) := by
          simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar, envEq,
            wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
          change wordSemOptionMax
            (wordSemOptionMax target.stackMax (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack)))
            (wordSemOptionAdd (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack))
              (sptLookup compareLocation target.stackSize)) = _
          rw [swapUsed]
          simp only [optMax, optAdd]
        have sourceMaxEq : (DataSem.doStack (.intOp .less) [.number a, .number b]
            (DataSem.doLimSafe next (.intOp .less) [.number a, .number b])).stackMax =
            Option.map₂ max cut.stackMax (Option.map₂ (· + ·) budget used) := by
          simp only [DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed]
          have nextFields : next.stackFrameSizes = cut.stackFrameSizes ∧ next.stack = cut.stack ∧
              next.localsSize = cut.localsSize ∧ next.stackMax = cut.stackMax := by
            simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
            subst next
            exact ⟨rfl, rfl, rfl, rfl⟩
          rw [nextFields.1, nextFields.2.1, nextFields.2.2.1, nextFields.2.2.2,
            ← frameSizeEq, ← localSizeEq, ← stackSizeEq]
        have bound : optionLe returnedMax (DataSem.doStack (.intOp .less) [.number a,.number b]
            (DataSem.doLimSafe next (.intOp .less) [.number a,.number b])).stackMax := by
          apply optionLe_trans _ _ _ ⟨stubMax, ?_⟩
          rw [entryStack, entrySize, entryMaxEq, sourceMaxEq]
          exact compareStackAlgebra target.stackMax cut.stackMax used _ _ oldMax oldUsage
        have entryBelow : optionLe entry.stackMax returnedMax := by
          have growth := WordSemStateFiniteExact.evaluate_stack_max_le (compareCode conf) entry
            (some (.result (.loc n l) [.word (wordCmpRes a b)])) returned stubEval
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
        let src := DataSem.doStack (.intOp .less) [.number a, .number b] (DataSem.doLimSafe next (.intOp .less) [.number a, .number b])
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
            (.call (some ([1], adjustSets names, .skip, n, l)) (some compareLocation) [1,3] none) initial =
            (none, WordSemStateFiniteExact.setVars [1] [.word (wordCmpRes a b)] restored) := by
          refine lessDirectCall conf initial returned restored (adjustSets names) cutFirst cutSecond n l x y (wordCmpRes a b)
            argsAt ?_ cutAt namesNonempty neClock ?_ popRun domain
          · change sptLookup compareLocation target.code = _
            exact codeCompare
          · change WordSemStateFiniteExact.evaluate (compareCode conf) entry =
              (some (.result (.loc n l) [.word (wordCmpRes a b)]), returned) at stubEval
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
        let r1 := after.setVar 1 (.word (wordCmpRes a b))
        have varsEq : WordSemStateFiniteExact.setVars [1] [.word (wordCmpRes a b)] restored =
            restored.setVar 1 (.word (wordCmpRes a b)) := by
          simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
            WordSemStateFiniteExact.setVar]
        have termNe : t5.termdep ≠ 0 := by
          change target.termdep ≠ 0
          omega
        have wrapped : WordSemStateFiniteExact.evaluate
            (.mustTerminate (.call (some ([1], adjustSets names, .skip, n, l))
              (some compareLocation) [1,3] none)) t5 = (none, r1) := by
          rw [WordSemStateFiniteExact.evaluate]
          simp only [termNe]
          change (match WordSemStateFiniteExact.evaluate
            (.call (some ([1], adjustSets names, .skip, n, l)) (some compareLocation) [1,3] none) initial with
            | (res, s1) => match res with
              | some .timeOut => (some .error, t5)
              | _ => (res, {s1 with clock := t5.clock, termdep := t5.termdep})) = (none, r1)
          rw [callRun, varsEq]
          simp [r1, after, WordSemStateFiniteExact.setVar, t5, t3, t1]
        have bits : (x ||| y) &&& (1 : BitVec width) ≠ 0 := by
          intro eq
          have eqBit := congrArg (fun z : BitVec width => z.getLsbD 0) eq
          have nz : 0 < width := NeZero.pos width
          simp [nz] at eqBit
          apply fast
          simpa [BitVec.getLsbD_eq_getElem nz] using eqBit
        have get5 : t5.getVar 5 = some (.word (x ||| y)) := by
          simp [t5, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have eqTest : wordSemWordCmp .test (.word (x ||| y)) (.word (1 : BitVec width)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (((x ||| y) &&& (1 : BitVec width)) == 0) = false
          exact beq_eq_false_iff_ne.mpr bits
        let r3 := r1.setVar 3 (.word 1)
        have getR1 : r3.getVar 1 = some (.word (wordCmpRes a b)) := by
          simp [r3, r1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have getR3 : r3.getVar 3 = some (.word 1) := by
          simp [r3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have slowEval : WordSemStateFiniteExact.evaluate (assignLess conf n l dest (some names) a1 a2).1 target =
            (none, r3.setVar (adjustVar dest) (.word (if Compiler.Encoders.Asm.wordCmpHOL .less (wordCmpRes a b : BitVec width) 1 then 18 else 2))) := by
          rw [lessPrefix conf n l dest a1 a2 (some names) target x y reads.1 reads.2]
          change WordSemStateFiniteExact.evaluate (.seq _ _) t5 = _
          rw [evalSeqLocal, evalIfLocal t5 .test 5 (.imm 1) _ _ _ _ false get5 (by rfl) eqTest]
          simp only [Bool.false_eq_true, if_false]
          rw [evalSeqLocal]
          simp only [Option.getD_some]
          rw [wrapped]
          simp only
          have assignRun : WordSemStateFiniteExact.evaluate (.assign 3 (.const 1)) r1 = (none, r3) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, r3]
          rw [assignRun]
          simp only
          change WordSemStateFiniteExact.evaluate (setBool (adjustVar dest) .less 1 (.reg 3)) r3 = _
          simp only [setBool]
          rw [evalIfLocal r3 .less 1 (.reg 3) _ _ _ _ (Compiler.Encoders.Asm.wordCmpHOL .less (wordCmpRes a b : BitVec width) 1) getR1
            (by simpa [WordSemStateFiniteExact.getVarImm] using getR3) (by rfl)]
          cases h : Compiler.Encoders.Asm.wordCmpHOL .less (wordCmpRes a b : BitVec width) 1 <;>
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
        have r1Rel : stateRel conf l1 l2 src r1 none locs := by
          simpa [r1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using afterRel
        have r3Rel : stateRel conf l1 l2 src r3 none locs := by
          simpa [r3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using r1Rel
        have flagResult : Compiler.Encoders.Asm.wordCmpHOL .less (wordCmpRes a b : BitVec width) 1 = decide (a < b) := by
          have h := wordCmpLessResult (width := width) a b good
          cases hc : Compiler.Encoders.Asm.wordCmpHOL .less (wordCmpRes a b : BitVec width) 1 <;> simp_all
        have outputRel := lessInsertBool conf l1 l2 src r3 locs dest (decide (a < b)) r3Rel
        refine ⟨none, r3.setVar (adjustVar dest) (.word (if decide (a < b) then 18 else 2)), ?_, ?_, ?_⟩
        · rw [flagResult] at slowEval
          simpa [compileAssign, arg2] using slowEval
        · simp
        · intro _
          exact ⟨outputRel, rfl⟩

private theorem lessEqSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.intOp .lessEq) values source = .val (result, resultState)) :
    ∃ a b next, values = [.number a, .number b] ∧
      DataSem.doSpace (.intOp .lessEq) values source = some next ∧
      result = DataSem.boolValue (decide (a ≤ b)) ∧
      resultState = DataSem.doStack (.intOp .lessEq) values
        (DataSem.doLimSafe next (.intOp .lessEq) values) := by
  cases sp : DataSem.doSpace (.intOp .lessEq) values source with
  | none => simp [DataSem.doApp, sp] at run
  | some next =>
    cases intResult : DataSem.doIntApp .lessEq values with
    | none => simp [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] at run
    | some v =>
      have r : result = v ∧ resultState = DataSem.doStack (.intOp .lessEq) values
          (DataSem.doLimSafe next (.intOp .lessEq) values) := by
        simpa [DataSem.doApp, sp, DataSem.doAppAux, DataSem.applyNonFfi, intResult] using run.symm
      cases values with
      | nil => simp [DataSem.doIntApp] at intResult
      | cons x xs =>
        cases xs with
        | nil => simp [DataSem.doIntApp] at intResult
        | cons y ys =>
          cases ys with
          | cons z zs => simp [DataSem.doIntApp] at intResult
          | nil =>
            cases x <;> cases y <;> simp [DataSem.doIntApp] at intResult
            rename_i a b
            subst v
            exact ⟨a, b, next, rfl, rfl, r.1, r.2⟩

/-- Evaluate the comparison compiler’s three scratch-register assignments. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem lessEqPrefix {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y)) :
    let t1 := target.setVar 1 (.word x)
    let t3 := t1.setVar 3 (.word y)
    let t5 := t3.setVar 5 (.word (x ||| y))
    WordSemStateFiniteExact.evaluate (assignLessEq conf n l dest names a1 a2).1 target =
      WordSemStateFiniteExact.evaluate
        (.seq (.ite .test 5 (.imm 1) .skip
          (.seq (.mustTerminate (.call (some ([1], adjustSets (names.getD .ln), .skip, n, l))
              (some compareLocation) [1,3] none)) (.assign 3 (.const 1))))
          (setBool (adjustVar dest) .notLess 3 (.reg 1))) t5 := by
  dsimp only
  simp only [assignLessEq, wordListSeq]
  rw [evalAssignSeq target 1 (.var (adjustVar a1)) (.word x) _ (by simpa [WordSemStateFiniteExact.wordExp] using hx)]
  have hne : adjustVar a2 ≠ 1 := by simp [adjustVar]
  rw [evalAssignSeq _ 3 (.var (adjustVar a2)) (.word y) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ hne] at hy ⊢
    exact hy)]
  rw [evalAssignSeq _ 5 (.op .or [.var 1, .var 3]) (.word (x ||| y)) _ (by
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, sptLookup_sptInsert_ne, wordOpHOL, wordOp, theWords, OrOp.or, BitVec.or_zero])]
  rfl


private theorem lessEqFastEval {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l dest a1 a2 : Nat) (names : Option NumSet)
    (target : WordSemStateFiniteExact width C F) (x y : BitVec width)
    (hx : target.getVar (adjustVar a1) = some (.word x))
    (hy : target.getVar (adjustVar a2) = some (.word y))
    (fast : (x ||| y) &&& 1 = 0) :
    WordSemStateFiniteExact.evaluate (assignLessEq conf n l dest names a1 a2).1 target =
      (none, (((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x ||| y))).setVar
        (adjustVar dest) (.word (if Compiler.Encoders.Asm.wordCmpHOL .notLess y x then 18 else 2))) := by
  rw [lessEqPrefix conf n l dest a1 a2 names target x y hx hy]
  let t := ((target.setVar 1 (.word x)).setVar 3 (.word y)).setVar 5 (.word (x ||| y))
  have t5 : t.getVar 5 = some (.word (x ||| y)) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have t1 : t.getVar 1 = some (.word x) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  have t3 : t.getVar 3 = some (.word y) := by
    simp [t, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  change WordSemStateFiniteExact.evaluate (.seq _ _) t = _
  rw [evalSeqLocal]
  have test : wordSemWordCmp .test (.word (x ||| y)) (.word (1 : BitVec width)) = some true := by
    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
    change (((x ||| y) &&& (1 : BitVec width)) == 0) = true
    exact beq_iff_eq.mpr fast
  rw [evalIfLocal t .test 5 (.imm 1) _ _ _ _ true t5 (by rfl) test]
  simp only [ite_true, WordSemStateFiniteExact.evaluate]
  simp only [setBool]
  rw [evalIfLocal t .notLess 3 (.reg 1) _ _ _ _ (Compiler.Encoders.Asm.wordCmpHOL .notLess y x)
    t3 (by simpa [WordSemStateFiniteExact.getVarImm] using t1) (by rfl)]
  cases h : Compiler.Encoders.Asm.wordCmpHOL .notLess y x <;>
    simp [t, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]


/-- Integer less-than-or-equal satisfies the complete HOL assignment simulation.
The word evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_LessEq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLessEq_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .intOp .lessEq)
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
    obtain ⟨a, b, next, valuesEq, spaceEq, resultEq, stateEq⟩ := lessEqSource values cut resultState result run
    subst values
    subst result
    subst resultState
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
      target.store target.memory target.mdomain target envs [a1, a2] [.number a, .number b] [w1, w2] (by
        refine ⟨?_, argsEq, getWord⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have good := related.2.2.2.2.2.2.1
    obtain ⟨x, y, rfl, rfl, cmp⟩ := memoryRel_numberCmp conf target.be (holThe source.tstamps)
      source.refs source.space target.store target.memory target.mdomain a b w1 w2
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
      ⟨by simpa using roots, good⟩
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
        (DataSem.doStack (.intOp .lessEq) [.number a, .number b]
          (DataSem.doLimSafe next (.intOp .lessEq) [.number a, .number b])) target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 next target locs _ _ nextRel)
    by_cases fast : x.getLsbD 0 = false ∧ y.getLsbD 0 = false
    · have cmpSmall : (a < b ↔ x.slt y = true) ∧ (a = b ↔ x = y) := by
        simpa [fast] using cmp
      have ordering := cmpSmall.1
      have flagResult : Compiler.Encoders.Asm.wordCmpHOL .notLess y x = decide (a ≤ b) := by
        simp only [Compiler.Encoders.Asm.wordCmpHOL, signedLessEq y x good,
          BitVec.slt_eq_decide] at *
        have eqIff : x.toInt = y.toInt ↔ x = y := BitVec.toInt_inj
        apply Bool.eq_iff_iff.mpr
        have eqord : (a = b ↔ x.toInt = y.toInt) := cmpSmall.2.trans eqIff.symm
        cases hy : decide (y.toInt < x.toInt) <;> simp_all <;>
          rcases lt_trichotomy a b with ha | ha | ha <;>
          rcases lt_trichotomy x.toInt y.toInt with hw | hw | hw <;>
          (try simp_all) <;> omega
      let src := DataSem.doStack (.intOp .lessEq) [.number a, .number b]
        (DataSem.doLimSafe next (.intOp .lessEq) [.number a, .number b])
      change stateRel conf l1 l2 src target none locs at finalSourceRel
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x ||| y))
      have rel1 : stateRel conf l1 l2 src t1 none locs := by
        simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using finalSourceRel
      have rel3 : stateRel conf l1 l2 src t3 none locs := by
        simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel1
      have rel5 : stateRel conf l1 l2 src t5 none locs := by
        simpa [t5, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using rel3
      have outputRel := lessInsertBool conf l1 l2 src t5 locs dest (decide (a ≤ b)) rel5
      refine ⟨none, t5.setVar (adjustVar dest) (.word (if decide (a ≤ b) then 18 else 2)), ?_, ?_, ?_⟩
      · have eval := lessEqFastEval conf n l dest a1 a2 (some names) target x y reads.1 reads.2
          (lowOrZero x y fast)
        rw [flagResult] at eval
        simpa [compileAssign, arg2, t5, t3, t1] using eval
      · simp
      · intro _
        exact ⟨outputRel, rfl⟩
    · obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
        cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
      let t1 := target.setVar 1 (.word x)
      let t3 := t1.setVar 3 (.word y)
      let t5 := t3.setVar 5 (.word (x ||| y))
      let initial := {t5 with clock := wordSemMustTerminateLimit width, termdep := t5.termdep - 1}
      let entry := WordSemStateFiniteExact.callEnv [.loc n l, .word x, .word y]
        (sptLookup compareLocation target.stackSize)
        (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
      have configBounds : conf.lenSize ≠ 0 ∧ conf.lenSize < width := by
        obtain ⟨heap, limit, addr, sp, sp1, gens, heapMem, _⟩ := roots
        have nonzero : conf.lenSize ≠ 0 := heapMem.2.2.2.1
        have bound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
        exact ⟨nonzero, by omega⟩
      have codeMembership :
          (compareLocation, 3, compareCode conf) ∈ stubs (width := width) conf ∧
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
      have codeCompare : sptLookup compareLocation target.code = some (3, compareCode conf) :=
        related.2.2.2.2.1.2.1 _ codeMembership.1
      have codeCompare1 : sptLookup compare1Location target.code = some (4, compare1Code) :=
        related.2.2.2.2.1.2.1 _ codeMembership.2
      have bitImp : x.getLsbD 0 = false → y.getLsbD 0 = true := by
        intro hx
        cases hy : y.getLsbD 0 <;> simp_all
      have clockBound : 2 ^ width < wordSemMustTerminateLimit width - 1 := by
        exact dimwordLessMustTerminateLimit width good
      have callEval := compareCode_correct conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain a b x y
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs)
        entry n l (by
          refine ⟨by simpa using roots, ?_, ?_, ?_, bitImp, related.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, configBounds.1, configBounds.2, good⟩
          all_goals simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar,
            WordSemStateFiniteExact.getVar, sptFromList2, sptLookup, sptLookup_sptInsert_ne,
            sptLookup_sptInsert_same, codeCompare1, clockBound])
      obtain ⟨returnedClock, returnedMax, stubEval, stubMax⟩ := callEval
      cases envEq : wordSemEnvToList cutSecond target.permute with
      | mk entries permute =>
        obtain ⟨firstRestored, secondRestored⟩ :=
          lessRestoredCuts (adjustSets names) target.locals cutFirst cutSecond target.permute permute entries cutPair envEq
        let returned := {entry with clock := returnedClock, locals := .ln, localsSize := some 0, permute := entry.permute, stackMax := returnedMax}
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
        let budget := Option.map₂ max (sptLookup compareLocation target.stackSize) (sptLookup compare1Location target.stackSize)
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
              (Option.map₂ (· + ·) used (sptLookup compareLocation target.stackSize)) := by
          simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
            WordSemStateFiniteExact.decClock, initial, t5, t3, t1, WordSemStateFiniteExact.setVar, envEq,
            wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame]
          change wordSemOptionMax
            (wordSemOptionMax target.stackMax (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack)))
            (wordSemOptionAdd (wordSemOptionAdd target.localsSize (wordSemStackSize target.stack))
              (sptLookup compareLocation target.stackSize)) = _
          rw [swapUsed]
          simp only [optMax, optAdd]
        have sourceMaxEq : (DataSem.doStack (.intOp .lessEq) [.number a, .number b]
            (DataSem.doLimSafe next (.intOp .lessEq) [.number a, .number b])).stackMax =
            Option.map₂ max cut.stackMax (Option.map₂ (· + ·) budget used) := by
          simp only [DataSem.doStack, DataSem.doLimSafe, DataSem.stackConsumed]
          have nextFields : next.stackFrameSizes = cut.stackFrameSizes ∧ next.stack = cut.stack ∧
              next.localsSize = cut.localsSize ∧ next.stackMax = cut.stackMax := by
            simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceEq
            subst next
            exact ⟨rfl, rfl, rfl, rfl⟩
          rw [nextFields.1, nextFields.2.1, nextFields.2.2.1, nextFields.2.2.2,
            ← frameSizeEq, ← localSizeEq, ← stackSizeEq]
        have bound : optionLe returnedMax (DataSem.doStack (.intOp .lessEq) [.number a,.number b]
            (DataSem.doLimSafe next (.intOp .lessEq) [.number a,.number b])).stackMax := by
          apply optionLe_trans _ _ _ ⟨stubMax, ?_⟩
          rw [entryStack, entrySize, entryMaxEq, sourceMaxEq]
          exact compareStackAlgebra target.stackMax cut.stackMax used _ _ oldMax oldUsage
        have entryBelow : optionLe entry.stackMax returnedMax := by
          have growth := WordSemStateFiniteExact.evaluate_stack_max_le (compareCode conf) entry
            (some (.result (.loc n l) [.word (wordCmpRes a b)])) returned stubEval
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
        let src := DataSem.doStack (.intOp .lessEq) [.number a, .number b] (DataSem.doLimSafe next (.intOp .lessEq) [.number a, .number b])
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
            (.call (some ([1], adjustSets names, .skip, n, l)) (some compareLocation) [1,3] none) initial =
            (none, WordSemStateFiniteExact.setVars [1] [.word (wordCmpRes a b)] restored) := by
          refine lessDirectCall conf initial returned restored (adjustSets names) cutFirst cutSecond n l x y (wordCmpRes a b)
            argsAt ?_ cutAt namesNonempty neClock ?_ popRun domain
          · change sptLookup compareLocation target.code = _
            exact codeCompare
          · change WordSemStateFiniteExact.evaluate (compareCode conf) entry =
              (some (.result (.loc n l) [.word (wordCmpRes a b)]), returned) at stubEval
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
        let r1 := after.setVar 1 (.word (wordCmpRes a b))
        have varsEq : WordSemStateFiniteExact.setVars [1] [.word (wordCmpRes a b)] restored =
            restored.setVar 1 (.word (wordCmpRes a b)) := by
          simp [WordSemStateFiniteExact.setVars, LoopSemStateFiniteExact.sptAlistInsert,
            WordSemStateFiniteExact.setVar]
        have termNe : t5.termdep ≠ 0 := by
          change target.termdep ≠ 0
          omega
        have wrapped : WordSemStateFiniteExact.evaluate
            (.mustTerminate (.call (some ([1], adjustSets names, .skip, n, l))
              (some compareLocation) [1,3] none)) t5 = (none, r1) := by
          rw [WordSemStateFiniteExact.evaluate]
          simp only [termNe]
          change (match WordSemStateFiniteExact.evaluate
            (.call (some ([1], adjustSets names, .skip, n, l)) (some compareLocation) [1,3] none) initial with
            | (res, s1) => match res with
              | some .timeOut => (some .error, t5)
              | _ => (res, {s1 with clock := t5.clock, termdep := t5.termdep})) = (none, r1)
          rw [callRun, varsEq]
          simp [r1, after, WordSemStateFiniteExact.setVar, t5, t3, t1]
        have bits : (x ||| y) &&& (1 : BitVec width) ≠ 0 := by
          intro eq
          have eqBit := congrArg (fun z : BitVec width => z.getLsbD 0) eq
          have nz : 0 < width := NeZero.pos width
          simp [nz] at eqBit
          apply fast
          simpa [BitVec.getLsbD_eq_getElem nz] using eqBit
        have get5 : t5.getVar 5 = some (.word (x ||| y)) := by
          simp [t5, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have eqTest : wordSemWordCmp .test (.word (x ||| y)) (.word (1 : BitVec width)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (((x ||| y) &&& (1 : BitVec width)) == 0) = false
          exact beq_eq_false_iff_ne.mpr bits
        let r3 := r1.setVar 3 (.word 1)
        have getR1 : r3.getVar 1 = some (.word (wordCmpRes a b)) := by
          simp [r3, r1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
        have getR3 : r3.getVar 3 = some (.word 1) := by
          simp [r3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        have slowEval : WordSemStateFiniteExact.evaluate (assignLessEq conf n l dest (some names) a1 a2).1 target =
            (none, r3.setVar (adjustVar dest) (.word (if Compiler.Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes a b : BitVec width) then 18 else 2))) := by
          rw [lessEqPrefix conf n l dest a1 a2 (some names) target x y reads.1 reads.2]
          change WordSemStateFiniteExact.evaluate (.seq _ _) t5 = _
          rw [evalSeqLocal, evalIfLocal t5 .test 5 (.imm 1) _ _ _ _ false get5 (by rfl) eqTest]
          simp only [Bool.false_eq_true, if_false]
          rw [evalSeqLocal]
          simp only [Option.getD_some]
          rw [wrapped]
          simp only
          have assignRun : WordSemStateFiniteExact.evaluate (.assign 3 (.const 1)) r1 = (none, r3) := by
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, r3]
          rw [assignRun]
          simp only
          change WordSemStateFiniteExact.evaluate (setBool (adjustVar dest) .notLess 3 (.reg 1)) r3 = _
          simp only [setBool]
          rw [evalIfLocal r3 .notLess 3 (.reg 1) _ _ _ _ (Compiler.Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes a b : BitVec width)) getR3
            (by simpa [WordSemStateFiniteExact.getVarImm] using getR1) (by rfl)]
          cases h : Compiler.Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes a b : BitVec width) <;>
            simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
        have r1Rel : stateRel conf l1 l2 src r1 none locs := by
          simpa [r1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using afterRel
        have r3Rel : stateRel conf l1 l2 src r3 none locs := by
          simpa [r3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using r1Rel
        have flagResult : Compiler.Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes a b : BitVec width) = decide (a ≤ b) := by
          have h := wordCmpNotLessResult (width := width) a b good
          cases hc : Compiler.Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes a b : BitVec width) <;> simp_all
        have outputRel := lessInsertBool conf l1 l2 src r3 locs dest (decide (a ≤ b)) r3Rel
        refine ⟨none, r3.setVar (adjustVar dest) (.word (if decide (a ≤ b) then 18 else 2)), ?_, ?_, ?_⟩
        · rw [flagResult] at slowEval
          simpa [compileAssign, arg2] using slowEval
        · simp
        · intro _
          exact ⟨outputRel, rfl⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
