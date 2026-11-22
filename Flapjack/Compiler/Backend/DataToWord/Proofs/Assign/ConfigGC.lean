module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SilentFfi
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.CallArith
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLemma
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit

@[expose] public section

/-! Garbage-collector configuration in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace ConfigGCAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ConfigGCAssignmentWitness

open Classical in
/-- The source state after the space reset of `ConfigGC`; local proof
infrastructure for `assign_ConfigGC`. -/
noncomputable def configGCSpace {C F : Type} (x : DataSem.State C F) (values : List DataSem.Value) :
    DataSem.State C F :=
  { x with
    space := 0
    safeForSpace := x.safeForSpace && decide (DataSem.noThunksInRefs x.refs ∧
      DataSem.sizeOfHeapArgs values x + DataSem.spaceConsumed x (.memOp .configGC) values ≤
        x.limits.heapLimit)
    peakHeapLength := max x.peakHeapLength
      (DataSem.sizeOfHeapArgs values x + DataSem.spaceConsumed x (.memOp .configGC) values) }

/-- Invert the source collector configuration; local proof infrastructure for
`assign_ConfigGC`. -/
private theorem configGCSource {C F : Type} (values : List DataSem.Value)
    (x resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .configGC) values x = .val (result, resultState)) :
    ∃ a b, values = [.number a, .number b] ∧ result = DataSem.unitValue ∧
      resultState = DataSem.doStack (.memOp .configGC) values
        (DataSem.doLimSafe (configGCSpace x values) (.memOp .configGC) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
      DataSem.applyNonFfi] at run
  | cons v1 rest =>
    cases rest with
    | nil => cases v1 <;> simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
        DataSem.applyNonFfi] at run
    | cons v2 rest =>
      cases rest with
      | cons v3 rest => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
          DataSem.applyNonFfi] at run
      | nil =>
        cases v1 with
        | number a =>
          cases v2 with
          | number b =>
            refine ⟨a, b, rfl, ?_⟩
            simp only [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
              DataSem.applyNonFfi, if_true] at run
            simp only [Result.val.injEq, Prod.mk.injEq] at run
            exact ⟨run.1.symm, run.2.symm⟩
          | _ => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
              DataSem.applyNonFfi] at run
        | _ => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSem.doAppAux,
            DataSem.applyNonFfi] at run

/-- Sequential evaluation; local proof infrastructure. -/
private theorem evalSeqCfg {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- The allocation and trailing silent FFI of the collector configuration code,
from a related pair whose source locals are cut by the live names; local proof
infrastructure for `assign_ConfigGC`. -/
private theorem configGCTail {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (l1 l2 : Nat) (src : DataSem.State C F)
    (tgt : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (ns : NumSet)
    (env : Spt DataSem.Value) (dest : Nat)
    (related : stateRel conf l1 l2 src tgt none locs)
    (cut : DataSem.cutEnv ns src.locals = some env) :
    ∃ q r, WordSemStateFiniteExact.evaluate (wordListSeq [.assign 1 (.const 0),
        .alloc 1 (adjustSets ns), silentFfi conf 3 (adjustSets ns),
        .assign (adjustVar dest) (.const 2)]) tgt = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = src.ffi ∧ optionLe r.stackMax src.stackMax ∧
        (conf.gcKind ≠ .none ∧ DataSem.noThunksInRefs src.refs →
          src.limits.heapLimit < DataSem.sizeOfHeap (cutLocals ns src))) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest DataSem.unitValue
          {src with locals := env, space := 0}) r none locs ∧ q = none) := by
  let N := (adjustSets ns : NumSet × NumSet)
  have zeroSize : (0 : BitVec width) = gcAllocSize 0 := by simp [gcAllocSize]
  have envIdem := cutEnv_idempotent ns src.locals env cut
  let S := {src with locals := env, space := 0}
  -- The remaining code after a successful allocation.
  have finish : ∀ r1 : WordSemStateFiniteExact width C F, stateRel conf l1 l2 S r1 none locs →
      ∃ r, WordSemStateFiniteExact.evaluate (wordListSeq [silentFfi conf 3 N,
        .assign (adjustVar dest) (.const 2)]) r1 = (none, r) ∧
        stateRel conf l1 l2 (DataSem.setVar dest DataSem.unitValue S) r none locs := by
    intro r1 rel1
    have after : ∀ r2 : WordSemStateFiniteExact width C F, stateRel conf l1 l2 S r2 none locs →
        WordSemStateFiniteExact.evaluate (silentFfi conf 3 N) r1 = (none, r2) →
        ∃ r, WordSemStateFiniteExact.evaluate (wordListSeq [silentFfi conf 3 N,
          .assign (adjustVar dest) (.const 2)]) r1 = (none, r) ∧
          stateRel conf l1 l2 (DataSem.setVar dest DataSem.unitValue S) r none locs := by
      intro r2 rel2 ev2
      have good := rel2.2.2.2.2.2.2.1
      have unitRoot := memoryRel_unit conf r2.be (holThe S.tstamps) S.refs S.space r2.store r2.memory
        r2.mdomain _ ⟨rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, good⟩
      refine ⟨WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) r2, ?_,
        stateRel_insertRoot conf l1 l2 S r2 locs dest DataSem.unitValue (.word 2) rel2
          (by simpa [List.append_assoc] using unitRoot)⟩
      simp only [wordListSeq]
      rw [evalSeqCfg, ev2]
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
    cases ffiOn : conf.callEmptyFfi with
    | false =>
      exact after r1 rel1 (by simp [silentFfi, ffiOn, WordSemStateFiniteExact.evaluate])
    | true =>
      have envS : DataSem.cutEnv ns S.locals = some env := envIdem
      obtain ⟨y, yEq⟩ := cutEnv_imp_wordCutEnv conf l1 l2 S r1 locs ns env ⟨rel1, envS⟩
      have ev2 := evaluate_silentFfi_three conf l1 l2 S r1 locs ns y ⟨ffiOn, rel1, yEq⟩
      have relCut := stateRel_cutEnv_cutEnv conf l1 l2 S r1 locs ns env y ⟨rel1, envS, yEq⟩
      have relFp := stateRel_withFpRegs conf l1 l2 _ _ none locs HolFiniteMapExact.empty relCut
      exact after _ relFp ev2
  cases ha : WordSemStateFiniteExact.alloc (gcAllocSize 0) N tgt with
  | mk q1 r1 =>
    have facts := allocLemma conf l1 l2 src tgt r1 locs ns env 0 q1 ⟨related, cut, ha⟩
    have evAlloc : WordSemStateFiniteExact.evaluate (wordListSeq [.assign 1 (.const 0),
        .alloc 1 N, silentFfi conf 3 N, .assign (adjustVar dest) (.const 2)]) tgt =
        match (q1, r1) with
        | (none, s1) => WordSemStateFiniteExact.evaluate (wordListSeq [silentFfi conf 3 N,
            .assign (adjustVar dest) (.const 2)]) s1
        | (some res, s1) => (some res, s1) := by
      have allocEq : WordSemStateFiniteExact.evaluate (.alloc 1 N)
          (WordSemStateFiniteExact.setVar 1 (.word 0) tgt) = (q1, r1) := by
        rw [← ha, zeroSize, ← alloc_locals_insert_one (gcAllocSize 0) ns tgt (.word 0)]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, ← zeroSize, N]
      have step1 : WordSemStateFiniteExact.evaluate (.assign 1 (.const 0)) tgt =
          (none, WordSemStateFiniteExact.setVar 1 (.word 0) tgt) := by
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
      simp only [wordListSeq]
      rw [evalSeqCfg, step1]
      dsimp only
      rw [evalSeqCfg, allocEq]
    by_cases nes : q1 = some .notEnoughSpace
    · subst nes
      obtain ⟨ffi, stack, heap⟩ := facts.1 rfl
      refine ⟨some .notEnoughSpace, r1, evAlloc, ?_, ?_⟩
      · intro _
        exact ⟨ffi, stack, heap⟩
      · intro h
        exact absurd rfl h
    · obtain ⟨rel1, -, -, -, -, -, -, qNone⟩ := facts.2 nes
      subst qNone
      obtain ⟨r, evRest, relR⟩ := finish r1 rel1
      refine ⟨none, r, ?_, ?_, ?_⟩
      · rw [evAlloc]
        exact evRest
      · intro h
        cases h
      · intro _
        exact ⟨relR, rfl⟩

/-- Configuring the garbage collector satisfies the original assignment
simulation. The evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_ConfigGC"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignConfigGC_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .configGC)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
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
  | some ns =>
    obtain ⟨env, envEq, cutIs⟩ : ∃ env, DataSem.cutEnv ns source.locals = some env ∧
        cut = {source with locals := env} := by
      cases h : DataSem.cutEnv ns source.locals with
      | none => simp [DataSem.cutStateOpt, DataSem.cutState, h] at cutEq
      | some env =>
        simp [DataSem.cutStateOpt, DataSem.cutState, h] at cutEq
        exact ⟨env, rfl, cutEq.symm⟩
    subst cut
    obtain ⟨a, b, valuesEq, resultEq, stateEq⟩ := configGCSource values _ resultState result run
    subst values result resultState
    have argLen := DataSpace.getVars_length args source.locals [.number a, .number b] argsEq
    obtain ⟨k1, k2, rfl⟩ : ∃ k1 k2, args = [k1, k2] := by
      match args, argLen with
      | [k1, k2], _ => exact ⟨k1, k2, rfl⟩
      | [], h | [_], h | _ :: _ :: _ :: _, h => simp at h
    let N := (adjustSets ns : NumSet × NumSet)
    have codeEq : (compileAssign (width := width) conf n l dest (.memOp .configGC) [k1, k2] (some ns)).1 =
        .seq (silentFfi conf 3 N) (wordListSeq [.assign 1 (.const 0), .alloc 1 N, silentFfi conf 3 N,
          .assign (adjustVar dest) (.const 2)]) := rfl
    have targetFfi : target.ffi = source.ffi := related.1
    have main : ∀ (src : DataSem.State C F) (tgt : WordSemStateFiniteExact width C F),
        stateRel conf l1 l2 src tgt none locs → DataSem.cutEnv ns src.locals = some env →
        src.ffi = source.ffi → src.stackMax = source.stackMax → src.refs = source.refs →
        src.limits = source.limits → cutLocals ns src = {source with locals := env} →
        ({src with locals := env, space := 0} : DataSem.State C F) =
          {source with locals := env, space := 0} →
        WordSemStateFiniteExact.evaluate (silentFfi conf 3 N) target = (none, tgt) →
        ∃ q r,
          WordSemStateFiniteExact.evaluate (compileAssign conf n l dest (.memOp .configGC) [k1, k2]
            (some ns)).1 target = (q, r) ∧
          (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax
            (DataSem.doStack (.memOp .configGC) [.number a, .number b] (DataSem.doLimSafe
              (configGCSpace {source with locals := env} [.number a, .number b])
              (.memOp .configGC) [.number a, .number b])).stackMax ∧
            (conf.gcKind ≠ .none →
              (DataSem.doStack (.memOp .configGC) [.number a, .number b] (DataSem.doLimSafe
              (configGCSpace {source with locals := env} [.number a, .number b])
              (.memOp .configGC) [.number a, .number b])).safeForSpace = false)) ∧
          (q ≠ some .notEnoughSpace →
            stateRel conf l1 l2 (DataSem.setVar dest DataSem.unitValue
              (DataSem.doStack (.memOp .configGC) [.number a, .number b] (DataSem.doLimSafe
              (configGCSpace {source with locals := env} [.number a, .number b])
              (.memOp .configGC) [.number a, .number b]))) r none locs ∧ q = none) := by
      intro src tgt rel cutSrc ffiEq maxEq refsEq limitsEq cutLoc stEq silentEv
      obtain ⟨q, r, ev, nesFacts, okFacts⟩ := configGCTail conf l1 l2 src tgt locs ns env dest rel cutSrc
      refine ⟨q, r, ?_, ?_, ?_⟩
      · rw [codeEq, evalSeqCfg, silentEv]
        exact ev
      · intro qn
        obtain ⟨rFfi, rMax, rHeap⟩ := nesFacts qn
        refine ⟨rFfi.trans (ffiEq.trans targetFfi.symm), ?_, ?_⟩
        · simp only [DataSem.doStack, DataSem.doLimSafe]
          exact (optionLe_max_right _ _ _).mpr (Or.inl (maxEq ▸ rMax))
        · intro gcNe
          by_cases nt : DataSem.noThunksInRefs source.refs
          · have big := rHeap ⟨gcNe, refsEq ▸ nt⟩
            rw [cutLoc, limitsEq] at big
            have le := Bignum.sizeOfHeap_le_args [.number a, .number b] ({source with locals := env} : DataSem.State C F)
            have notLe : ¬ (DataSem.sizeOfHeapArgs [.number a, .number b] {source with locals := env} +
                DataSem.spaceConsumed {source with locals := env} (.memOp .configGC)
                  [.number a, .number b] ≤ source.limits.heapLimit) := by
              simp only [DataSem.spaceConsumed]
              omega
            simp [DataSem.doStack, DataSem.doLimSafe, configGCSpace, notLe]
          · simp [DataSem.doStack, DataSem.doLimSafe, configGCSpace, nt]
      · intro qn
        obtain ⟨relR, qNone⟩ := okFacts qn
        rw [stEq] at relR
        refine ⟨?_, qNone⟩
        have h2 := stateRel_doStack conf l1 l2 _ r locs (.memOp .configGC) [.number a, .number b] relR
        exact h2
    cases ffiOn : conf.callEmptyFfi with
    | false =>
      exact main source target related envEq rfl rfl rfl rfl
        (by simp [cutLocals, envEq]) rfl
        (by simp [silentFfi, ffiOn, WordSemStateFiniteExact.evaluate])
    | true =>
      obtain ⟨y, yEq⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs ns env ⟨related, envEq⟩
      have ev1 := evaluate_silentFfi_three conf l1 l2 source target locs ns y ⟨ffiOn, related, yEq⟩
      have relCut := stateRel_cutEnv_cutEnv conf l1 l2 source target locs ns env y ⟨related, envEq, yEq⟩
      have relFp := stateRel_withFpRegs conf l1 l2 _ _ none locs HolFiniteMapExact.empty relCut
      have envIdem := cutEnv_idempotent ns source.locals env envEq
      exact main {source with locals := env} _ relFp envIdem rfl rfl rfl rfl
        (by simp [cutLocals, envIdem]) rfl ev1
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
