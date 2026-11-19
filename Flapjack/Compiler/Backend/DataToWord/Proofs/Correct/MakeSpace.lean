module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLemma
public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLocals
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SilentFfi
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Tick
@[expose] public section

/-! The complete MakeSpace case of data-to-word compiler correctness. -/
open Flapjack Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The compiler’s byte encoding is the allocation-size expression used in the HOL proof. -/
private theorem allocSizeEncoding {width : Nat} [NeZero width] (n : Nat) :
    (let bytes := n * (width / 8)
     let value := BitVec.ofNat width bytes
     if value.toNat = bytes then value else (-1 : BitVec width)) = gcAllocSize n := by
  by_cases h : n * (width / 8) < 2 ^ width
  · simp [gcAllocSize, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, h]
  · have modNe : n * (width / 8) % 2 ^ width ≠ n * (width / 8) := by
      have small := Nat.mod_lt (n * (width / 8)) (by positivity : 0 < 2 ^ width)
      omega
    simp [gcAllocSize, BitVec.toNat_ofNat, h, modNe]

open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
namespace Flapjack.Compiler.Backend.DataToWord.Proofs

namespace MakeSpaceWitnesses
/-- Canonical finite-map roundtrip for the target state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MakeSpaceWitnesses

/-- The full MakeSpace case, including both allocation outcomes and the optional
empty FFI calls. The word evaluator inherits the real-model assumption documented
in SOUNDNESS item 8. Assembly with the other cases remains open. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_makeSpace {width : Nat} [NeZero width] {C F : Type}
    (amount : Nat) (names : NumSet)
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (run : DataSem.evaluate (.makeSpace amount names) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (_depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  cases cutRun : DataSem.cutEnv names source.locals with
  | none =>
    have bad : res = some (.err (.abort .typeError)) := by
      simpa [DataSem.evaluate, cutRun, DataSem.typeError] using congrArg Prod.fst run.symm
    exact False.elim (notTypeError bad)
  | some cutData =>
    have src : res = none ∧ source1 = DataSem.addSpace {source with locals := cutData} amount := by
      simpa [DataSem.evaluate, cutRun] using run.symm
    rcases src with ⟨rfl, rfl⟩
    have compiled : compileControl (width := width) conf n l (.makeSpace amount names) =
        (.seq (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
          (.ite .lower 1 (.imm (gcAllocSize amount))
            (wordListSeq [silentFfi conf 3 (adjustSets names), .assign 1 (.const (gcAllocSize amount)),
              .alloc 1 (adjustSets names), silentFfi conf 3 (adjustSets names)]) .skip), l) := by
      have h := compileControl_option (width := width) conf n l (.makeSpace amount names)
      simp only [compileControl?] at h
      rw [allocSizeEncoding] at h
      exact Option.some.inj h.symm
    have hmem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    obtain ⟨next, trigger, available, nextStore, triggerStore, gap, _, _, _⟩ :=
      memoryRel_spaceMax conf target.be (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain _ hmem
    let mid := WordSemStateFiniteExact.setVar 1 (.word (trigger - next)) target
    have assigned : WordSemStateFiniteExact.evaluate
        (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree])) target = (none, mid) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getStore, triggerStore, nextStore, theWords, wordOpHOL, wordOp, mid]
    let yes : WordLangProgHOL (BitVec width) := wordListSeq [silentFfi conf 3 (adjustSets names), .assign 1 (.const (gcAllocSize amount)),
      .alloc 1 (adjustSets names), silentFfi conf 3 (adjustSets names)]
    have midRun : WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target =
        WordSemStateFiniteExact.evaluate (.ite .lower 1 (.imm (gcAllocSize amount)) yes .skip) mid := by
      rw [compiled]
      simp only [WordSemStateFiniteExact.evaluate, assigned]
      simp [WordSemStateFiniteExact.fixClock, mid, WordSemStateFiniteExact.setVar, yes]
    by_cases needs : trigger - next < (gcAllocSize amount : BitVec width)
    · have chosen : WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target =
          WordSemStateFiniteExact.evaluate yes mid := by
        rw [midRun]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
          mid, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, needs]
      by_cases ffiEnabled : conf.callEmptyFfi = true
      · have midRel : stateRel conf l1 l2 source mid none locs := by
          simpa [mid, WordSemStateFiniteExact.setVar, stateRel_insert_1] using related
        obtain ⟨wordCut, targetCut⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs names cutData ⟨related, cutRun⟩
        have midCut : wordSemCutEnv (adjustSets names) mid.locals = some wordCut := by
          simpa [mid, WordSemStateFiniteExact.setVar, cutEnv_adjustSets_insertOdd names target.locals 1 (.word (trigger - next)) (by decide)] using targetCut
        let pruned := {target with locals := wordCut, fpRegs := HolFiniteMapExact.empty}
        have firstRun : WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets names)) mid = (none, pruned) := by
          have h := Assign.evaluate_silentFfi_three conf l1 l2 source mid locs names wordCut ⟨ffiEnabled, midRel, midCut⟩
          simpa [mid, WordSemStateFiniteExact.setVar, pruned] using h
        have cutRel := stateRel_cutEnv_cutEnv conf l1 l2 source target locs names cutData wordCut ⟨related, cutRun, targetCut⟩
        have preRel : stateRel conf l1 l2 {source with locals := cutData} pruned none locs := by
          simpa [pruned] using stateRel_withFpRegs conf l1 l2 {source with locals := cutData}
            {target with locals := wordCut} none locs HolFiniteMapExact.empty cutRel
        have recut : DataSem.cutEnv names cutData = some cutData := Assign.cutEnv_idempotent names source.locals cutData cutRun
        cases halloc : WordSemStateFiniteExact.alloc (gcAllocSize amount) (adjustSets names) pruned with
        | mk q out =>
          have allocation := allocLemma conf l1 l2 {source with locals := cutData} pruned out locs names cutData amount q
            ⟨preRel, recut, halloc⟩
          have runYes : WordSemStateFiniteExact.evaluate yes mid =
              match q with
              | none => WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets names)) out
              | some _ => (q, out) := by
            have clocks := WordSemStateFiniteExact.alloc_clock (α := Unit) (gcAllocSize amount) (adjustSets names) () pruned q out halloc
            have firstFix : WordSemStateFiniteExact.fixClock mid ((none : Option (WordSemResult width)), pruned) = (none, pruned) := by
              simp [WordSemStateFiniteExact.fixClock, mid, pruned, WordSemStateFiniteExact.setVar]
            simp only [yes, wordListSeq, WordSemStateFiniteExact.evaluate, firstRun, firstFix]
            cases q <;> simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
              sptLookup_sptInsert_same, alloc_locals_insert_one, halloc,
              Nat.not_lt.mpr clocks.1] <;> cases out <;> simp_all
          by_cases bad : q = some .notEnoughSpace
          · obtain ⟨ffiEq, stackBound, heapBound⟩ := allocation.1 bad
            subst q
            have exec : WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target =
                (some .notEnoughSpace, out) := by
              rw [chosen, runYes]
            refine ⟨out, some .notEnoughSpace, exec, ?_, ?_, ?_⟩
            · simpa [DataSem.addSpace] using stackBound
            · intro _
              refine ⟨?_, ?_⟩
              · simp [DataSem.addSpace] at ffiEq ⊢
                simp [ffiEq]
              · intro kind
                by_cases noThunks : DataSem.noThunksInRefs source.refs
                · have overflow := heapBound ⟨kind, noThunks⟩
                  have hsize : DataSem.sizeOfHeap (cutLocals names {source with locals := cutData}) =
                      DataSem.sizeOfHeap {source with locals := cutData} := by
                    simp [cutLocals, recut]
                  rw [hsize] at overflow
                  simp [DataSem.addSpace, noThunks, Nat.not_le_of_gt overflow]
                · simp [DataSem.addSpace, noThunks]
            · simp
          · obtain ⟨finalRel, _, _, _, _, _, _, qnone⟩ := allocation.2 bad
            subst q
            let sourceAlloc := {source with locals := cutData, space := amount}
            have postRel : stateRel conf l1 l2 sourceAlloc out none locs := finalRel
            have allocCut : DataSem.cutEnv names sourceAlloc.locals = some cutData := recut
            obtain ⟨postCut, postCutRun⟩ := cutEnv_imp_wordCutEnv conf l1 l2 sourceAlloc out locs names cutData ⟨postRel, allocCut⟩
            let final := {out with locals := postCut, fpRegs := HolFiniteMapExact.empty}
            have secondRun : WordSemStateFiniteExact.evaluate (silentFfi conf 3 (adjustSets names)) out = (none, final) := by
              have h := Assign.evaluate_silentFfi_three conf l1 l2 sourceAlloc out locs names postCut ⟨ffiEnabled, postRel, postCutRun⟩
              simpa [final] using h
            have resultRel := stateRel_cutEnv_cutEnv conf l1 l2 sourceAlloc out locs names cutData postCut ⟨postRel, allocCut, postCutRun⟩
            have finalRel2 : stateRel conf l1 l2 sourceAlloc final none locs := by
              have h := stateRel_withFpRegs conf l1 l2 {sourceAlloc with locals := cutData}
                {out with locals := postCut} none locs HolFiniteMapExact.empty resultRel
              simpa [final, sourceAlloc] using h
            have exec : WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target =
                (none, final) := by
              rw [chosen, runYes, secondRun]
            have stackBound := finalRel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            refine ⟨final, none, exec, ?_, ?_, ?_⟩
            · simpa [DataSem.addSpace, sourceAlloc] using stackBound
            · simp
            · intro _
              refine ⟨?_, rfl⟩
              unfold stateRel at finalRel2 ⊢
              simpa [DataSem.addSpace, sourceAlloc] using finalRel2
      · have ffiDisabled : conf.callEmptyFfi = false := by cases h : conf.callEmptyFfi <;> simp_all
        cases halloc : WordSemStateFiniteExact.alloc (gcAllocSize amount) (adjustSets names) target with
        | mk q out =>
          have allocation := allocLemma conf l1 l2 source target out locs names cutData amount q ⟨related, cutRun, halloc⟩
          have execute : WordSemStateFiniteExact.evaluate yes mid = (q, out) := by
            have clocks := WordSemStateFiniteExact.alloc_clock (α := Unit) (gcAllocSize amount) (adjustSets names) () target q out halloc
            cases q <;> simp [yes, silentFfi, ffiDisabled, wordListSeq, WordSemStateFiniteExact.evaluate,
              WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
              sptLookup_sptInsert_same, mid, sptInsert_insert_shadow, alloc_locals_insert_one, halloc,
              Nat.not_lt.mpr clocks.1] <;> cases out <;> simp_all
          by_cases bad : q = some .notEnoughSpace
          · obtain ⟨ffiEq, stackBound, heapBound⟩ := allocation.1 bad
            subst q
            refine ⟨out, some .notEnoughSpace, chosen.trans execute, ?_, ?_, ?_⟩
            · simpa [DataSem.addSpace] using stackBound
            · intro _
              refine ⟨?_, ?_⟩
              · simp [DataSem.addSpace, ffiEq]
              · intro kind
                by_cases noThunks : DataSem.noThunksInRefs source.refs
                · have overflow := heapBound ⟨kind, noThunks⟩
                  have hsize : DataSem.sizeOfHeap (cutLocals names source) =
                      DataSem.sizeOfHeap {source with locals := cutData} := by
                    simp [cutLocals, cutRun]
                  rw [hsize] at overflow
                  simp [DataSem.addSpace, noThunks, Nat.not_le_of_gt overflow]
                · simp [DataSem.addSpace, noThunks]
            · simp
          · obtain ⟨finalRel, _, _, _, _, _, _, qnone⟩ := allocation.2 bad
            subst q
            have stackBound := finalRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            refine ⟨out, none, chosen.trans execute, ?_, ?_, ?_⟩
            · simpa [DataSem.addSpace] using stackBound
            · simp
            · intro _
              refine ⟨?_, rfl⟩
              unfold stateRel at finalRel ⊢
              simpa [DataSem.addSpace] using finalRel
    · have enough : WordSemStateFiniteExact.hasSpace (.word (gcAllocSize amount) : WordLocW width) mid = some true := by
        have hle : (gcAllocSize amount : BitVec width).toNat ≤ (trigger - next).toNat := by
          exact Nat.le_of_not_gt (by simpa [BitVec.lt_def] using needs)
        simp [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore, mid,
          WordSemStateFiniteExact.setVar, triggerStore, nextStore]
        simpa [BitVec.toNat_sub] using hle
      have midRel : stateRel conf l1 l2 source mid none locs := by
        simpa [mid, WordSemStateFiniteExact.setVar, stateRel_insert_1] using related
      have cutRel := stateRel_cutEnv conf l1 l2 source mid locs names cutData ⟨midRel, cutRun⟩
      have spaceRel := hasSpace_stateRel conf l1 l2 {source with locals := cutData} mid locs amount ⟨enough, cutRel⟩
      have execute : WordSemStateFiniteExact.evaluate (compileControl conf n l (.makeSpace amount names)).1 target =
          (none, mid) := by
        rw [midRun]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
          mid, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, needs]
      refine ⟨mid, none, execute, ?_, ?_, ?_⟩
      · simpa [mid, WordSemStateFiniteExact.setVar, DataSem.addSpace] using
          related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · simp
      · intro _
        refine ⟨?_, rfl⟩
        unfold stateRel at spaceRel ⊢
        simpa [DataSem.addSpace] using spaceRel

end Flapjack.Compiler.Backend.DataToWord.Proofs
