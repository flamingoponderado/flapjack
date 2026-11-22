module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.LenEq
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockTests
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.WordArith

@[expose] public section

/-! Block tag-and-length tests in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Extract the successful source operation used by the tag-and-length test. -/
private theorem tagLenEqSourceRun {C F : Type} (tag len : Nat)
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp (.tagLenEq tag len)) values source = .val (result, resultState)) :
    ∃ stamp found elements,
      values = [.block stamp found elements] ∧
      result = DataSem.boolValue (decide (found = tag ∧ elements.length = len)) ∧
      resultState = DataSem.doStack (.blockOp (.tagLenEq tag len)) values
        (DataSem.doLimSafe source (.blockOp (.tagLenEq tag len)) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | cons w ws => cases v <;> simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset,
        DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at run
    | nil =>
      cases v <;>
        simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi]

namespace TagLenEqAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end TagLenEqAssignmentWitness

/-- Combined block tag and length tests satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_TagLenEq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignTagLenEq_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ tag len, op = .blockOp (.tagLenEq tag len))
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
  obtain ⟨tag, len, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨stamp, found, elements, valuesEq, resultEq, stateEq⟩ :=
    tagLenEqSourceRun tag len source resultState values result run
  subst values
  subst result
  subst resultState
  obtain ⟨a, w, rfl, operand, vars, roots⟩ :=
    blockArg_setup conf l1 l2 source target locs args stamp found elements related argsEq
  have good := related.2.2.2.2.2.2.1
  obtain ⟨w', wordEq, blockInfo⟩ := memoryRel_blockImp conf target.be (holThe source.tstamps)
    source.refs source.space target.store target.memory target.mdomain stamp found elements
    (.word w) vars ⟨roots, good⟩
  cases wordEq
  have heapMem := heapFacts conf l1 l2 source target locs related
  let answer := decide (found = tag ∧ elements.length = len)
  have operand1 : ∀ x : WordLocW width,
      WordSemStateFiniteExact.getVar (adjustVar a) (target.setVar 1 x) = some (.word w) := by
    intro x
    simp only [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar] at operand ⊢
    rw [sptLookup_sptInsert_ne 1 (adjustVar a) _ _ (by simp [adjustVar])]
    exact operand
  have getOne : ∀ (s : WordSemStateFiniteExact width C F) (x : WordLocW width),
      WordSemStateFiniteExact.getVar 1 (s.setVar 1 x) = some x := by
    intro s x
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  have scratchRel : ∀ x (s : DataSem.State C F) v,
      stateRel conf l1 l2 s (target.setVar 1 x) v locs = stateRel conf l1 l2 s target v locs :=
    fun x s v => stateRel_insert_1 conf l1 l2 s target v locs x
  have lowBit : w.getLsbD 0 = !decide (elements = []) := by
    by_cases empty : elements = []
    · simp only [empty, ite_true] at blockInfo
      simp [empty, blockInfo.2.1]
    · simp only [if_neg empty] at blockInfo
      obtain ⟨_, _, low, _⟩ := blockInfo
      simp [empty, low]
  have test : wordSemWordCmp .test (.word w) (.word (1#width)) = some (decide (elements = [])) := by
    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
    change (w &&& (1 : BitVec width) == 0) = _
    have iff := StackAlloc.word_and_one_eq_0_iff w
    by_cases empty : elements = [] <;> simp_all
  have runFacts : ∃ scratch : WordSemStateFiniteExact width C F,
      (∀ (s : DataSem.State C F) v,
        stateRel conf l1 l2 s scratch v locs = stateRel conf l1 l2 s target v locs) ∧
      WordSemStateFiniteExact.evaluate
        (compileAssign conf n l dest (.blockOp (.tagLenEq tag len)) [a] none).1 target =
        (none, scratch.setVar (adjustVar dest) (.word (if answer then 18 else 2))) := by
    have compiled : (compileAssign (width := width) conf n l dest (.blockOp (.tagLenEq tag len)) [a] none).1 =
        if len = 0 then
          (if tag < 2 ^ width / 16 then
            setBool (adjustVar dest) .equal (adjustVar a) (.imm (BitVec.ofNat width (16 * tag + 2)))
          else .assign (adjustVar dest) (.const 2))
        else if tag < 2 ^ conf.tagBits - 1 ∧ len < 2 ^ conf.lenBits - 1 then
          .seq (.assign 1 (.op .and [.var (adjustVar a),
              .const (allOnes (conf.lenBits + conf.tagBits + 1) 0)]))
            (setBool (adjustVar dest) .equal 1 (.imm (ptrBits conf tag len ||| 1)))
        else
          match encodeHeader (width := width) conf (4 * tag) len with
          | none => .assign (adjustVar dest) (.const 2)
          | some header => wordListSeq [.assign 1 (.const 0),
              .ite .test (adjustVar a) (.imm 1) .skip (.assign 1 (.load (realAddr conf (adjustVar a)))),
              setBool (adjustVar dest) .equal 1 (.imm header)] := by
      simp only [compileAssign, arg1, assignTagLenEq]
      split_ifs <;> try rfl
      cases encodeHeader (width := width) conf (4 * tag) len <;> rfl
    rw [compiled]
    have rel0 : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain ((.block stamp found elements, .word w) :: vars) := roots
    by_cases zero : len = 0
    · rw [if_pos zero]
      refine ⟨target, fun _ _ => rfl, ?_⟩
      by_cases small : tag < 2 ^ width / 16
      · rw [if_pos small]
        obtain ⟨v, vEq, iff⟩ := memoryRel_testNilEq conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain stamp found tag elements
          (.word w) vars ⟨rel0, small, good⟩
        cases vEq
        have cmp : (w == BitVec.ofNat width (16 * tag + 2)) = answer := by
          by_cases h : w = BitVec.ofNat width (16 * tag + 2)
          · have := iff.mp h
            simp [h, answer, this.1, this.2, zero]
          · have : ¬ (found = tag ∧ elements.length = len) := by
              rintro ⟨h1, h2⟩
              exact h (iff.mpr ⟨h1, List.length_eq_zero_iff.mp (by omega)⟩)
            simp only [answer, this, decide_false]
            exact beq_eq_false_iff_ne.mpr h
        simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
          WordSemStateFiniteExact.wordExp, operand]
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, cmp]
        by_cases hb : answer = true <;> simp [hb]
      · rw [if_neg small]
        have limit := memoryRel_tagLimit conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain stamp found elements
          (.word w) vars ⟨rel0, good⟩
        have no : answer = false := by
          simp only [answer, decide_eq_false_iff_not]
          rintro ⟨rfl, _⟩
          exact small limit
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, no]
    rw [if_neg zero]
    by_cases short : tag < 2 ^ conf.tagBits - 1 ∧ len < 2 ^ conf.lenBits - 1
    · rw [if_pos short]
      have bitsLt : conf.lenBits + conf.tagBits < width := by
        have h := heapMem.2.2
        simp only [shiftLength] at h
        omega
      have masked : (w &&& (allOnes (conf.lenBits + conf.tagBits + 1) 0 : BitVec width) == ptrBits conf tag len ||| 1#width) = answer := by
        by_cases empty : elements = []
        · have noAnswer : answer = false := by
            simp only [answer, decide_eq_false_iff_not, empty, List.length_nil]
            omega
          rw [noAnswer]
          apply beq_eq_false_iff_ne.mpr
          intro h
          have bit := congrArg (fun x : BitVec width => x.getLsbD 0) h
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, lowBit, empty] at bit
          simp [NeZero.pos width] at bit
        · obtain ⟨ptr, ptrEq⟩ := memoryRel_blockPtr conf target.be (holThe source.tstamps)
            source.refs source.space target.store target.memory target.mdomain stamp found elements
            w vars roots empty
          have get : w &&& (allOnes (conf.lenBits + conf.tagBits + 1) 0 : BitVec width) = ptrBits conf found elements.length ||| 1 := by
            rw [ptrEq, BitVec.and_comm]
            simp only [Nat.add_assoc]
            exact allOnes_getAddr conf ptr found elements.length
          rw [get]
          have iff := ptrBits_eq_ptrBits (width := width) conf tag len found elements.length
            ⟨short.1, short.2, bitsLt⟩
          by_cases same : found = tag ∧ elements.length = len
          · simp [answer, same]
          · simp only [answer, same, decide_false]
            exact beq_eq_false_iff_ne.mpr (fun h => same (iff.mp h))
      refine ⟨target.setVar 1 (.word (w &&& (allOnes (conf.lenBits + conf.tagBits + 1) 0 : BitVec width))), scratchRel _, ?_⟩
      simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.wordExp, operand, fixClock_setVar_self, getOne, theWords, wordOpHOL,
        wordOp]
      simp only [andOp_and_allOnes, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, masked]
      by_cases hb : answer = true <;> simp [hb]
    rw [if_neg short]
    cases enc : encodeHeader (width := width) conf (4 * tag) len with
    | none =>
      have notBoth := memoryRel_testNoneEq conf target.be (holThe source.tstamps)
        source.refs source.space target.store target.memory target.mdomain stamp found tag len elements
        (.word w) vars ⟨enc, rel0, zero, good⟩
      have no : answer = false := by
        simp only [answer, decide_eq_false_iff_not]
        exact notBoth
      refine ⟨target, fun _ _ => rfl, ?_⟩
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, no]
    | some header =>
      simp only [wordListSeq, setBool]
      by_cases empty : elements = []
      · have testTrue : wordSemWordCmp .test (.word w) (.word (1#width)) = some true := by
          simpa [empty] using test
        have noAnswer : answer = false := by
          simp only [answer, decide_eq_false_iff_not, empty, List.length_nil]
          omega
        have nonzero := encodeHeader_ne_zero conf (4 * tag) len header enc
        have zeroNe : (0#width == header) = false :=
          beq_eq_false_iff_ne.mpr (fun h => nonzero (h.symm.trans rfl))
        refine ⟨(WordSemStateFiniteExact.setVar 1 (.word 0#width) target), scratchRel _, ?_⟩
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
          WordSemStateFiniteExact.wordExp, operand1, fixClock_setVar_self, fixClock_self, getOne,
          testTrue, noAnswer]
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, zeroNe]
      · have testFalse : wordSemWordCmp .test (.word w) (.word (1#width)) = some false := by
          simpa [empty] using test
        simp only [if_neg empty] at blockInfo
        obtain ⟨address, x, _, _, _, real, headerRead, headerDomain, _, _, encoded, _⟩ := blockInfo
        have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) (WordSemStateFiniteExact.setVar 1 (.word 0#width) target) w address
          ⟨heapMem.2.2, good, operand1 _, real⟩
        have dom0 : (WordSemStateFiniteExact.setVar 1 (.word 0#width) target).mdomain address = true := headerDomain
        have mem0 : (WordSemStateFiniteExact.setVar 1 (.word 0#width) target).memory address = .word x := headerRead
        have cmp : (x == header) = answer := by
          have iff := encodeHeader_eq conf (4 * found) elements.length (4 * tag) len x header
            ⟨encoded, enc, by have := heapMem.2.1; omega⟩
          by_cases same : found = tag ∧ elements.length = len
          · have : x = header := iff.mpr ⟨by rw [same.1], same.2⟩
            simp [answer, same, this]
          · simp only [answer, same, decide_false]
            exact beq_eq_false_iff_ne.mpr (fun h => same ⟨by have := (iff.mp h).1; omega, (iff.mp h).2⟩)
        refine ⟨(WordSemStateFiniteExact.setVar 1 (.word 0#width) target).setVar 1 (.word x), fun t v => ?_, ?_⟩
        · exact (stateRel_insert_1 conf l1 l2 t (WordSemStateFiniteExact.setVar 1 (.word 0#width) target) v locs _).trans (scratchRel _ t v)
        · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
            WordSemStateFiniteExact.wordExp, operand1, fixClock_setVar_self, getOne,
            testFalse, realExp, WordSemStateFiniteExact.memLoad, dom0, mem0]
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, cmp]
          by_cases hb : answer = true <;> simp [hb]
  obtain ⟨scratch, relEq, evalEq⟩ := runFacts
  exact blockTest_finish conf l1 l2 dest _ _ source target scratch locs _ answer related relEq evalEq
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
