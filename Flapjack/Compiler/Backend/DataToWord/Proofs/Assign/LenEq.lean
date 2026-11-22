module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.TagEq
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SmallWordLemmas

@[expose] public section

/-! Block length tests in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Extract the successful source operation used by the length test. -/
private theorem lenEqSourceRun {C F : Type} (len : Nat)
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp (.lenEq len)) values source = .val (result, resultState)) :
    ∃ stamp found elements,
      values = [.block stamp found elements] ∧
      result = DataSem.boolValue (decide (elements.length = len)) ∧
      resultState = DataSem.doStack (.blockOp (.lenEq len)) values
        (DataSem.doLimSafe source (.blockOp (.lenEq len)) values) := by
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

/-- The length-and-marker mask of a pointer word keeps the length annotation and
the pointer marker. This is the HOL `assign_LenEq` rewriting step with
`all_ones_get_addr`, `all_ones_and_1` and `all_ones_and_ptr_bits_tag_0`;
Flapjack proof infrastructure without a separate HOL declaration. -/
theorem allOnes_len_getAddr {width : Nat} [NeZero width] (c : Config) (ptr tag len : Nat) :
    getAddr c ptr (.word (ptrBits c tag len : BitVec width)) &&& allOnes (c.lenBits + 1) 0 =
      ptrBits c 0 len ||| 1 := by
  have split : (allOnes (c.lenBits + 1) 0 : BitVec width) =
      allOnes (c.lenBits + 1) 0 &&& allOnes (c.lenBits + (c.tagBits + 1)) 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 := allOnes_bit (width := width) (c.lenBits + 1) 0 i hi
    have h2 := allOnes_bit (width := width) (c.lenBits + (c.tagBits + 1)) 0 i hi
    rw [BitVec.getLsbD_and]
    by_cases low : i < c.lenBits + 1
    · rw [h1.mpr ⟨by omega, low⟩, h2.mpr ⟨by omega, by omega⟩]; rfl
    · have : (allOnes (c.lenBits + 1) 0 : BitVec width).getLsbD i = false := by
        cases hb : (allOnes (c.lenBits + 1) 0 : BitVec width).getLsbD i
        · rfl
        · exact absurd (h1.mp hb).2 low
      rw [this]; rfl
  rw [BitVec.and_comm, split, BitVec.and_assoc, allOnes_getAddr, BitVec.and_or_distrib_left,
    allOnes_and_ptrBits_tag_0, allOnes_and_1 _ (by omega)]

namespace LenEqAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LenEqAssignmentWitness

/-- Block length tests satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_LenEq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLenEq_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ len, op = .blockOp (.lenEq len))
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
  obtain ⟨len, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨stamp, found, elements, valuesEq, resultEq, stateEq⟩ :=
    lenEqSourceRun len source resultState values result run
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
  let answer := decide (elements.length = len)
  have lengthBound : elements.length < 2 ^ width := by
    by_cases empty : elements = []
    · subst empty; exact Nat.two_pow_pos width
    · simp only [if_neg empty] at blockInfo
      obtain ⟨_, _, _, _, _, _, _, _, _, bound, _, _⟩ := blockInfo
      exact Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
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
  have runFacts : ∃ scratch : WordSemStateFiniteExact width C F,
      (∀ (s : DataSem.State C F) v,
        stateRel conf l1 l2 s scratch v locs = stateRel conf l1 l2 s target v locs) ∧
      WordSemStateFiniteExact.evaluate
        (compileAssign conf n l dest (.blockOp (.lenEq len)) [a] none).1 target =
        (none, scratch.setVar (adjustVar dest) (.word (if answer then 18 else 2))) := by
    have compiled : (compileAssign (width := width) conf n l dest (.blockOp (.lenEq len)) [a] none).1 =
        if len = 0 then setBool (adjustVar dest) .test (adjustVar a) (.imm 1)
        else if len < 2 ^ conf.lenBits - 1 then
          .seq (.assign 1 (.op .and [.var (adjustVar a), .const (allOnes (conf.lenBits + 1) 0)]))
            (setBool (adjustVar dest) .equal 1 (.imm (ptrBits conf 0 len ||| 1)))
        else if len < 2 ^ width then
          wordListSeq [.assign 1 (.const 0),
            .ite .test (adjustVar a) (.imm 1) .skip
              (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar a))) (width - conf.lenSize))),
            setBool (adjustVar dest) .equal 1 (.imm (BitVec.ofNat width len))]
        else .assign (adjustVar dest) (.const 2) := by
      simp only [compileAssign, arg1, assignLenEq]
      split_ifs <;> rfl
    rw [compiled]
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
    by_cases zero : len = 0
    · rw [if_pos zero]
      refine ⟨target, fun _ _ => rfl, ?_⟩
      simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, operand,
        test, answer, zero, WordSemStateFiniteExact.wordExp]
      by_cases empty : elements = [] <;> simp [empty]
    rw [if_neg zero]
    by_cases short : len < 2 ^ conf.lenBits - 1
    · rw [if_pos short]
      have lenBitsLt : conf.lenBits < width := by
        have h := heapMem.2.2
        simp only [shiftLength] at h
        omega
      have masked : (w &&& allOnes (conf.lenBits + 1) 0 == (ptrBits conf 0 len ||| 1 : BitVec width)) =
          answer := by
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
          rw [ptrEq, allOnes_len_getAddr]
          have iff := ptrBits_eq_ptrBits_len_only (width := width) conf len elements.length
            ⟨short, lenBitsLt⟩
          by_cases same : elements.length = len
          · simp [answer, same]
          · simp only [answer, same, decide_false]
            exact beq_eq_false_iff_ne.mpr (fun h => same (iff.mp h))
      refine ⟨target.setVar 1 (.word (w &&& allOnes (conf.lenBits + 1) 0)), scratchRel _, ?_⟩
      simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.wordExp, operand, fixClock_setVar_self, getOne, theWords, wordOpHOL,
        wordOp]
      have masked' : (w &&& allOnes (conf.lenBits + 1) 0 == ptrBits conf 0 len ||| 1#width) = answer :=
        masked
      simp only [andOp_and_allOnes, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, masked']
      by_cases hb : answer = true <;> simp [hb]
    rw [if_neg short]
    by_cases fits : len < 2 ^ width
    · rw [if_pos fits]
      simp only [wordListSeq, setBool]
      let s0 := target.setVar 1 (.word 0#width)
      have lenWord : ∀ m, m < 2 ^ width →
          (BitVec.ofNat width m == BitVec.ofNat width len) = decide (m = len) := by
        intro m hm
        by_cases same : m = len
        · simp [same]
        · simp only [same, decide_false]
          apply beq_eq_false_iff_ne.mpr
          intro h
          have := congrArg BitVec.toNat h
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt fits] at this
          exact same this
      by_cases empty : elements = []
      · have testTrue : wordSemWordCmp .test (.word w) (.word (1#width)) = some true := by
          simpa [empty] using test
        have noAnswer : answer = false := by
          simp only [answer, decide_eq_false_iff_not, empty, List.length_nil]
          omega
        refine ⟨s0, scratchRel _, ?_⟩
        have zeroWord := lenWord 0 (Nat.two_pow_pos width)
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
          WordSemStateFiniteExact.wordExp, operand1, fixClock_setVar_self, fixClock_self, getOne,
          testTrue, s0, noAnswer]
        have zeroNe : (0#width == BitVec.ofNat width len) = false := by
          rw [show (0#width) = BitVec.ofNat width 0 from rfl, zeroWord]
          simp only [decide_eq_false_iff_not]
          omega
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, zeroNe]
      · have testFalse : wordSemWordCmp .test (.word w) (.word (1#width)) = some false := by
          simpa [empty] using test
        simp only [if_neg empty] at blockInfo
        obtain ⟨address, header, _, _, _, real, headerRead, headerDomain,
          headerLength, sizeBound, _, _⟩ := blockInfo
        let lengthWord : BitVec width := BitVec.ofNat width elements.length
        have lengthEq : header >>> (width - conf.lenSize) = lengthWord := by
          simpa [WordGcFunctions.decodeLength, lengthWord] using headerLength
        have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) (WordSemStateFiniteExact.setVar 1 (.word 0#width) target) w address
          ⟨heapMem.2.2, good, operand1 _, real⟩
        have offsetBound : width - conf.lenSize < width := by
          have positive := NeZero.pos width
          have := heapMem.1
          omega
        have widthBound : width < 2 ^ width := by
          rcases good with h | h <;> subst width <;> decide
        have offsetWord : (BitVec.ofNat width (width - conf.lenSize)).toNat = width - conf.lenSize := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans offsetBound widthBound)]
        have dom0 : (WordSemStateFiniteExact.setVar 1 (.word 0#width) target).mdomain address = true := headerDomain
        have mem0 : (WordSemStateFiniteExact.setVar 1 (.word 0#width) target).memory address = .word header := headerRead
        have valueExp : (WordSemStateFiniteExact.setVar 1 (.word 0#width) target).wordExp (shiftN .lsr (.load (realAddr conf (adjustVar a)))
              (width - conf.lenSize)) = some (.word lengthWord) := by
          simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
            shiftN, realExp, dom0, mem0, wordShiftHOL, offsetWord,
            Nat.not_le_of_gt offsetBound, lengthEq]
        refine ⟨(WordSemStateFiniteExact.setVar 1 (.word 0#width) target).setVar 1 (.word lengthWord), fun t v => ?_, ?_⟩
        · exact (stateRel_insert_1 conf l1 l2 t (WordSemStateFiniteExact.setVar 1 (.word 0#width) target) v locs _).trans (scratchRel _ t v)
        · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
            WordSemStateFiniteExact.wordExp, operand1, fixClock_setVar_self, getOne,
            testFalse, valueExp]
          have cmp := lenWord elements.length lengthBound
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, lengthWord, cmp]
          by_cases same : elements.length = len <;> simp [answer, same]
    · rw [if_neg fits]
      have no : answer = false := by
        simp only [answer, decide_eq_false_iff_not]
        omega
      refine ⟨target, fun _ _ => rfl, ?_⟩
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, no]
  obtain ⟨scratch, relEq, evalEq⟩ := runFacts
  exact blockTest_finish conf l1 l2 dest _ _ source target scratch locs _ answer related relEq evalEq
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
