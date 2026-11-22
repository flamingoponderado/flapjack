module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.LengthBlock
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeaderInjective
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Bool
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateInsert

@[expose] public section

/-! Block tag tests in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The tag mask is HOL's `tag_mask` slice when the length field fits in the
word. Flapjack proof infrastructure for the tag tests; HOL unfolds `tag_mask_def`. -/
theorem tagMask_eq_holSlice {width : Nat} [NeZero width] (conf : Config)
    (good : goodDimindex width) (lt : conf.lenSize < width) :
    tagMask (width := width) conf = holWordSlice (width - conf.lenSize - 1) 2 (~~~(0 : BitVec width)) := by
  rcases good with h | h <;> subst width <;> interval_cases hlen : conf.lenSize <;>
    simp_all only [tagMask, holWordSlice] <;> decide +kernel

/-- Equality of encoded small tags decides equality of the tags.
Flapjack proof infrastructure for the HOL `LESS_DIV_16_IMP` rewriting step. -/
theorem tagWord_beq {width : Nat} (found tag : Nat)
    (foundBound : found < 2 ^ width / 16) (tagBound : tag < 2 ^ width / 16) :
    (BitVec.ofNat width (16 * found + 2) == BitVec.ofNat width (16 * tag + 2)) =
      decide (found = tag) := by
  have h1 : 16 * found + 2 < 2 ^ width := by omega
  have h2 : 16 * tag + 2 < 2 ^ width := by omega
  by_cases eq : found = tag
  · subst eq; simp
  · simp only [eq, decide_false]
    apply beq_eq_false_iff_ne.mpr
    intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    omega

/-- Fixing the clock after a local update is the identity.
Flapjack proof infrastructure for the straight-line tag tests; no HOL declaration. -/
theorem fixClock_setVar_self {width : Nat} [NeZero width] {C F R : Type}
    (state : WordSemStateFiniteExact width C F) (k : Nat) (x : WordLocW width) (r : R) :
    state.fixClock (r, state.setVar k x) = (r, state.setVar k x) := by
  simp [WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.setVar]

/-- Fixing the clock of an unchanged state is the identity.
Flapjack proof infrastructure for the straight-line tag tests; no HOL declaration. -/
theorem fixClock_self {width : Nat} [NeZero width] {C F R : Type}
    (state : WordSemStateFiniteExact width C F) (r : R) :
    state.fixClock (r, state) = (r, state) := by
  simp [WordSemStateFiniteExact.fixClock]

/-- The word-semantics fold of a binary `And` is the ordinary conjunction.
Flapjack proof infrastructure; no HOL declaration. -/
theorem andOp_and_allOnes {width : Nat} (x y : BitVec width) :
    AndOp.and x (AndOp.and y (BitVec.allOnes width)) = x &&& y := by
  change x &&& (y &&& BitVec.allOnes width) = _
  rw [BitVec.and_allOnes]

/-- Extract the successful source operation used by the tag test. -/
private theorem tagEqSourceRun {C F : Type} (tag : Nat)
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp (.tagEq tag)) values source = .val (result, resultState)) :
    ∃ stamp found elements,
      values = [.block stamp found elements] ∧
      result = DataSem.boolValue (decide (found = tag)) ∧
      resultState = DataSem.doStack (.blockOp (.tagEq tag)) values
        (DataSem.doLimSafe source (.blockOp (.tagEq tag)) values) := by
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

/-- A single block argument of a related source state is held in an even target
variable as a word related by the memory relation. Flapjack proof
infrastructure shared by the block tests; HOL uses `memory_rel_get_vars_IMP`
and `memory_rel_Block_IMP` inline. -/
theorem blockArg_setup {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (args : List Nat) (stamp tag : Nat) (elements : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (argsEq : DataSem.getVars args source.locals = some [.block stamp tag elements]) :
    ∃ a w, args = [a] ∧ WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) ∧
      ∃ vars, memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain ((.block stamp tag elements, .word w) :: vars) := by
  have argLen : args.length = 1 := by
    have h := DataSpace.getVars_length args source.locals [.block stamp tag elements] argsEq
    simpa using h.symm
  match args, argLen with
  | [a], _ =>
    obtain ⟨words, getWords, lengthEq⟩ :=
      stateRel_getVars conf l1 l2 source target locs [a] [.block stamp tag elements] related argsEq
    match words, lengthEq with
    | [word1], _ =>
      let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
        flatStack source.stack target.stack
      have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
        target.store target.memory target.mdomain target envs [a]
        [.block stamp tag elements] [word1] (by
          refine ⟨?_, argsEq, getWords⟩
          simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
      have good := related.2.2.2.2.2.2.1
      obtain ⟨w, wordEq, _⟩ := memoryRel_blockImp conf target.be
        (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain
        stamp tag elements word1 _ ⟨by simpa using roots, good⟩
      subst word1
      refine ⟨a, w, rfl, ?_, _, by simpa using roots⟩
      cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
        simp_all [WordSemStateFiniteExact.getVars]

/-- Configuration bounds carried by the heap part of the state relation.
Flapjack proof infrastructure; HOL reads them from `memory_rel_def` and
`heap_in_memory_store_def`. -/
theorem heapFacts {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (related : stateRel conf l1 l2 source target none locs) :
    conf.lenSize ≠ 0 ∧ conf.lenSize + 7 < width ∧ shiftLength conf < width := by
  obtain ⟨_, _, _, _, _, _, heapMem, _⟩ := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨heapMem.2.2.2.1, heapMem.2.2.2.2.1, heapMem.2.2.2.2.2.1⟩

/-- The common conclusion of the Boolean block tests: when the compiled test
leaves a scratch-only change and writes the encoded Boolean, the original
assignment goal holds. Flapjack proof infrastructure; HOL repeats the
`memory_rel_insert` and `memory_rel_Boolv_T/F` steps inline. -/
theorem blockTest_finish {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (l1 l2 dest : Nat) (op : ClosLang.Op) (values : List DataSem.Value)
    (source : DataSem.State C F) (target scratch : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (prog : WordLangProgHOL (BitVec width)) (answer : Bool)
    (related : stateRel conf l1 l2 source target none locs)
    (relEq : ∀ (s : DataSem.State C F) v,
      stateRel conf l1 l2 s scratch v locs = stateRel conf l1 l2 s target v locs)
    (evalEq : WordSemStateFiniteExact.evaluate prog target =
      (none, scratch.setVar (adjustVar dest) (.word (if answer then 18 else 2)))) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate prog target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧
        optionLe r.stackMax (DataSem.doStack op values (DataSem.doLimSafe source op values)).stackMax ∧
        (conf.gcKind ≠ .none →
          (DataSem.doStack op values (DataSem.doLimSafe source op values)).safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest (DataSem.boolValue answer)
          (DataSem.doStack op values (DataSem.doLimSafe source op values))) r none locs ∧ q = none) := by
  let next := DataSem.doStack op values (DataSem.doLimSafe source op values)
  have nextRel : stateRel conf l1 l2 next scratch none locs := by
    rw [relEq]
    exact stateRel_doStack conf l1 l2 _ target locs _ _
      (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
  have good := related.2.2.2.2.2.2.1
  have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have boolRoot := memoryRel_bool conf scratch.be (holThe next.tstamps) next.refs next.space
    scratch.store scratch.memory scratch.mdomain _ answer (.word (if answer then 18 else 2))
    ⟨hmem, good, fun h => by simp [h], fun h => by simp [h]⟩
  have updated := stateRel_insertRoot conf l1 l2 next scratch locs dest
    (DataSem.boolValue answer) (.word (if answer then 18 else 2)) nextRel (by simpa using boolRoot)
  exact ⟨none, _, evalEq, by simp, fun _ => ⟨updated, rfl⟩⟩

/-- A related nonempty block is a pointer word whose low bits are the block's
pointer annotation. Flapjack proof infrastructure; HOL unfolds
`memory_rel_def`, `v_inv_def` and `word_addr_def` inline. -/
theorem memoryRel_blockPtr {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List DataSem.Value) (w : BitVec width)
    (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf bigEndian next refs space store memory domain
      ((.block stamp tag values, .word w) :: vars))
    (nonempty : values ≠ []) :
    ∃ ptr, w = getAddr conf ptr (.word (ptrBits conf tag values.length)) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩ := rel
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, valueRel, _⟩ := stackInv
  cases roots with
  | nil => cases valueRel
  | cons root rest =>
    cases valueRel with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        obtain ⟨ptr, children, pair, _, rootEq, _⟩ :=
          (valueInv_nonemptyBlock conf stamp tag values refs root f tf heap nonempty).mp related
        subst root
        have childrenLength : values.length = children.length := pair.length_eq
        refine ⟨ptr, ?_⟩
        rw [childrenLength]
        simpa [wordAddr] using projected.symm

namespace TagEqAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end TagEqAssignmentWitness

/-- Block tag tests satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_TagEq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignTagEq_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ tag, op = .blockOp (.tagEq tag))
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
  obtain ⟨tag, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨stamp, found, elements, valuesEq, resultEq, stateEq⟩ :=
    tagEqSourceRun tag source resultState values result run
  subst values
  subst result
  subst resultState
  obtain ⟨a, w, rfl, operand, vars, roots⟩ :=
    blockArg_setup conf l1 l2 source target locs args stamp found elements related argsEq
  have good := related.2.2.2.2.2.2.1
  have blockInfo := (memoryRel_blockImp conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain stamp found elements (.word w) vars ⟨roots, good⟩)
  obtain ⟨w', wordEq, blockInfo⟩ := blockInfo
  cases wordEq
  have heapMem := heapFacts conf l1 l2 source target locs related
  have foundBound : found < 2 ^ width / 16 := by
    by_cases empty : elements = []
    · simp only [empty, ite_true] at blockInfo
      exact blockInfo.2.2.1
    · simp only [if_neg empty] at blockInfo
      obtain ⟨_, header, _, _, _, _, _, _, _, _, encoded, _⟩ := blockInfo
      exact (encodeHeader_tagMask conf found elements.length header encoded good).1
  let answer := decide (found = tag)
  let out : BitVec width := if answer then 18 else 2
  -- The register 1 scratch value left by the compiled code.
  have runFacts : ∃ scratch : WordSemStateFiniteExact width C F,
      (∀ (s : DataSem.State C F) v,
        stateRel conf l1 l2 s scratch v locs = stateRel conf l1 l2 s target v locs) ∧
      WordSemStateFiniteExact.evaluate
        (compileAssign conf n l dest (.blockOp (.tagEq tag)) [a] none).1 target =
        (none, scratch.setVar (adjustVar dest) (.word out)) := by
    have compiled : (compileAssign (width := width) conf n l dest (.blockOp (.tagEq tag)) [a] none).1 =
        if tag < 2 ^ width / 16 then
          wordListSeq [.assign 1 (.var (adjustVar a)),
            .ite .test (adjustVar a) (.imm 1) .skip
              (.assign 1 (.op .and [.load (realAddr conf (adjustVar a)), .const (tagMask conf ||| 2)])),
            setBool (adjustVar dest) .equal 1 (.imm (BitVec.ofNat width (16 * tag + 2)))]
        else .assign (adjustVar dest) (.const 2) := by
      simp only [compileAssign, arg1, assignTagEq]
      split <;> rfl
    rw [compiled]
    by_cases small : tag < 2 ^ width / 16
    · rw [if_pos small]
      simp only [wordListSeq, setBool]
      have beqTag := tagWord_beq found tag foundBound small
      have operand1 : WordSemStateFiniteExact.getVar (adjustVar a)
            (target.setVar 1 (.word w)) = some (.word w) := by
          simp only [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar] at operand ⊢
          rw [sptLookup_sptInsert_ne 1 (adjustVar a) _ _ (by simp [adjustVar])]
          exact operand
      have common : ∀ (s : DataSem.State C F) v,
          stateRel conf l1 l2 s (target.setVar 1 (.word w)) v locs =
            stateRel conf l1 l2 s target v locs :=
        fun s v => stateRel_insert_1 conf l1 l2 s target v locs (.word w)
      by_cases empty : elements = []
      · simp only [empty, ite_true] at blockInfo
        obtain ⟨wEq, low, _, _⟩ := blockInfo
        have mask : w &&& 1 = 0 := (StackAlloc.word_and_one_eq_0_iff w).mpr (by simp [low])
        have test : wordSemWordCmp .test (.word w) (.word (1#width)) = some true := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec width) == 0) = true
          exact beq_iff_eq.mpr mask
        have wNat : w = BitVec.ofNat width (16 * found + 2) := by
          rw [wEq]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]
          rw [Nat.mul_comm]
        refine ⟨target.setVar 1 (.word w), common, ?_⟩
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getVarImm, operand, operand1, test, fixClock_setVar_self,
          fixClock_self]
        have getOne : WordSemStateFiniteExact.getVar 1
            (WordSemStateFiniteExact.setVar 1 (.word w) target) = some (.word w) := by
          simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        rw [getOne]
        simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, wNat, beqTag]
        by_cases hf : found = tag <;> simp [out, answer, hf]
      · simp only [if_neg empty] at blockInfo
        obtain ⟨address, header, low, _, _, real, headerRead, headerDomain,
          _, _, encoded, _⟩ := blockInfo
        have mask : w &&& 1 ≠ 0 := fun h => (StackAlloc.word_and_one_eq_0_iff w).mp h (by simp [low])
        have test : wordSemWordCmp .test (.word w) (.word (1#width)) = some false := by
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
          change (w &&& (1 : BitVec width) == 0) = false
          exact beq_eq_false_iff_ne.mpr mask
        have realExp := Bignum.getRealAddr_lemma conf (adjustVar a)
          (target.setVar 1 (.word w)) w address
          ⟨heapMem.2.2, good, operand1, real⟩
        have lenLt : conf.lenSize < width := by
          have h := heapMem.2.1
          omega
        have tagged := (encodeHeader_tagMask conf found elements.length header encoded good).2
        rw [← tagMask_eq_holSlice conf good lenLt] at tagged
        let s1 := WordSemStateFiniteExact.setVar 1 (.word w) target
        let v : BitVec width := BitVec.ofNat width (16 * found + 2)
        refine ⟨s1.setVar 1 (.word v), fun s r => ?_, ?_⟩
        · exact (stateRel_insert_1 conf l1 l2 s s1 r locs (.word v)).trans (common s r)
        · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getVarImm, operand, operand1, test, fixClock_setVar_self,
            realExp, WordSemStateFiniteExact.memLoad]
          have dom1 : (WordSemStateFiniteExact.setVar 1 (.word w) target).mdomain address = true :=
            headerDomain
          have mem1 : (WordSemStateFiniteExact.setVar 1 (.word w) target).memory address =
            .word header := headerRead
          simp [dom1, mem1, theWords, wordOpHOL, wordOp, fixClock_setVar_self]
          have andv : AndOp.and header (AndOp.and (tagMask conf ||| 2#width) (BitVec.allOnes width)) =
              v := by
            change header &&& ((tagMask conf ||| 2#width) &&& BitVec.allOnes width) = _
            rw [BitVec.and_allOnes]
            exact tagged
          have getOne : WordSemStateFiniteExact.getVar 1
              (WordSemStateFiniteExact.setVar 1 (.word v) s1) = some (.word v) := by
            simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
              sptLookup_sptInsert_same]
          rw [andv, getOne]
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, v, beqTag]
          by_cases hf : found = tag <;> simp [out, answer, hf, s1]
    · have ne : answer = false := by
        simp only [answer, decide_eq_false_iff_not]
        intro h; subst h; exact small foundBound
      refine ⟨target, fun _ _ => rfl, ?_⟩
      simp [small, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, out, ne]
  obtain ⟨scratch, relEq, evalEq⟩ := runFacts
  exact blockTest_finish conf l1 l2 dest _ _ source target scratch locs _ answer related relEq evalEq
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
