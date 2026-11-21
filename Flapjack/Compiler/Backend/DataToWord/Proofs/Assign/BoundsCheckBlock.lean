module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.DerefByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BoundsCheck
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader



@[expose] public section

/-! Block bounds checks in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Extract the successful source operation used by the bounds-check simulation. -/
private theorem boundsBlockSourceRun {C F : Type}
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp .boundsCheckBlock) values source = .val (result, resultState)) :
    ∃ stamp tag index elements,
      values = [.block stamp tag elements, .number index] ∧
      result = DataSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat elements.length)) ∧
      resultState = DataSem.doStack (.blockOp .boundsCheckBlock) values
        (DataSem.doLimSafe source (.blockOp .boundsCheckBlock) values) := by
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

namespace BoundsBlockAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end BoundsBlockAssignmentWitness

/-- Block bounds checks satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_BoundsCheckBlock" 11214
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignBoundsCheckBlock_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .blockOp .boundsCheckBlock)
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
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  obtain ⟨stamp, tag, index, elements, valuesEq, resultEq, stateEq⟩ :=
    boundsBlockSourceRun source resultState values result run
  subst values
  subst result
  subst resultState
  have argLen : args.length = 2 := by
    have h := DataSpace.getVars_length args source.locals [.block stamp tag elements, .number index] argsEq
    simpa using h.symm
  cases args with
  | nil => simp at argLen
  | cons a args =>
    cases args with
    | nil => simp at argLen
    | cons b args =>
      cases args with
      | cons c rest => simp at argLen
      | nil =>
        obtain ⟨words, getWords, lengthEq⟩ :=
          stateRel_getVars conf l1 l2 source target locs [a,b] [.block stamp tag elements, .number index] related argsEq
        cases words with
        | nil => simp at lengthEq
        | cons word1 words =>
          cases words with
          | nil => simp at lengthEq
          | cons word2 words =>
            cases words with
            | cons word3 rest => simp at lengthEq
            | nil =>
              let envs := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
              let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
              have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                target.store target.memory target.mdomain target envs [a,b]
                [.block stamp tag elements, .number index] [word1,word2] (by
                  refine ⟨?_, argsEq, getWords⟩
                  simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
              have good := related.2.2.2.2.2.2.1
              obtain ⟨w, wordEq, blockInfo⟩ := memoryRel_blockImp conf target.be
                (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain
                stamp tag elements word1 ((.number index, word2) :: locals ++ envs)
                ⟨by simpa [locals] using roots, good⟩
              have tail := memoryRel_tail conf target.be (holThe source.tstamps) source.refs source.space
                target.store target.memory target.mdomain (.block stamp tag elements, word1)
                ((.number index, word2) :: locals ++ envs) (by simpa [locals] using roots)
              obtain ⟨indexWord, indexEq, indexBit⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps)
                source.refs source.space target.store target.memory target.mdomain index word2 (locals ++ envs) ⟨good, tail⟩
              subst word1
              subst word2
              have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) ∧
                  WordSemStateFiniteExact.getVar (adjustVar b) target = some (.word indexWord) := by
                cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                  cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
                  simp_all [WordSemStateFiniteExact.getVars]
              let lengthWord : BitVec width := BitVec.ofNat width elements.length
              let s1 := target.setVar 1 (.word lengthWord)
              have firstFacts : smallInt width (Int.ofNat elements.length) ∧
                  WordSemStateFiniteExact.evaluate
                    (.ite .test (adjustVar a) (.imm 1) (.assign 1 (.const 0))
                      (.assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar a)))
                        (width - conf.lenSize)))) target = (none, s1) := by
                by_cases empty : elements = []
                · subst elements
                  simp only [ite_true] at blockInfo
                  obtain ⟨_, low, _, _⟩ := blockInfo
                  have mask : w &&& 1 = 0 := (StackAlloc.word_and_one_eq_0_iff w).mpr (by simp [low])
                  have test : wordSemWordCmp .test (.word w) (.word (1 : BitVec width)) = some true := by
                    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
                    change (w &&& (1 : BitVec width) == 0) = true
                    exact beq_iff_eq.mpr mask
                  constructor
                  · rcases good with h | h <;> subst width <;> simp [smallInt]
                  · simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                      WordSemStateFiniteExact.getVarImm, operands.1, test,
                      - BitVec.ofNat_eq_ofNat, s1, lengthWord, WordSemStateFiniteExact.setVar]
                    rfl
                · simp only [if_neg empty] at blockInfo
                  obtain ⟨address, header, low, _, _, real, headerRead, headerDomain,
                    headerLength, sizeBound, _, _⟩ := blockInfo
                  have smallLength : smallInt width (Int.ofNat elements.length) := by
                    rcases good with h | h <;> subst width <;> simp [smallInt] at sizeBound ⊢ <;> omega
                  have lengthEq : header >>> (width - conf.lenSize) = lengthWord := by
                    simpa [WordGcFunctions.decodeLength, lengthWord] using headerLength
                  have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
                    ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
                  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  obtain ⟨heap, limit, ha, sp, sp1, gens, heapMem, _⟩ := mem
                  have lenPos : 0 < conf.lenSize := by
                    have h := heapMem.2.2.2.1
                    omega
                  have offsetBound : width - conf.lenSize < width := by
                    have positive := NeZero.pos width
                    omega
                  have widthBound : width < 2 ^ width := by
                    rcases good with h | h <;> subst width <;> decide
                  have offsetWord : (BitVec.ofNat width (width - conf.lenSize)).toNat = width - conf.lenSize := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans offsetBound widthBound)]
                  have headerExp : target.wordExp (shiftN .lsr (.load (realAddr conf (adjustVar a)))
                        (width - conf.lenSize)) = some (.word lengthWord) := by
                    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                      shiftN, realExp, headerRead, headerDomain, wordShiftHOL, offsetWord,
                      Nat.not_le_of_gt offsetBound, lengthEq]
                  have mask : w &&& 1 ≠ 0 := fun h => (StackAlloc.word_and_one_eq_0_iff w).mp h (by simp [low])
                  have test : wordSemWordCmp .test (.word w) (.word (1 : BitVec width)) = some false := by
                    simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
                    change (w &&& (1 : BitVec width) == 0) = false
                    exact beq_eq_false_iff_ne.mpr mask
                  refine ⟨smallLength, ?_⟩
                  simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                    operands.1, test, headerExp]
                  simp [s1, WordSemStateFiniteExact.setVar]
              have smallLength := firstFacts.1
              have boundsCmp := memoryRel_boundsCheck conf target.be (holThe source.tstamps) source.refs
                source.space target.store target.memory target.mdomain index indexWord (locals ++ envs) elements.length
                (by simpa [locals] using tail) smallLength good
              let rotated := indexWord.rotateRight 2
              let answer := decide (0 ≤ index ∧ index < Int.ofNat elements.length)
              let out : BitVec width := if answer then 18 else 2
              have rotRead : s1.getVar (adjustVar b) = some (.word indexWord) := by
                simpa [s1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                  sptLookup_sptInsert_ne, adjustVar] using operands.2
              have rotExp : s1.wordExp (shiftVar .ror (adjustVar b) 2) = some (.word rotated) := by
                rcases good with h | h <;> subst width <;>
                  simp [shiftVar, shiftN, WordSemStateFiniteExact.wordExp, rotRead,
                    wordShiftHOL, rotated]
              have fixed1 : target.fixClock ((none : Option (WordSemResult width)), s1) = (none, s1) := by
                simp [WordSemStateFiniteExact.fixClock, s1, WordSemStateFiniteExact.setVar]
              let s3 := s1.setVar 3 (.word rotated)
              have fixed3 : s1.fixClock ((none : Option (WordSemResult width)), s3) = (none, s3) := by
                simp [WordSemStateFiniteExact.fixClock, s3, WordSemStateFiniteExact.setVar]
              let final := s3.setVar (adjustVar dest) (.word out)
              have eval : WordSemStateFiniteExact.evaluate
                  (compileAssign conf n l dest (.blockOp .boundsCheckBlock) [a,b] none).1 target =
                  (none, final) := by
                dsimp only [s3] at fixed3
                simp only [compileAssign, arg2, assignBoundsCheckBlock, wordListSeq]
                rw [WordSemStateFiniteExact.evaluate]
                simp only [firstFacts.2, fixed1, WordSemStateFiniteExact.evaluate, rotExp, fixed3]
                change WordSemStateFiniteExact.evaluate
                  (setBool (adjustVar dest) .lower 3 (.reg 1)) s3 = (none, final)
                simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.setVar, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                  sptLookup_sptInsert_ne, sptLookup_sptInsert_same, s3, s1, final, out, answer,
                  rotated, lengthWord, boundsCmp]
                (split <;> simp_all); (split <;> simp_all [BitVec.lt_def, BitVec.le_def]); omega
              let next := DataSem.doStack (.blockOp .boundsCheckBlock)
                [.block stamp tag elements, .number index]
                (DataSem.doLimSafe source (.blockOp .boundsCheckBlock) [.block stamp tag elements, .number index])
              have nextRel : stateRel conf l1 l2 next target none locs :=
                stateRel_doStack conf l1 l2 _ target locs _ _
                  (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
              have s1Rel : stateRel conf l1 l2 next s1 none locs := by
                simpa [s1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using nextRel
              have s3Rel : stateRel conf l1 l2 next s3 none locs := by
                simpa [s3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using s1Rel
              let nextLocals := joinEnv next.locals (sptToAList (sptInter s3.locals (adjustSet next.locals)))
              let nextEnvs := [(theGlobal next.global, holFapply s3.store .globals)] ++ flatStack next.stack s3.stack
              have hmem := s3Rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              have boolRoot : memoryRel conf s3.be (holThe next.tstamps) next.refs next.space
                  s3.store s3.memory s3.mdomain
                  ((DataSem.boolValue answer, .word out) :: nextLocals ++ nextEnvs) := by
                apply memoryRel_bool conf s3.be (holThe next.tstamps) next.refs next.space
                  s3.store s3.memory s3.mdomain (nextLocals ++ nextEnvs) _ _
                refine ⟨?_, ?_, ?_, ?_⟩
                · simpa [nextLocals, nextEnvs] using hmem
                · simpa [s3, s1, WordSemStateFiniteExact.setVar] using good
                · intro h; simp [out, h]
                · intro h; simp [out, h]
              have updated := stateRel_insertRoot conf l1 l2 next s3 locs dest
                (DataSem.boolValue answer) (.word out) s3Rel (by simpa [nextLocals, nextEnvs] using boolRoot)
              refine ⟨none, final, eval, by simp, ?_⟩
              intro _
              exact ⟨by simpa [final, next, answer] using updated, rfl⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
