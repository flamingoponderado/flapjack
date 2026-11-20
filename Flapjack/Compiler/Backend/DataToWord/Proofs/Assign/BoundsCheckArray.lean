module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.DerefByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BoundsCheck
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ValueArray


@[expose] public section

/-! Value-array bounds checks in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Extract the successful source operation used by the bounds-check simulation. -/
private theorem boundsArraySourceRun {C F : Type}
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .boundsCheckArray) values source = .val (result, resultState)) :
    ∃ bit ptr index elements,
      values = [.refPtr bit ptr, .number index] ∧
      sptLookup ptr source.refs = some (.valueArray elements) ∧
      result = DataSem.boolValue (decide (0 ≤ index ∧ index < Int.ofNat elements.length)) ∧
      resultState = DataSem.doStack (.memOp .boundsCheckArray) values
        (DataSem.doLimSafe source (.memOp .boundsCheckArray) values) := by
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
        rename_i bit ptr index
        have refsEq : (DataSem.doStack (.memOp .boundsCheckArray)
            [.refPtr bit ptr, .number index]
            (DataSem.doLimSafe source (.memOp .boundsCheckArray) [.refPtr bit ptr, .number index])).refs = source.refs := rfl
        rw [refsEq] at run
        cases found : sptLookup ptr source.refs with
        | none => simp [found] at run
        | some ref =>
          cases ref with
          | valueArray elements =>
            simp [found] at run
            obtain ⟨rfl, rfl⟩ := run
            simp_all
          | _ => simp [found] at run

namespace BoundsArrayAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end BoundsArrayAssignmentWitness

/-- Compiler equation for a value-array bounds check. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_BoundsCheckArray" 11289
  (words_as_type_indexed_bitvec)]
theorem assignBoundsCheckArrayEquation {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (sec l dest : Nat)
    (args : List Nat) (names : Option NumSet) :
    (compileAssign conf sec l dest (.memOp .boundsCheckArray) args names :
      WordLangProgHOL (BitVec width) × Nat) =
      match args with
      | [base, index] =>
          (wordListSeq [
            .assign 1 (shiftN .lsr (.load (realAddr conf (adjustVar base))) (width - conf.lenSize)),
            .assign 3 (shiftVar .ror (adjustVar index) 2),
            setBool (adjustVar dest) .lower 3 (.reg 1)], l)
      | _ => (.skip, l) := by
  cases args with
  | nil => rfl
  | cons x xs => cases xs with
    | nil => rfl
    | cons y ys => cases ys <;> rfl

/-- Value-array bounds checks satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_BoundsCheckArray" 11306
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignBoundsCheckArray_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .boundsCheckArray)
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
  obtain ⟨bit, ptr, index, elements, valuesEq, found, resultEq, stateEq⟩ :=
    boundsArraySourceRun source resultState values result run
  subst values
  subst result
  subst resultState
  have argLen : args.length = 2 := by
    have h := DataSpace.getVars_length args source.locals [.refPtr bit ptr, .number index] argsEq
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
          stateRel_getVars conf l1 l2 source target locs [a,b] [.refPtr bit ptr, .number index] related argsEq
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
                [.refPtr bit ptr, .number index] [word1,word2] (by
                  refine ⟨?_, argsEq, getWords⟩
                  simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
              have good := related.2.2.2.2.2.2.1
              obtain ⟨w, address, header, wordEq, low, _, _, _, _, real,
                headerRead, headerDomain, headerLength, sizeBound⟩ :=
                memoryRel_valueArrayImp conf target.be (holThe source.tstamps) source.refs
                  source.space target.store target.memory target.mdomain bit ptr elements word1
                  ((.number index, word2) :: locals ++ envs) ⟨by simpa [locals] using roots, found, good⟩
              have tail := memoryRel_tail conf target.be (holThe source.tstamps) source.refs source.space
                target.store target.memory target.mdomain (.refPtr bit ptr, word1)
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
              have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
                ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
              have smallLength : smallInt width (Int.ofNat elements.length) := by
                rcases good with hw | hw <;> subst width <;> simp [smallInt] at sizeBound ⊢ <;> omega
              have boundsCmp := memoryRel_boundsCheck conf target.be (holThe source.tstamps) source.refs
                source.space target.store target.memory target.mdomain index indexWord (locals ++ envs) elements.length
                (by simpa [locals] using tail) smallLength good
              let lengthWord : BitVec width := BitVec.ofNat width elements.length
              have lengthEq : header >>> (width - conf.lenSize) = lengthWord := by
                simpa [WordGcFunctions.decodeLength, lengthWord] using headerLength
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
              let rotated := indexWord.rotateRight 2
              let answer := decide (0 ≤ index ∧ index < Int.ofNat elements.length)
              let out : BitVec width := if answer then 18 else 2
              let s1 := target.setVar 1 (.word lengthWord)
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
                  (compileAssign conf n l dest (.memOp .boundsCheckArray) [a,b] none).1 target =
                  (none, final) := by
                dsimp only [s1] at fixed1 rotExp
                dsimp only [s1, s3] at fixed3
                simp only [compileAssign, arg2, assignBoundsCheckArray, wordListSeq]
                simp only [WordSemStateFiniteExact.evaluate, headerExp, fixed1, rotExp, fixed3]
                change WordSemStateFiniteExact.evaluate
                  (setBool (adjustVar dest) .lower 3 (.reg 1)) s3 = (none, final)
                simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.setVar, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                  sptLookup_sptInsert_ne, sptLookup_sptInsert_same, s3, s1, final, out, answer,
                  rotated, lengthWord, boundsCmp]
                (split <;> simp_all); (split <;> simp_all [BitVec.lt_def, BitVec.le_def]); omega
              let next := DataSem.doStack (.memOp .boundsCheckArray)
                [.refPtr bit ptr, .number index]
                (DataSem.doLimSafe source (.memOp .boundsCheckArray) [.refPtr bit ptr, .number index])
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
