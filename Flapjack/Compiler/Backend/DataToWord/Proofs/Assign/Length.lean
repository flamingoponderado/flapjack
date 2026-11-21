module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoundsCheckArray

@[expose] public section

/-! Value-array lengths in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Extract the successful source operation used by the array-length simulation. -/
private theorem lengthSourceRun {C F : Type}
    (source resultState : DataSem.State C F) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .length) values source = .val (result, resultState)) :
    ∃ bit ptr elements,
      values = [.refPtr bit ptr] ∧
      sptLookup ptr source.refs = some (.valueArray elements) ∧
      result = .number (Int.ofNat elements.length) ∧
      resultState = DataSem.doStack (.memOp .length) values
        (DataSem.doLimSafe source (.memOp .length) values) := by
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
      rename_i bit ptr
      have refsEq : (DataSem.doStack (.memOp .length) [.refPtr bit ptr]
          (DataSem.doLimSafe source (.memOp .length) [.refPtr bit ptr])).refs = source.refs := rfl
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

namespace LengthAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LengthAssignmentWitness

/-- Value-array lengths satisfy the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Length"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLength_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .length)
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
  obtain ⟨bit, ptr, elements, valuesEq, found, resultEq, stateEq⟩ :=
    lengthSourceRun source resultState values result run
  subst values
  subst result
  subst resultState
  have argLen : args.length = 1 := by
    have h := DataSpace.getVars_length args source.locals [.refPtr bit ptr] argsEq
    simpa using h.symm
  cases args with
  | nil => simp at argLen
  | cons a args =>
    cases args with
    | cons b rest => simp at argLen
    | nil =>
      obtain ⟨words, getWords, lengthEq⟩ :=
        stateRel_getVars conf l1 l2 source target locs [a] [.refPtr bit ptr] related argsEq
      cases words with
      | nil => simp at lengthEq
      | cons word1 words =>
        cases words with
        | cons word2 rest => simp at lengthEq
        | nil =>
          let envs := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
          let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
          have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
            target.store target.memory target.mdomain target envs [a]
            [.refPtr bit ptr] [word1] (by
              refine ⟨?_, argsEq, getWords⟩
              simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
          have good := related.2.2.2.2.2.2.1
          obtain ⟨w, address, header, wordEq, _, _, _, _, _, real,
            headerRead, headerDomain, headerLength, sizeBound⟩ :=
            memoryRel_valueArrayImp conf target.be (holThe source.tstamps) source.refs
              source.space target.store target.memory target.mdomain bit ptr elements word1
              (locals ++ envs) ⟨by simpa [locals] using roots, found, good⟩
          subst word1
          have operand : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) := by
            cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
              simp_all [WordSemStateFiniteExact.getVars]
          let lenInt : Int := Int.ofNat elements.length
          let final := target.setVar (adjustVar dest) (.word (smallnum lenInt : BitVec width))
          have smallLength : smallInt width lenInt := by
            rcases good with h | h <;> subst width <;> simp [smallInt, lenInt] at sizeBound ⊢ <;> omega
          let lengthWord : BitVec width := BitVec.ofNat width elements.length
          have lengthEq : header >>> (width - conf.lenSize) = lengthWord := by
            simpa [WordGcFunctions.decodeLength, lengthWord] using headerLength
          have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
            ⟨related.2.2.2.2.2.2.2.1, good, operand, real⟩
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
          have shifted : lengthWord <<< (2 : Nat) = (smallnum lenInt : BitVec width) := by
            have small : (smallnum lenInt : BitVec width) = BitVec.ofNat width (elements.length * 4) := by
              unfold smallnum; rw [if_neg (by simp [lenInt])]; congr 1; simp [lenInt]; omega
            rw [small]
            apply BitVec.eq_of_toNat_eq
            simp [lengthWord, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod]
          have valueExp : target.wordExp (shiftN .lsl (shiftN .lsr (.load (realAddr conf (adjustVar a)))
                (width - conf.lenSize)) 2) = some (.word (smallnum lenInt)) := by
            rcases good with h | h <;> subst width <;>
            simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
              shiftN, realExp, headerRead, headerDomain, wordShiftHOL, offsetWord,
              Nat.not_le_of_gt offsetBound, lengthEq] <;> exact shifted
          have eval : WordSemStateFiniteExact.evaluate
              (compileAssign conf n l dest (.memOp .length) [a] none).1 target = (none, final) := by
            simp only [compileAssign, arg1, assignLength]
            simp only [WordSemStateFiniteExact.evaluate, valueExp]
            simp [final, WordSemStateFiniteExact.setVar]
          let next := DataSem.doStack (.memOp .length) [.refPtr bit ptr]
            (DataSem.doLimSafe source (.memOp .length) [.refPtr bit ptr])
          have nextRel : stateRel conf l1 l2 next target none locs :=
            stateRel_doStack conf l1 l2 _ target locs _ _
              (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
          let nextLocals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
          let nextEnvs := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
          have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          have numberRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain
              ((.number lenInt, .word (smallnum lenInt)) :: nextLocals ++ nextEnvs) := by
            apply impMemoryRel_number conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain (nextLocals ++ nextEnvs) _
            exact ⟨good, smallLength, by simpa [nextLocals, nextEnvs] using hmem⟩
          have updated := stateRel_insertRoot conf l1 l2 next target locs dest
            (.number lenInt) (.word (smallnum lenInt)) nextRel
            (by simpa [nextLocals, nextEnvs] using numberRoot)
          refine ⟨none, final, eval, by simp, ?_⟩
          intro _
          exact ⟨by simpa [final, next, lenInt] using updated, rfl⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
