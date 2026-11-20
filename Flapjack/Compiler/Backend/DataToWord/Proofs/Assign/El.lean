module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.ElemAt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Offset

@[expose] public section

/-! Dynamic element reads in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace ElAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ElAssignmentWitness

/-- Invert the successful dynamic element read in the HOL assignment proof. -/
private theorem elSourceRun {C F : Type} (source resultState : DataSem.State C F)
    (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .el) values source = .val (result, resultState)) :
    ∃ base index entries, ∃ h : index.toNat < entries.length,
      values = [base, .number index] ∧ 0 ≤ index ∧ result = entries[index.toNat] ∧
      resultState = DataSem.doStack (.memOp .el) values
        (DataSem.doLimSafe source (.memOp .el) values) ∧
      ((∃ stamp tag, base = .block stamp tag entries) ∨
        ∃ bit ptr, base = .refPtr bit ptr ∧ sptLookup ptr source.refs = some (.valueArray entries)) := by
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
        case block.number stamp tag entries index =>
          by_cases negative : index < 0
          · simp [negative] at run
          · by_cases bound : index.toNat < entries.length
            · simp [negative, bound] at run
              obtain ⟨rfl, rfl⟩ := run
              simp [Int.not_lt.mp negative, bound]
            · simp [negative, bound] at run
        case refPtr.number bit ptr index =>
          have refsEq : (DataSem.doStack (.memOp .el) [.refPtr bit ptr, .number index]
              (DataSem.doLimSafe source (.memOp .el) [.refPtr bit ptr, .number index])).refs = source.refs := rfl
          rw [refsEq] at run
          cases found : sptLookup ptr source.refs with
          | none => simp [found] at run
          | some ref =>
            cases ref with
            | valueArray entries =>
              by_cases negative : index < 0
              · simp [found, negative] at run
              · by_cases bound : index.toNat < entries.length
                · simp [found, negative, bound] at run
                  obtain ⟨rfl, rfl⟩ := run
                  cases bit <;> simp [Int.not_lt.mp negative] <;> omega
                · simp [found, negative, bound] at run
            | _ => simp [found] at run

/-- Dynamic element lookup satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_El"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignEl_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .el)
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
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨base, index, entries, bound, valuesEq, nonneg, resultEq, stateEq, shape⟩ :=
      elSourceRun source resultState values result run
    subst values
    subst result
    subst resultState
    have indexNat : Int.ofNat index.toNat = index := Int.toNat_of_nonneg nonneg
    have argLen : args.length = 2 := by
      have h := DataSpace.getVars_length args source.locals [base, .number index] argsEq
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
            stateRel_getVars conf l1 l2 source target locs [a,b] [base, .number index] related argsEq
          cases words with
          | nil => simp at lengthEq
          | cons word1 words =>
            cases words with
            | nil => simp at lengthEq
            | cons word2 words =>
              cases words with
              | cons extra rest => simp at lengthEq
              | nil =>
                let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                  flatStack source.stack target.stack
                let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                  target.store target.memory target.mdomain target envs [a,b] [base, .number index] [word1,word2] (by
                    refine ⟨?_, argsEq, getWords⟩
                    simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                have good := related.2.2.2.2.2.2.1
                have element : ∃ ptrWord indexWord addr offset : BitVec width,
                    word1 = .word ptrWord ∧ word2 = .word indexWord ∧
                    getRealAddr conf target.store ptrWord = some addr ∧ getRealOffset indexWord = some offset ∧
                    target.mdomain (addr + offset) = true ∧
                    memoryRel conf target.be (holThe source.tstamps) source.refs source.space target.store
                      target.memory target.mdomain ((entries[index.toNat], target.memory (addr + offset)) ::
                        (base, word1) :: (.number index, word2) :: locals ++ envs) := by
                  rcases shape with ⟨stamp, tag, rfl⟩ | ⟨bit, ptr, rfl, found⟩
                  · have fact := memoryRel_elIndex conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain stamp tag entries word1 word2 (locals ++ envs) index.toNat
                      ⟨by simpa [locals, indexNat, max_eq_left nonneg] using roots, good, bound⟩
                    simpa [indexNat, max_eq_left nonneg] using fact
                  · have fact := memoryRel_derefIndex conf target.be (holThe source.tstamps) source.refs source.space
                      target.store target.memory target.mdomain bit ptr entries word1 word2 (locals ++ envs) index.toNat
                      ⟨by simpa [locals, indexNat, max_eq_left nonneg] using roots, found, good, bound⟩
                    simpa [indexNat, max_eq_left nonneg] using fact
                obtain ⟨ptrWord, indexWord, addr, offset, rfl, rfl, real, realOffsetEq, domain, extended⟩ := element
                have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word ptrWord) ∧
                    WordSemStateFiniteExact.getVar (adjustVar b) target = some (.word indexWord) := by
                  cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                    cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
                    simp_all [WordSemStateFiniteExact.getVars]
                let next := DataSem.doStack (.memOp .el) [base, .number index]
                  (DataSem.doLimSafe source (.memOp .el) [base, .number index])
                have nextRel : stateRel conf l1 l2 next target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                let loaded := target.memory (addr + offset)
                have newRoot : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain ((entries[index.toNat], loaded) :: locals ++ envs) := by
                  apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain _ _ ?_ extended
                  intro pair member
                  simp only [List.mem_cons, List.mem_append] at member ⊢
                  simp only [loaded] at member
                  tauto
                have updated := stateRel_insertRoot conf l1 l2 next target locs dest entries[index.toNat]
                  loaded nextRel (by simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs] using newRoot)
                have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target ptrWord addr
                  ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
                have offsetExp := getRealOffset_lemma (adjustVar b) target indexWord offset conf
                  ⟨operands.2, good, realOffsetEq⟩
                refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) loaded target, ?_, ?_, ?_⟩
                · simp [compileAssign, arg2, assignEl, WordSemStateFiniteExact.evaluate,
                    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                    realExp, offsetExp, domain, loaded, theWords, wordOpHOL, wordOp]
                · simp
                · simpa [next] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
