module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MemoryRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefArrayElement

@[expose] public section

/-! Fixed-index element reads in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace ElemAtAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ElemAtAssignmentWitness

/-- Invert the successful source element read in the HOL assignment proof. -/
private theorem elemAtSourceRun {C F : Type} (source resultState : DataSem.State C F)
    (k : Nat) (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp (.elemAt k)) values source = .val (result, resultState)) :
    ∃ base entries, ∃ h : k < entries.length,
      values = [base] ∧ result = entries[k] ∧
      resultState = DataSem.doStack (.blockOp (.elemAt k)) values
        (DataSem.doLimSafe source (.blockOp (.elemAt k)) values) ∧
      ((∃ stamp tag, base = .block stamp tag entries) ∨
        ∃ bit ptr, base = .refPtr bit ptr ∧ sptLookup ptr source.refs = some (.valueArray entries)) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | cons v vs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | nil =>
      cases v <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi]
      case block stamp tag entries =>
        by_cases bound : k < entries.length
        · simp [bound] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [bound]
        · simp [bound] at run
      case refPtr bit ptr =>
        have refsEq : (DataSem.doStack (.blockOp (.elemAt k)) [.refPtr bit ptr]
            (DataSem.doLimSafe source (.blockOp (.elemAt k)) [.refPtr bit ptr])).refs = source.refs := rfl
        rw [refsEq] at run
        cases found : sptLookup ptr source.refs with
        | none => simp [found] at run
        | some ref =>
          cases ref with
          | valueArray entries =>
            by_cases bound : k < entries.length
            · simp [found, bound] at run
              obtain ⟨rfl, rfl⟩ := run
              cases bit <;> simp [bound]
            · simp [found, bound] at run
          | _ => simp [found] at run

/-- Element lookup satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_ElemAt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignElemAt_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ k, op = .blockOp (.elemAt k))
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
  obtain ⟨k, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨base, entries, bound, valuesEq, resultEq, stateEq, shape⟩ :=
      elemAtSourceRun source resultState k values result run
    subst values
    subst result
    subst resultState
    have argLen : args.length = 1 := by
      have h := DataSpace.getVars_length args source.locals [base] argsEq
      simpa using h.symm
    cases args with
    | nil => simp at argLen
    | cons a args =>
      cases args with
      | cons b rest => simp at argLen
      | nil =>
        obtain ⟨words, getWords, lengthEq⟩ :=
          stateRel_getVars conf l1 l2 source target locs [a] [base] related argsEq
        cases words with
        | nil => simp at lengthEq
        | cons word words =>
          cases words with
          | cons extra rest => simp at lengthEq
          | nil =>
            let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
              flatStack source.stack target.stack
            let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
            have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
              target.store target.memory target.mdomain target envs [a] [base] [word] (by
                refine ⟨?_, argsEq, getWords⟩
                simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            have good := related.2.2.2.2.2.2.1
            have element : ∃ w address : BitVec width,
                word = .word w ∧ getRealAddr conf target.store w = some address ∧
                target.mdomain (address + StackRemove.bytesInWord width +
                  StackRemove.bytesInWord width * BitVec.ofNat width k) = true ∧
                memoryRel conf target.be (holThe source.tstamps) source.refs source.space target.store
                  target.memory target.mdomain ((entries[k], target.memory (address + StackRemove.bytesInWord width +
                    StackRemove.bytesInWord width * BitVec.ofNat width k)) :: (base, word) :: locals ++ envs) := by
              rcases shape with ⟨stamp, tag, rfl⟩ | ⟨bit, ptr, rfl, found⟩
              · obtain ⟨w, address, _, eqWord, eqAddr, domain, extended⟩ :=
                  memoryRel_elAny conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain stamp tag entries word (locals ++ envs) k bound
                    ⟨by simpa [locals] using roots, good⟩
                exact ⟨w, address, eqWord, eqAddr, domain, extended⟩
              · exact memoryRel_deref conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain bit ptr entries word (locals ++ envs) k
                  ⟨by simpa [locals] using roots, found, good, bound⟩
            obtain ⟨w, address, rfl, real, domain, extended⟩ := element
            have read : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word w) := by
              cases h : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                simp_all [WordSemStateFiniteExact.getVars]
            let next := DataSem.doStack (.blockOp (.elemAt k)) [base]
              (DataSem.doLimSafe source (.blockOp (.elemAt k)) [base])
            have nextRel : stateRel conf l1 l2 next target none locs :=
              stateRel_doStack conf l1 l2 _ target locs _ _
                (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
            let loaded := target.memory (address + StackRemove.bytesInWord width +
              StackRemove.bytesInWord width * BitVec.ofNat width k)
            have newRoot : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                target.store target.memory target.mdomain ((entries[k], loaded) :: locals ++ envs) := by
              apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                target.store target.memory target.mdomain _ _ ?_ extended
              intro pair member
              simp only [List.mem_cons, List.mem_append] at member ⊢
              simp only [loaded] at member
              tauto
            have updated := stateRel_insertRoot conf l1 l2 next target locs dest entries[k] loaded nextRel (by
              simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs] using newRoot)
            have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target w address
              ⟨related.2.2.2.2.2.2.2.1, good, read, real⟩
            have domain' : target.mdomain (address + (wordSemBytesInWord +
                wordSemBytesInWord * BitVec.ofNat width k)) = true := by
              simpa [StackRemove.bytesInWord, wordSemBytesInWord, BitVec.add_assoc] using domain
            simp only [wordSemBytesInWord] at domain'
            refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) loaded target, ?_, ?_, ?_⟩
            · simp [compileAssign, arg1, assignElemAt, WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                realExp, domain', loaded, wordSemBytesInWord,
                StackRemove.bytesInWord, theWords, wordOpHOL, wordOp, BitVec.add_assoc]
            · simp
            · simpa [next] using updated

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
