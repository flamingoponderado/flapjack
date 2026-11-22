module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.UpdateByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Offset
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.UpdateCons

@[expose] public section

/-! Mutable-constructor hole updates in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace UpdateConsAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end UpdateConsAssignmentWitness

/-- Invert a successful source hole update of a mutable constructor; untagged proof
infrastructure for `assign_UpdateCons`. -/
private theorem updateConsSourceRun {C F : Type} (source resultState : DataSem.State C F)
    (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.memOp .updateCons) values source = .val (result, resultState)) :
    ∃ bit ptr value tag left old right,
      values = [.refPtr bit ptr, .number (Int.ofNat left.length), value] ∧
      sptLookup ptr source.refs = some (.mutBlock tag false left old right) ∧
      result = DataSem.unitValue ∧
      resultState = { (DataSem.doStack (.memOp .updateCons) values
        (DataSem.doLimSafe source (.memOp .updateCons) values)) with
        refs := sptInsert ptr (.mutBlock tag false left value right) source.refs } := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons w ws =>
      cases ws with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | cons x xs =>
        cases xs with
        | cons y ys => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | nil =>
          cases v <;> cases w <;>
            simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi]
          rename_i bit ptr index
          have refsEq : (DataSem.doStack (.memOp .updateCons) [.refPtr bit ptr, .number index, x]
              (DataSem.doLimSafe source (.memOp .updateCons) [.refPtr bit ptr, .number index, x])).refs =
              source.refs := rfl
          rw [refsEq] at run
          cases found : sptLookup ptr source.refs with
          | none => simp [found] at run
          | some ref =>
            cases ref with
            | mutBlock tag finalised left old right =>
              by_cases bad : index ≠ Int.ofNat left.length ∨ finalised = true
              · rcases bad with bad | bad <;> simp_all
              · simp only [not_or, ne_eq, Decidable.not_not, Bool.not_eq_true] at bad
                obtain ⟨rfl, rfl⟩ := bad
                simp [found] at run
                obtain ⟨rfl, rfl⟩ := run
                simp_all
            | _ => simp [found] at run

/-- Mutable-constructor hole update satisfies the original data-to-word assignment goal.
The evaluator inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_UpdateCons"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignUpdateCons_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .memOp .updateCons)
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
    obtain ⟨bit, ptr, value, tag, left, old, right, valuesEq, found, resultEq, stateEq⟩ :=
      updateConsSourceRun source resultState values result run
    subst values
    subst result
    subst resultState
    have argLen : args.length = 3 := by
      have h := DataSpace.getVars_length args source.locals [.refPtr bit ptr, .number (Int.ofNat left.length), value] argsEq
      simpa using h.symm
    cases args with
    | nil => simp at argLen
    | cons a args =>
      cases args with
      | nil => simp at argLen
      | cons b args =>
        cases args with
        | nil => simp at argLen
        | cons c args =>
          cases args with
          | cons d rest => simp at argLen
          | nil =>
            obtain ⟨words, getWords, lengthEq⟩ :=
              stateRel_getVars conf l1 l2 source target locs [a,b,c]
                [.refPtr bit ptr, .number (Int.ofNat left.length), value] related argsEq
            cases words with
            | nil => simp at lengthEq
            | cons word1 words =>
              cases words with
              | nil => simp at lengthEq
              | cons word2 words =>
                cases words with
                | nil => simp at lengthEq
                | cons word3 words =>
                  cases words with
                  | cons word4 rest => simp at lengthEq
                  | nil =>
                    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                      flatStack source.stack target.stack
                    let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                      target.store target.memory target.mdomain target envs [a,b,c]
                      [.refPtr bit ptr, .number (Int.ofNat left.length), value] [word1,word2,word3] (by
                        refine ⟨?_, argsEq, getWords⟩
                        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                    have good := related.2.2.2.2.2.2.1
                    have ordered : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                        target.store target.memory target.mdomain
                        ((value, word3) :: (.refPtr bit ptr, word1) :: (.number (Int.ofNat left.length), word2) :: locals ++ envs) := by
                      apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
                        target.store target.memory target.mdomain _ _ ?_ (by simpa [locals] using roots)
                      intro pair member
                      simp only [locals, List.mem_cons, List.mem_append] at member ⊢
                      tauto
                    have updateFact := memoryRel_updateCons conf target.be (holThe source.tstamps) source.refs
                      source.space target.store target.memory target.mdomain value word3 bit ptr word1 left.length
                      word2 (locals ++ envs) tag left old right ⟨by simpa using ordered, found, good, rfl⟩
                    obtain ⟨ptrWord, indexWord, addr, offset, rfl, rfl, real, realOffsetEq, domain, updatedHeap⟩ := updateFact
                    have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some (.word ptrWord) ∧
                        WordSemStateFiniteExact.getVar (adjustVar b) target = some (.word indexWord) ∧
                        WordSemStateFiniteExact.getVar (adjustVar c) target = some word3 := by
                      cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
                        cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
                        cases h3 : WordSemStateFiniteExact.getVar (adjustVar c) target <;>
                        simp_all [WordSemStateFiniteExact.getVars]
                    let refs := sptInsert ptr (.mutBlock tag false left value right) source.refs
                    let mem := fun key => if key = addr + offset then word3 else target.memory key
                    have baseHeap : memoryRel conf target.be (holThe source.tstamps) refs source.space
                        target.store mem target.mdomain (locals ++ envs) := by
                      apply memoryRel_rearrange conf target.be (holThe source.tstamps) refs source.space
                        target.store mem target.mdomain _ _ ?_ (by simpa [refs, mem] using updatedHeap)
                      intro pair member
                      simp only [List.mem_cons, List.mem_append] at member ⊢
                      tauto
                    let next := DataSem.doStack (.memOp .updateCons) [.refPtr bit ptr, .number (Int.ofNat left.length), value]
                      (DataSem.doLimSafe source (.memOp .updateCons) [.refPtr bit ptr, .number (Int.ofNat left.length), value])
                    have nextRel : stateRel conf l1 l2 next target none locs :=
                      stateRel_doStack conf l1 l2 _ target locs _ _
                        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                    let midSource := {next with refs := refs}
                    let midTarget := {target with memory := mem}
                    have midRel : stateRel conf l1 l2 midSource midTarget none locs :=
                      stateRel_replaceMemory conf l1 l2 next target locs refs mem nextRel (by
                        simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs] using baseHeap)
                    have unitRoot := memoryRel_unit conf target.be (holThe source.tstamps) refs source.space
                      target.store mem target.mdomain (locals ++ envs) ⟨baseHeap, good⟩
                    have finalRel := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest DataSem.unitValue
                      (.word 2) midRel (by simpa [midSource, midTarget, next, DataSem.doStack,
                        DataSem.doLimSafe, locals, envs] using unitRoot)
                    have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target ptrWord addr
                      ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
                    have offsetExp := getRealOffset_lemma (adjustVar b) target indexWord offset conf
                      ⟨operands.2.1, good, realOffsetEq⟩
                    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) midTarget, ?_, ?_, ?_⟩
                    · simp [compileAssign, arg3, assignUpdate, unitExp, WordSemStateFiniteExact.evaluate,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memStore,
                        WordSemStateFiniteExact.fixClock, realExp, offsetExp, operands.2.2,
                        domain, midTarget, mem, theWords, wordOpHOL, wordOp]
                    · simp
                    · simpa [midSource, refs, next, DataSem.doStack, DataSem.doLimSafe] using finalRel

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
