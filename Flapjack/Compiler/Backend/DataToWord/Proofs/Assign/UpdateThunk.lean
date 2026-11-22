module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.UpdateByte
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Offset
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SetGlobal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.UpdateThunk

@[expose] public section

/-! Thunk updates in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace UpdateThunkAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end UpdateThunkAssignmentWitness

open Classical in
/-- Invert a successful source thunk update; local proof infrastructure for
`assign_UpdateThunk`. -/
private theorem updateThunkSourceRun {C F : Type} (mode : AstHOL.ThunkMode)
    (source resultState : DataSem.State C F)
    (values : List DataSem.Value) (result : DataSem.Value)
    (run : DataSem.doApp (.thunkOp (.updateThunk mode)) values source = .val (result, resultState)) :
    ∃ ptr value old,
      values = [.refPtr false ptr, value] ∧ ¬ DataSem.badThunkUpdate mode value source.refs ∧
      sptLookup ptr source.refs = some (.thunk .notEvaluated old) ∧ result = DataSem.unitValue ∧
      resultState = { (DataSem.doStack (.thunkOp (.updateThunk mode)) values
        (DataSem.doLimSafe source (.thunkOp (.updateThunk mode)) values)) with
        refs := sptInsert ptr (.thunk mode value) source.refs } := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons v vs =>
    cases vs with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons x xs =>
      cases xs with
      | cons y ys => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | nil =>
        cases v with
        | refPtr bit ptr =>
          cases bit with
          | true => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi] at run
          | false =>
            simp only [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi] at run
            have refsEq : (DataSem.doStack (.thunkOp (.updateThunk mode)) [.refPtr false ptr, x]
                (DataSem.doLimSafe source (.thunkOp (.updateThunk mode)) [.refPtr false ptr, x])).refs =
                source.refs := rfl
            by_cases bad : DataSem.badThunkUpdate mode x source.refs
            · simp [refsEq, bad] at run
            · cases found : sptLookup ptr source.refs with
              | none => simp [refsEq, bad, found] at run
              | some ref =>
                cases ref with
                | thunk m old =>
                  cases m with
                  | notEvaluated =>
                    simp [refsEq, bad, found] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact ⟨ptr, x, old, rfl, bad, found, rfl, rfl⟩
                  | evaluated => simp [refsEq, bad, found] at run
                | _ => simp [refsEq, bad, found] at run
        | _ => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run

/-- The evaluated-thunk header is always encodable under the state relation; local
proof infrastructure for `assign_UpdateThunk`. -/
private theorem thunkHeaderSome {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    ∃ hd, encodeHeader (width := width) conf (8 + 6) 1 = some hd := by
  have good := related.2.2.2.2.2.2.1
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have lenPos : 0 < conf.lenSize := by
    have h := heapMem.2.2.2.1
    omega
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have countBound : 1 < 2 ^ conf.lenSize := by
    have h : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rcases good with h | h <;> subst width
  · refine ⟨makeHeader conf (BitVec.ofNat 32 14) 1, ?_⟩
    simp [encodeHeader, countBound, show 14 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · refine ⟨makeHeader conf (BitVec.ofNat 64 14) 1, ?_⟩
    simp [encodeHeader, countBound, show 14 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 4 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]

/-- Thunk update satisfies the original data-to-word assignment goal. The evaluator
inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_UpdateThunk"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignUpdateThunk_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ ev, op = .thunkOp (.updateThunk ev))
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
  obtain ⟨mode, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨ptr, value, old, valuesEq, notBad, found, resultEq, stateEq⟩ :=
      updateThunkSourceRun mode source resultState values result run
    subst values result resultState
    have argLen : args.length = 2 := by
      have h := DataSpace.getVars_length args source.locals [.refPtr false ptr, value] argsEq
      simpa using h.symm
    obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := by
      match args, argLen with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨words, getWords, lengthEq⟩ :=
      stateRel_getVars conf l1 l2 source target locs [a, b] [.refPtr false ptr, value] related argsEq
    obtain ⟨word1, word2, rfl⟩ : ∃ w1 w2, words = [w1, w2] := by
      match words, lengthEq with
      | [w1, w2], _ => exact ⟨w1, w2, rfl⟩
    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
      flatStack source.stack target.stack
    let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
      target.store target.memory target.mdomain target envs [a, b]
      [.refPtr false ptr, value] [word1, word2] (by
        refine ⟨?_, argsEq, getWords⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    have good := related.2.2.2.2.2.2.1
    have ordered : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain
        ((value, word2) :: (.refPtr false ptr, word1) :: locals ++ envs) := by
      apply memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
        target.store target.memory target.mdomain _ _ ?_ (by simpa [locals] using roots)
      intro pair member
      simp only [locals, List.mem_cons, List.mem_append] at member ⊢
      tauto
    have operands : WordSemStateFiniteExact.getVar (adjustVar a) target = some word1 ∧
        WordSemStateFiniteExact.getVar (adjustVar b) target = some word2 := by
      cases h1 : WordSemStateFiniteExact.getVar (adjustVar a) target <;>
        cases h2 : WordSemStateFiniteExact.getVar (adjustVar b) target <;>
        simp_all [WordSemStateFiniteExact.getVars]
    let next := DataSem.doStack (.thunkOp (.updateThunk mode)) [.refPtr false ptr, value]
      (DataSem.doLimSafe source (.thunkOp (.updateThunk mode)) [.refPtr false ptr, value])
    have nextRel : stateRel conf l1 l2 next target none locs :=
      stateRel_doStack conf l1 l2 _ target locs _ _
        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
    let refs := sptInsert ptr (.thunk mode value) source.refs
    -- Common completion once the memory has been updated.
    have finish : ∀ (mem : BitVec width → WordLocW width) (t2 : WordSemStateFiniteExact width C F),
        memoryRel conf target.be (holThe source.tstamps) refs source.space target.store mem
          target.mdomain ((value, word2) :: (.refPtr false ptr, word1) :: locals ++ envs) →
        stateRel conf l1 l2 {next with refs := refs} t2 none locs =
          stateRel conf l1 l2 {next with refs := refs} {target with memory := mem} none locs →
        stateRel conf l1 l2 (DataSem.setVar dest DataSem.unitValue {next with refs := refs})
          (WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) t2) none locs ∧ True := by
      intro mem t2 updatedHeap relEq
      have baseHeap : memoryRel conf target.be (holThe source.tstamps) refs source.space
          target.store mem target.mdomain (locals ++ envs) := by
        apply memoryRel_rearrange conf target.be (holThe source.tstamps) refs source.space
          target.store mem target.mdomain _ _ ?_ updatedHeap
        intro pair member
        simp only [List.mem_cons, List.mem_append] at member ⊢
        tauto
      have midRel : stateRel conf l1 l2 {next with refs := refs} {target with memory := mem} none locs :=
        stateRel_replaceMemory conf l1 l2 next target locs refs mem nextRel (by
          simpa [next, DataSem.doStack, DataSem.doLimSafe, locals, envs] using baseHeap)
      have midRel2 : stateRel conf l1 l2 {next with refs := refs} t2 none locs := relEq ▸ midRel
      have unitRoot := memoryRel_unit conf t2.be (holThe source.tstamps) refs source.space t2.store
        t2.memory t2.mdomain _ ⟨midRel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, good⟩
      exact ⟨stateRel_insertRoot conf l1 l2 {next with refs := refs} t2 locs dest DataSem.unitValue
        (.word 2) midRel2 (by simpa [List.append_assoc, next, DataSem.doStack, DataSem.doLimSafe]
          using unitRoot), trivial⟩
    cases mode with
    | notEvaluated =>
      obtain ⟨ptrW, x, rfl, real, dom, updatedHeap⟩ := memoryRel_updateThunk_notEvaluated conf target.be
        (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain value word2
        ptr word1 (locals ++ envs) old ⟨by simpa using ordered, found, good⟩
      let mem := fun key => if key = x + StackRemove.bytesInWord width then word2 else target.memory key
      have dom' : target.mdomain (x + BitVec.ofNat width (width / 8)) = true := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using dom
      have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target ptrW x
        ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
      obtain ⟨relFinal, -⟩ := finish mem {target with memory := mem}
        (by simpa [refs, mem] using updatedHeap) rfl
      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) {target with memory := mem},
        ?_, by simp, fun _ => ⟨by simpa [next, refs] using relFinal, rfl⟩⟩
      simp [compileAssign, arg2, assignUpdateThunk, unitExp, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memStore,
        WordSemStateFiniteExact.fixClock, realExp, operands.2, mem, theWords, wordOpHOL, wordOp,
        StackRemove.bytesInWord, wordSemBytesInWord, WordSemStateFiniteExact.setVar, dom']
      all_goals rfl
    | evaluated =>
      obtain ⟨hd, hdEq⟩ := thunkHeaderSome conf source target l1 l2 locs related
      have notThunk : DataSem.destThunk value source.refs = .notThunk := by
        by_contra hne
        exact notBad ⟨rfl, hne⟩
      obtain ⟨ptrW, x, rfl, real, dom0, dom1, updatedHeap⟩ := memoryRel_updateThunk_evaluated conf target.be
        (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain value word2
        ptr word1 (locals ++ envs) old hd ⟨by simpa using ordered, found, hdEq, notThunk, good⟩
      let mem : BitVec width → WordLocW width := fun key =>
        if key = x + StackRemove.bytesInWord width then word2
        else if key = x then .word hd else target.memory key
      have memEq : Misc.UpdateList.updateList target.memory
          [(x, .word hd), (x + StackRemove.bytesInWord width, word2)] = mem := by
        funext key
        simp [Misc.UpdateList.updateList, mem, eq_comm]
      let t2 : WordSemStateFiniteExact width C F :=
        {target with memory := mem, locals := sptInsert 3 (.word hd) (sptInsert 1 (.word x) target.locals)}
      have realExp := Bignum.getRealAddr_lemma conf (adjustVar a) target ptrW x
        ⟨related.2.2.2.2.2.2.2.1, good, operands.1, real⟩
      obtain ⟨relFinal, -⟩ := finish mem t2 (by simpa [refs, memEq] using updatedHeap)
        (stateRel_insert_3_1 conf l1 l2 {next with refs := refs} {target with memory := mem} none locs
          (.word hd) (.word x))
      have dom1' : target.mdomain (x + BitVec.ofNat width (width / 8)) = true := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using dom1
      have hb1 : adjustVar b ≠ 1 := by simp [adjustVar]
      have hb3 : adjustVar b ≠ 3 := by simp [adjustVar]
      have readB : sptLookup (adjustVar b) target.locals = some word2 := by
        simpa [WordSemStateFiniteExact.getVar] using operands.2
      refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) t2,
        ?_, by simp, fun _ => ⟨by simpa [next, refs] using relFinal, rfl⟩⟩
      simp [compileAssign, arg2, assignUpdateThunk, hdEq, wordListSeq, unitExp,
        WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memStore,
        WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        realExp, sptLookup_sptInsert_same, sptLookup_sptInsert_ne, hb1, hb3, readB, theWords, wordOpHOL,
        wordOp, t2, mem, StackRemove.bytesInWord, wordSemBytesInWord, dom0, dom1']
      all_goals rfl
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
