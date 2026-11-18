module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GlobalsPtr
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefArrayElement

@[expose] public section

/-! The global-value assignment case of the data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

/-- The global-value case retains the source assignment goal. Its compiler
and state relation are pending source review, so it is not yet HOL-tagged. -/
theorem assignGlobal_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l l1 l2 dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (result : DataSem.Value)
    (globalOp : ∃ i, op = .globOp (.global i))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (_argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.assign dest op args names)).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨i, rfl⟩ := globalOp
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    cases values with
    | cons head tail =>
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | nil =>
      cases globalEq : source.global with
      | none =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq] at run
      | some ptr =>
        cases refEq : sptLookup ptr source.refs with
        | none =>
          simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
        | some cell =>
          cases cell with
          | valueArray entries =>
            cases entryEq : entries[i]? with
            | none =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq, entryEq] at run
            | some entry =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq, entryEq] at run
              obtain ⟨rfl, rfl⟩ := run
              have bound : i < entries.length := (List.getElem?_eq_some_iff.mp entryEq).1
              have entryValue : entries[i] = entry := (List.getElem?_eq_some_iff.mp entryEq).2
              let next := DataSem.doStack (.globOp (.global i)) []
                (DataSem.doLimSafe source (.globOp (.global i)) [])
              have nextRel : stateRel conf l1 l2 next target none locs :=
                stateRel_doStack conf l1 l2 _ target locs _ _
                  (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
              let globals := holFapply target.store .globals
              let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
              let rest := flatStack next.stack target.stack
              have roots : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain ((.refPtr true ptr, globals) :: locals ++ rest) := by
                have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain _ _ ?_ hmem
                intro pair member
                change pair ∈ (.refPtr true ptr, globals) :: (locals ++ rest) at member
                rcases List.mem_cons.mp member with rfl | member
                · simp [next, globals, DataSem.doStack, DataSem.doLimSafe, globalEq, theGlobal]
                · simp only [locals, rest, List.mem_append] at member ⊢
                  rcases member with h | h
                  · exact Or.inl (Or.inl (Or.inr h))
                  · exact Or.inr h
              have good := nextRel.2.2.2.2.2.2.1
              have refNext : sptLookup ptr next.refs = some (.valueArray entries) := by
                simpa [next, DataSem.doStack, DataSem.doLimSafe] using refEq
              obtain ⟨w, addr, globalWord, realAddr, domain, extended⟩ :=
                memoryRel_deref conf target.be (holThe next.tstamps) next.refs next.space target.store
                  target.memory target.mdomain true ptr entries globals (locals ++ rest) i
                  ⟨roots, refNext, good, bound⟩
              obtain ⟨w1, addr1, header, locationEq, _, _, real1, simple1, _, _⟩ :=
                memoryRel_refPtrTrueImp conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain ptr globals (locals ++ rest) ⟨roots, good⟩
              have sameWord : w1 = w := by rw [globalWord] at locationEq; exact WordLocW.word.inj locationEq.symm
              subst w1
              have sameAddr : addr1 = addr := Option.some.inj (real1.symm.trans realAddr)
              subst addr1
              have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _, _, _⟩ := hmem
              rcases heapMem with ⟨_, _, _, _, _, _, _, curr, other, _, _, currLookup, _, _, _, _, _, globInv, _, _⟩
              obtain ⟨w2, globalLookup, realLookup⟩ := globInv
              have wordEq : w2 = w := by
                have h := holFapply_of_lookup globalLookup
                change globals = .word w2 at h
                rw [globalWord] at h
                exact WordLocW.word.inj h.symm
              subst w2
              have addressEq : curr + ((w >>> shiftLength conf) <<< wordShiftAmount width) = addr := by
                simpa [getRealSimpleAddr, currLookup] using simple1
              rw [addressEq] at realLookup
              let loaded := target.memory (addr + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width i)
              have newRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain
                  ((entry, loaded) :: locals ++ [(theGlobal next.global, globals)] ++ rest) := by
                apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain _ _ ?_ extended
                intro pair member
                simp only [List.mem_cons, List.mem_append] at member ⊢
                simp only [next, DataSem.doStack, DataSem.doLimSafe, globalEq, theGlobal] at member ⊢
                simp only [entryValue] at ⊢
                tauto
              have updated := stateRel_insertRoot conf l1 l2 next target locs dest entry loaded nextRel (by
                simpa [locals, rest, globals] using newRoot)
              have compiled : compileControl (width := width) conf n l (.assign dest (.globOp (.global i)) args none) =
                  (assignGlobal conf i l dest) := by
                have h := compileControl_option (width := width) conf n l (.assign dest (.globOp (.global i)) args none)
                simpa [compileControl?] using h.symm
              have domain' : target.mdomain
                  (addr + (BitVec.ofNat width (width / 8) +
                    BitVec.ofNat width (width / 8) * BitVec.ofNat width i)) = true := by
                simpa [StackRemove.bytesInWord, BitVec.add_assoc] using domain
              refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) loaded target, ?_, ?_, ?_⟩
              · simp [compiled, assignGlobal, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.memLoad, realLookup, loaded,
                  wordSemBytesInWord, StackRemove.bytesInWord, theWords, wordOpHOL, wordOp,
                  BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm, domain']
              · simp
              · simpa [next, DataSem.doStack, DataSem.doLimSafe, globalEq] using updated
          | byteArray flag bytes =>
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
          | thunk mode value =>
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
          | mutBlock tag fin left value right =>
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
