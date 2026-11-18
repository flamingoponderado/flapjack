module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Global
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Roots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.GlobalsSet
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State

@[expose] public section

/-! Global-value stores in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

/-- Replacing the source reference tree and target memory preserves the
state relation when the original memory relation is re-established. This is
an intermediate step of the source global-store proof. -/
private theorem stateRel_replaceMemory {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (memory : BitVec width → WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (heap : memoryRel conf target.be (holThe source.tstamps) refs source.space target.store memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) :
    stateRel conf l1 l2 {source with refs := refs} {target with memory := memory} none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, heap⟩

/-- The global-value update case of the original assignment goal. The
compiler and state relation are pending source review, so it is untagged. -/
theorem assignSetGlobal_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l l1 l2 dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (result : DataSem.Value)
    (globalOp : ∃ i, op = .globOp (.setGlobal i))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
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
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons value values =>
      cases values with
      | cons head tail => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | nil =>
        cases globalEq : source.global with
        | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq] at run
        | some ptr =>
          cases refEq : sptLookup ptr source.refs with
          | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
          | some cell =>
            cases cell with
            | valueArray entries =>
              by_cases bound : i < entries.length
              · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                  DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq, bound] at run
                obtain ⟨rfl, rfl⟩ := run
                have argLen : args.length = 1 := by
                  have h := DataSpace.getVars_length args source.locals [value] argsEq
                  simpa using h.symm
                cases args with
                | nil => simp at argLen
                | cons arg args =>
                  cases args with
                  | cons extra tail => simp at argLen
                  | nil =>
                    have sourceFound : DataSem.getVar arg source.locals = some value := by
                      cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
                    obtain ⟨word, targetFound⟩ :=
                      stateRel_getVar conf l1 l2 source target none locs arg value related sourceFound
                    let next := DataSem.doStack (.globOp (.setGlobal i)) [value]
                      (DataSem.doLimSafe source (.globOp (.setGlobal i)) [value])
                    have nextRel : stateRel conf l1 l2 next target none locs :=
                      stateRel_doStack conf l1 l2 _ target locs _ _
                        (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                    let globals := holFapply target.store .globals
                    let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
                    let rest := flatStack next.stack target.stack
                    have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                    have added := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
                      target.store target.memory target.mdomain next.locals target
                      ([(theGlobal next.global, globals)] ++ rest) [arg] [value] [word] (by
                        refine ⟨?_, ?_, ?_⟩
                        · simpa [globals, locals, rest] using hmem
                        · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
                        · simp [WordSemStateFiniteExact.getVars, targetFound])
                    have roots : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain
                        ((value, word) :: (.refPtr true ptr, globals) :: locals ++ rest) := by
                      apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain _ _ ?_ added
                      intro pair member
                      simp [locals, next, DataSem.doStack, DataSem.doLimSafe, globalEq, theGlobal] at member ⊢
                      tauto
                    have good := nextRel.2.2.2.2.2.2.1
                    have refNext : sptLookup ptr next.refs = some (.valueArray entries) := by
                      simpa [next, DataSem.doStack, DataSem.doLimSafe] using refEq
                    obtain ⟨w, addr, globalWord, realAddr, domain, updatedHeap⟩ :=
                      memoryRel_updateRef conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain value word true ptr globals (locals ++ rest)
                        entries i ⟨roots, refNext, good, bound⟩
                    have rootFirst : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain
                        ((.refPtr true ptr, globals) :: (value, word) :: locals ++ rest) := by
                      apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain _ _ ?_ roots
                      intro pair member
                      change pair ∈ (.refPtr true ptr, globals) :: (value, word) :: (locals ++ rest) at member
                      change pair ∈ (value, word) :: (.refPtr true ptr, globals) :: (locals ++ rest)
                      simp only [List.mem_cons] at member ⊢
                      tauto
                    obtain ⟨w1, addr1, locationEq, real1, simple1⟩ :=
                      memoryRel_refPtrTrueAddress conf target.be (holThe next.tstamps) next.refs next.space
                        target.store target.memory target.mdomain ptr globals ((value, word) :: locals ++ rest) good rootFirst
                    have sameWord : w1 = w := by rw [globalWord] at locationEq; exact WordLocW.word.inj locationEq.symm
                    subst w1
                    have sameAddr : addr1 = addr := Option.some.inj (real1.symm.trans realAddr)
                    subst addr1
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
                    let mem := fun key => if key = addr + StackRemove.bytesInWord width +
                      StackRemove.bytesInWord width * BitVec.ofNat width i then word else target.memory key
                    let refs := sptInsert ptr (.valueArray (entries.set i value)) next.refs
                    have baseHeap : memoryRel conf target.be (holThe next.tstamps) refs next.space
                        target.store mem target.mdomain (locals ++ [(theGlobal next.global, globals)] ++ rest) := by
                      apply memoryRel_rearrange conf target.be (holThe next.tstamps) refs next.space
                        target.store mem target.mdomain _ _ ?_ updatedHeap
                      intro pair member
                      simp only [List.mem_cons, List.mem_append] at member ⊢
                      simp only [next, DataSem.doStack, DataSem.doLimSafe, globalEq, theGlobal] at member ⊢
                      tauto
                    let midSource := {next with refs := refs}
                    let midTarget := {target with memory := mem}
                    have midRel : stateRel conf l1 l2 midSource midTarget none locs :=
                      stateRel_replaceMemory conf l1 l2 next target locs refs mem nextRel (by
                        simpa [locals, rest, globals] using baseHeap)
                    have unitRoot := memoryRel_unit conf target.be (holThe next.tstamps) refs next.space
                      target.store mem target.mdomain (locals ++ [(theGlobal next.global, globals)] ++ rest) ⟨baseHeap, good⟩
                    have finalRel := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest DataSem.unitValue
                      (.word 2) midRel (by simpa [midSource, midTarget, locals, rest, globals] using unitRoot)
                    have compiled : compileControl (width := width) conf n l
                        (.assign dest (.globOp (.setGlobal i)) [arg] none) = assignSetGlobal conf i l dest arg := by
                      have h := compileControl_option (width := width) conf n l
                        (.assign dest (.globOp (.setGlobal i)) [arg] none)
                      simpa [compileControl?, compileAssign, arg1] using h.symm
                    have domain' : target.mdomain
                        (addr + (BitVec.ofNat width (width / 8) +
                          BitVec.ofNat width (width / 8) * BitVec.ofNat width i)) = true := by
                      simpa [StackRemove.bytesInWord, BitVec.add_assoc] using domain
                    refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) midTarget, ?_, ?_, ?_⟩
                    · simp [compiled, assignSetGlobal, unitExp, WordSemStateFiniteExact.evaluate,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
                        WordSemStateFiniteExact.memStore, WordSemStateFiniteExact.fixClock, targetFound,
                        realLookup, midTarget, mem, wordSemBytesInWord, StackRemove.bytesInWord,
                        theWords, wordOpHOL, wordOp, BitVec.ofNat_add, BitVec.mul_add,
                        BitVec.add_assoc, BitVec.add_comm, domain']
                    · simp
                    · simpa [midSource, midTarget, refs, next, DataSem.doStack, DataSem.doLimSafe, globalEq] using finalRel
              · simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                  DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq, bound] at run
            | byteArray flag bytes =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
            | thunk mode child =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run
            | mutBlock tag fin left child right =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, globalEq, refEq] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
