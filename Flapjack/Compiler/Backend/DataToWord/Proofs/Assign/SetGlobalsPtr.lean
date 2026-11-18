module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SetGlobal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress

@[expose] public section

/-! Global-pointer updates in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

/-- Reconstruct the state relation after changing the global pointer and its
two target store entries. The supplied memory relation is established by
the global-store update proof. -/
private theorem stateRel_replaceGlobals {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (ptr : Nat) (word address : BitVec width)
    (related : stateRel conf l1 l2 source target none locs)
    (heap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      ((target.store.updateEq (.globals, .word word)).updateEq (.globReal, .word address))
      target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(.refPtr true ptr, .word word)] ++ flatStack source.stack target.stack)) :
    stateRel conf l1 l2 {source with global := some ptr}
      {target with store := (target.store.updateEq (.globals, .word word)).updateEq (.globReal, .word address)}
      none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  have oracle' : codeOracleRel conf source.compile source.compileOracle
      ((target.store.updateEq (.globals, .word word)).updateEq (.globReal, .word address))
      target.compile target.compileOracle target.codeBuffer target.dataBuffer := by
    rcases horacle with ⟨a, b, c, d, e, f, g, h, j⟩
    refine ⟨a, b, ?_, ?_, ?_, ?_, g, h, j⟩
    · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using c
    · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using d
    · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using e
    · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using f
  refine ⟨hffi, hclock, hhandler, hgc, hcode, oracle', hgood, hshift, htstamp, ?_,
    hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
  · intro key member
    simp only [List.mem_singleton] at member
    subst key
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  · simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using hlim
  · simpa [theGlobal, holFapply_of_lookup, HolFiniteMapExact.updateEq, FUPDATE_HOL] using heap

/-- The source global-pointer update case, with all original assignment-goal
premises and result branches. It remains untagged pending review of the
shared state-relation and stub dependencies. -/
theorem assignSetGlobalsPtr_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (n l l1 l2 dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) (source cut resultState : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List DataSem.Value) (result : DataSem.Value)
    (globalOp : op = .globOp .setGlobalsPtr)
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
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons value values =>
      cases values with
      | cons head tail => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | nil =>
        cases value with
        | number i => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | word64 w => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | block ts tag xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | codePtr p => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi] at run
        | refPtr bit ptr =>
          cases bit with
          | false => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi] at run
          | true =>
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe] at run
            obtain ⟨rfl, rfl⟩ := run
            have argLen : args.length = 1 := by
              have h := DataSpace.getVars_length args source.locals [.refPtr true ptr] argsEq
              simpa using h.symm
            cases args with
            | nil => simp at argLen
            | cons arg args =>
              cases args with
              | cons extra tail => simp at argLen
              | nil =>
                have sourceFound : DataSem.getVar arg source.locals = some (.refPtr true ptr) := by
                  cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
                obtain ⟨word, targetFound⟩ :=
                  stateRel_getVar conf l1 l2 source target none locs arg (.refPtr true ptr) related sourceFound
                let next := DataSem.doStack (.globOp .setGlobalsPtr) [.refPtr true ptr]
                  (DataSem.doLimSafe source (.globOp .setGlobalsPtr) [.refPtr true ptr])
                have nextRel : stateRel conf l1 l2 next target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
                let rest := flatStack next.stack target.stack
                let oldGlobal := (theGlobal next.global, holFapply target.store .globals)
                have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                have added := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain next.locals target ([oldGlobal] ++ rest) [arg]
                  [.refPtr true ptr] [word] (by
                    refine ⟨?_, ?_, ?_⟩
                    · simpa [oldGlobal, locals, rest] using hmem
                    · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
                    · simp [WordSemStateFiniteExact.getVars, targetFound])
                have roots : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain ((.refPtr true ptr, word) :: locals ++ [oldGlobal] ++ rest) := by
                  simpa [locals, rest] using added
                have good := nextRel.2.2.2.2.2.2.1
                have shiftBound := nextRel.2.2.2.2.2.2.2.1
                obtain ⟨w, addr, wordEq, realDecoded, simpleAddr⟩ :=
                  memoryRel_refPtrTrueAddress conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain ptr word (locals ++ [oldGlobal] ++ rest) good roots
                subst word
                have baseHeap : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain (locals ++ [(.refPtr true ptr, .word w)] ++ rest) := by
                  apply memoryRel_rearrange conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain _ _ ?_ roots
                  intro pair member
                  simp only [List.mem_cons, List.mem_append] at member ⊢
                  tauto
                have updatedHeap := memoryRel_setGlobals conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain _ w addr simpleAddr baseHeap
                let store := (target.store.updateEq (.globals, .word w)).updateEq (.globReal, .word addr)
                let midSource := {next with global := some ptr}
                let midTarget := {target with store := store}
                have midRel : stateRel conf l1 l2 midSource midTarget none locs :=
                  stateRel_replaceGlobals conf l1 l2 next target locs ptr w addr nextRel (by
                    simpa [locals, rest] using updatedHeap)
                have unitRoot := memoryRel_unit conf target.be (holThe next.tstamps) next.refs next.space
                  store target.memory target.mdomain (locals ++ [(.refPtr true ptr, .word w)] ++ rest)
                  ⟨updatedHeap, good⟩
                have finalRel := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest DataSem.unitValue
                  (.word 2) midRel (by
                    simpa [midSource, midTarget, store, locals, rest, theGlobal,
                      holFapply_of_lookup, HolFiniteMapExact.updateEq, FUPDATE_HOL] using unitRoot)
                let first := WordSemStateFiniteExact.setStore .globals (.word w) target
                have addressEval : WordSemStateFiniteExact.wordExp first (realAddr conf (adjustVar arg)) = some (.word addr) := by
                  apply Bignum.getRealAddr_lemma conf (adjustVar arg) first w addr
                  refine ⟨shiftBound, good, ?_, ?_⟩
                  · simpa [first, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.getVar] using targetFound
                  · simpa [first, WordSemStateFiniteExact.setStore, getRealAddr,
                      HolFiniteMapExact.updateEq, FUPDATE_HOL] using realDecoded
                dsimp [first, WordSemStateFiniteExact.setStore] at addressEval
                have compiled : compileAssign (width := width) conf n l dest
                    (.globOp .setGlobalsPtr) [arg] none = assignSetGlobalsPtr conf l dest arg := by
                  rfl
                refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word 2) midTarget, ?_, ?_, ?_⟩
                · simp [compiled, assignSetGlobalsPtr, unitExp, WordSemStateFiniteExact.evaluate,
                    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setStore,
                    WordSemStateFiniteExact.fixClock, targetFound, addressEval, midTarget, store]
                · simp
                · simpa [midSource, midTarget, next, DataSem.doStack, DataSem.doLimSafe] using finalRel

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
