import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorSetup
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.NewLocal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Scratch

/-! Relating constructor arguments to the state relation's heap roots. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Starting from related states, the checked constructor compiler emits a
sequence that executes using the corresponding source and target locals. Its
heap result represents the newly allocated block along with all prior roots.
This is Flapjack simulation infrastructure, not a complete pass theorem. -/
theorem stateRel64_cons_heap {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (names : Option (Spt Unit)) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars args source.locals = some values)
    (nonempty : values ≠ []) (enough : values.length + 1 ≤ source.space)
    (header : BitVec 64) (encoded : encodeHeader conf (4 * tag) values.length = some header) :
    ∃ (words : List (WordLocW 64)) (program : WordLangProgHOL (BitVec 64))
      (index : Nat) (final : WordSemStateFiniteExact 64 C F),
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      compileControl? conf secn label (.assign dest (.blockOp (.cons tag)) args names) = some (program, label) ∧
      WordSemStateFiniteExact.evaluate program target = (none, final) ∧
      WordSemStateFiniteExact.getVar (adjustVar dest) final =
        some (wordAddr conf (.pointer index (.word (ptrBits conf tag values.length)))) ∧
      (∃ (base free : BitVec 64) (mem : BitVec 64 → WordLocW 64),
        final = WordSemStateFiniteExact.setVar (adjustVar dest)
          (wordAddr conf (.pointer index (.word (ptrBits conf tag values.length))))
          (WordSemStateFiniteExact.setVar 3 (.word header) (WordSemStateFiniteExact.setVar 1 (.word base)
            (WordSemStateFiniteExact.setStore .nextFree (.word free) { target with memory := mem })))) ∧
      memoryRel conf target.be (holThe source.tstamps + 1) source.refs (source.space - (values.length + 1))
        final.store final.memory final.mdomain
        (((.block (holThe source.tstamps) tag values),
          wordAddr conf (.pointer index (.word (ptrBits conf tag values.length)))) ::
          (values.zip words) ++
          (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
  obtain ⟨words, wordRun, lengths⟩ := stateRel64_getVars conf l1 l2 source target none locs related args values sourceRun
  have withRoots := stateRel64_returnRoots conf l1 l2 source target locs related args values words sourceRun wordRun
  have firstMap : (values.zip words).map Prod.fst = values := List.map_fst_zip (by omega)
  have secondMap : (values.zip words).map Prod.snd = words := List.map_snd_zip (by omega)
  have zipLength : (values.zip words).length = values.length := by simp [List.length_zip, lengths]
  have zipNonempty : values.zip words ≠ [] := by
    intro empty
    apply nonempty
    have := congrArg (List.map Prod.fst) empty
    simpa [firstMap] using this
  have memory : memoryRel conf target.be (holThe source.tstamps) source.refs source.space target.store target.memory target.mdomain
      ((values.zip words) ++
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
    simpa [stateRel64] using withRoots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨program, index, final, compiled, run, pointer, frame, result⟩ :=
    compileControl_cons_evaluate conf secn label dest tag args names (values.zip words)
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
      source.refs (holThe source.tstamps) source.space target.be header target
      related.2.2.2.2.2.2.1 zipNonempty (by simpa [zipLength] using enough)
      (by simpa [zipLength] using encoded) memory (by simpa [secondMap] using wordRun)
  refine ⟨words, program, index, final, wordRun, compiled, run, ?_, ?_, ?_⟩
  · simpa [zipLength] using pointer
  · simpa [zipLength] using frame
  · simpa [zipLength, firstMap] using result

/-- A constructor heap update restores the candidate state relation before
the new block is installed in a local. The caller supplies the heap relation
established by the generated stores. -/
theorem stateRel64_cons_heap_update {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (next tag cost : Nat) (values : List DataSem.Value) (word : WordLocW 64)
    (free : BitVec 64) (memory : BitVec 64 → WordLocW 64)
    (stamps : source.tstamps = some next)
    (heap : memoryRel conf target.be (next + 1) source.refs (source.space - cost)
      (target.store.updateEq (.nextFree, .word free)) memory target.mdomain
      ((.block next tag values, word) ::
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))) :
    stateRel64 conf l1 l2 { source with tstamps := source.tstamps.map (· + 1), space := source.space - cost }
      (WordSemStateFiniteExact.setStore .nextFree (.word free) { target with memory := memory })
      none locs := by
  simp only [stamps, Option.map_some]
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, good, shift, _, globals, zero,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, limits, _⟩
  have globalsApply : holFapply (target.store.updateEq (.nextFree, .word free)) .globals =
      holFapply target.store .globals := by
    simp [holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have newOracle : codeOracleRel64 conf source.compile source.compileOracle
      (target.store.updateEq (.nextFree, .word free)) target.compile target.compileOracle
      target.codeBuffer target.dataBuffer := by
    simpa [codeOracleRel64, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using oracle
  have newLimits : limitsInv source.limits ((target.store.updateEq (.nextFree, .word free)).lookup .heapLength)
      target.stackLimit conf.lenSize conf.hasFpOps conf.hasFpTern := by
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using limits
  refine ⟨ffi, clock, handler, gc, code, newOracle, good, shift, by simp, ?_, ?_,
    names, stackRel, locRel, stackBound, stackMax, stackSize, localsSize, newLimits, ?_⟩
  · simpa [WordSemStateFiniteExact.setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using globals
  · intro _
    exact zero rfl
  · apply memoryRel_rearrange conf target.be (next + 1) source.refs (source.space - cost)
      (target.store.updateEq (.nextFree, .word free)) memory target.mdomain
      ((.block next tag values, word) ::
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))
    · intro pair member
      apply List.mem_cons_of_mem
      simpa [WordSemStateFiniteExact.setStore, globalsApply, holThe] using member
    · exact heap

/-- The emitted nonempty constructor sequence preserves the candidate state
relation after allocation and assignment. This covers the heap operation;
source evaluator side conditions and stack accounting are handled separately. -/
theorem stateRel64_cons_compiled {C F : Type} (conf : Config) (secn label l1 l2 dest tag : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (args : List Nat) (names : Option (Spt Unit)) (values : List DataSem.Value)
    (sourceRun : DataSem.getVars args source.locals = some values)
    (nonempty : values ≠ []) (enough : values.length + 1 ≤ source.space)
    (header : BitVec 64) (encoded : encodeHeader conf (4 * tag) values.length = some header)
    (next : Nat) (stamps : source.tstamps = some next) :
    ∃ (program : WordLangProgHOL (BitVec 64)) (final : WordSemStateFiniteExact 64 C F),
      compileControl? conf secn label (.assign dest (.blockOp (.cons tag)) args names) = some (program, label) ∧
      WordSemStateFiniteExact.evaluate program target = (none, final) ∧
      stateRel64 conf l1 l2
        (DataSem.setVar dest (.block next tag values)
          { source with tstamps := some (next + 1), space := source.space - (values.length + 1) })
        final none locs := by
  obtain ⟨words, program, index, final, _, compiled, run, _, frame, heap⟩ :=
    stateRel64_cons_heap conf secn label l1 l2 dest tag source target locs related args names values
      sourceRun nonempty enough header encoded
  obtain ⟨base, free, mem, frame⟩ := frame
  let pointer : WordLocW 64 := wordAddr conf (.pointer index (.word (ptrBits conf tag values.length)))
  let updatedSource := { source with tstamps := some (next + 1), space := source.space - (values.length + 1) }
  let updatedTarget := WordSemStateFiniteExact.setStore .nextFree (.word free) { target with memory := mem }
  let prepared := WordSemStateFiniteExact.setVar 3 (.word header)
    (WordSemStateFiniteExact.setVar 1 (.word base) updatedTarget)
  have oldRoots : memoryRel conf target.be (next + 1) source.refs (source.space - (values.length + 1))
      (target.store.updateEq (.nextFree, .word free)) mem target.mdomain
      ((.block next tag values, pointer) ::
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)) := by
    apply memoryRel_rearrange conf target.be (next + 1) source.refs (source.space - (values.length + 1))
      (target.store.updateEq (.nextFree, .word free)) mem target.mdomain
      ((.block next tag values, pointer) :: (values.zip words) ++
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))
    · intro pair member
      rcases List.mem_cons.mp member with same | old
      · subst pair
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ old)
    · simpa [frame, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore, stamps, holThe, pointer] using heap
  have updatedRel : stateRel64 conf l1 l2 updatedSource updatedTarget none locs := by
    simpa [updatedSource, updatedTarget, stamps] using
      stateRel64_cons_heap_update conf l1 l2 source target locs related next tag (values.length + 1)
        values pointer free mem stamps oldRoots
  have scratch1 := stateRel64_setScratch1 conf l1 l2 updatedSource updatedTarget locs updatedRel (.word base)
  have scratch3 : stateRel64 conf l1 l2 updatedSource prepared none locs := by
    apply stateRel64_setScratch conf l1 l2 updatedSource _ locs scratch1 3 (.word header) (by decide)
    intro n
    simp [adjustVar]
  have globalsApply : holFapply (target.store.updateEq (.nextFree, .word free)) .globals =
      holFapply target.store .globals := by
    simp [holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have newMemory : memoryRel conf prepared.be (holThe updatedSource.tstamps) updatedSource.refs updatedSource.space
      prepared.store prepared.memory prepared.mdomain
      ((.block next tag values, pointer) ::
        (joinEnv updatedSource.locals (sptToAList (sptInter prepared.locals (adjustSet updatedSource.locals))) ++
          [(theGlobal updatedSource.global, holFapply prepared.store .globals)] ++ flatStack updatedSource.stack prepared.stack)) := by
    change memoryRel conf target.be (next + 1) source.refs (source.space - (values.length + 1))
      (target.store.updateEq (.nextFree, .word free)) mem target.mdomain
      ((.block next tag values, pointer) ::
        (joinEnv source.locals (sptToAList (sptInter prepared.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply (target.store.updateEq (.nextFree, .word free)) .globals)] ++
          flatStack source.stack target.stack))
    rw [globalsApply]
    apply memoryRel_rearrange conf target.be (next + 1) source.refs (source.space - (values.length + 1))
      (target.store.updateEq (.nextFree, .word free)) mem target.mdomain
      ((.block next tag values, pointer) ::
        (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))
    · intro pair member
      rcases List.mem_cons.mp member with same | old
      · exact List.mem_cons.mpr (Or.inl same)
      · apply List.mem_cons_of_mem
        simp only [List.mem_append] at old ⊢
        rcases old with (localPair | global) | stack
        · obtain ⟨n, sourceLookup, targetLookup⟩ := joinEnv_localPair source.locals prepared.locals pair.1 pair.2 localPair
          have key1 : adjustVar n ≠ 1 := by simp [adjustVar]
          have key3 : adjustVar n ≠ 3 := by simp [adjustVar]
          have targetLookup' : sptLookup (adjustVar n) target.locals = some pair.2 := by
            simpa [prepared, updatedTarget, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore,
              sptLookup_sptInsert_ne, key1, key3] using targetLookup
          exact Or.inl (Or.inl (localPair_mem_joinEnv source.locals target.locals n pair.1 pair.2 sourceLookup targetLookup'))
        · exact Or.inl (Or.inr global)
        · exact Or.inr stack
    · exact oldRoots
  have assigned := stateRel64_setNewLocal conf l1 l2 updatedSource prepared locs scratch3 dest
    (.block next tag values) pointer newMemory
  refine ⟨program, final, compiled, run, ?_⟩
  simpa [frame, prepared, updatedTarget, updatedSource, pointer] using assigned

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
