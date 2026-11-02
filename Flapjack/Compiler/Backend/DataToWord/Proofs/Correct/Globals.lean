import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Constant

/-! Globals-pointer assignment in the 64-bit data-to-word simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- The distinguished globals root can be copied into corresponding locals. -/
theorem stateRel64_setGlobalsPtr {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (dest ptr : Nat) (word : WordLocW 64)
    (global : source.global = some ptr) (lookup : target.store.lookup .globals = some word) :
    stateRel64 conf l1 l2 (DataSem.setVar dest (.refPtr true ptr) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs := by
  apply stateRel64_setNewLocal conf l1 l2 source target locs related
  let roots := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have pairMem : (DataSem.Value.refPtr true ptr, word) ∈ roots := by
    simp [roots, theGlobal, global, holFapply_of_lookup lookup]
  apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain roots
  · intro pair present
    simp only [List.mem_cons] at present
    rcases present with rfl | tail
    · exact pairMem
    · exact tail
  · simpa [roots] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The target globals-store lookup represents the source global pointer. -/
theorem assignGlobalsPtr64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (dest ptr : Nat) (global : source.global = some ptr) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp .globalsPtr) [] none) source target locs := by
  obtain ⟨word, lookup⟩ : ∃ word, target.store.lookup .globals = some word := by
    cases h : target.store.lookup .globals with
    | none => exact False.elim (related.2.2.2.2.2.2.2.2.2.1 h)
    | some value => exact ⟨value, rfl⟩
  let op := ClosLang.Op.globOp .globalsPtr
  let middle := DataSem.doStack op [] (DataSem.doLimSafe source op [])
  have middleRel : stateRel64 conf l1 l2 middle target none locs :=
    stateRel64_afterDoStack conf l1 l2 source target locs related op []
  refine ⟨DataSem.setVar dest (.refPtr true ptr) middle, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
  · simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global, DataSem.installSfs, op, middle]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, lookup]
  · exact stateRel64_setGlobalsPtr conf l1 l2 middle target locs middleRel dest ptr word global lookup

/-- Source type safety supplies the global pointer. -/
theorem assignGlobalsPtr64_of_safe {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (dest : Nat)
    (safe : (DataSem.evaluate (.assign dest (.globOp .globalsPtr) [] none) source).1 ≠ some (.err (.abort .typeError))) :
    continues64 conf secn label l1 l2 (.assign dest (.globOp .globalsPtr) [] none) source target locs := by
  cases global : source.global with
  | none =>
    simp [DataSem.evaluate, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.getVars,
      DataSem.cutStateOpt, DataSem.doApp, DataSem.doSpace, DataSpace.opSpaceReq, DataSem.doAppAux,
      DataSem.applyNonFfi, DataSem.doStack, DataSem.doLimSafe, global] at safe
  | some ptr => exact assignGlobalsPtr64 conf secn label l1 l2 source target locs related dest ptr global

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
