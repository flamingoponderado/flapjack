import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocalUpdates

/-! Reserved target locals in the candidate data-to-word relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Updating a nonzero target local outside the adjusted source-local range
preserves the candidate state relation. This is Lean-side simulation
infrastructure; the candidate relation is not yet the unrestricted HOL port. -/
theorem stateRel64_setScratch {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (scratch : Nat) (word : WordLocW 64) (nonzero : scratch ≠ 0)
    (disjoint : ∀ n, adjustVar n ≠ scratch) :
    stateRel64 conf l1 l2 source (WordSemStateFiniteExact.setVar scratch word target) none locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals, ?_, ?_,
    stack, locations, stackBound, maxBound, stackSize, localSize, limits, ?_⟩
  · intro _
    change sptLookup 0 (sptInsert scratch word target.locals) = some (.loc l1 l2)
    rw [sptLookup_sptInsert_ne]
    · exact zero rfl
    · exact Ne.symm nonzero
  · intro n present
    change (sptLookup (adjustVar n) (sptInsert scratch word target.locals)).isSome = true
    rw [sptLookup_sptInsert_ne scratch (adjustVar n) word target.locals (disjoint n)]
    exact locals n present
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      change pair ∈ joinEnv source.locals
          (sptToAList (sptInter (sptInsert scratch word target.locals) (adjustSet source.locals))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
      simp only [List.mem_append] at member ⊢
      rcases member with (localPair | global) | frame
      · obtain ⟨n, sourceLookup, targetLookup⟩ := joinEnv_localPair source.locals
          (sptInsert scratch word target.locals) pair.1 pair.2 localPair
        rw [sptLookup_sptInsert_ne scratch (adjustVar n) word target.locals (disjoint n)] at targetLookup
        exact Or.inl (Or.inl (localPair_mem_joinEnv source.locals target.locals n pair.1 pair.2 sourceLookup targetLookup))
      · exact Or.inl (Or.inr global)
      · exact Or.inr frame
    · simpa using memory

/-- Register 1 is reserved for compiler temporaries. -/
theorem stateRel64_setScratch1 {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs) (word : WordLocW 64) :
    stateRel64 conf l1 l2 source (WordSemStateFiniteExact.setVar 1 word target) none locs := by
  apply stateRel64_setScratch conf l1 l2 source target locs related 1 word (by decide)
  intro n
  simp [adjustVar]

/-- An adjusted source register is distinct from temporary register 1. -/
theorem adjustedVar_ne_scratch1 (n : Nat) : adjustVar n ≠ 1 := by
  simp [adjustVar]

/-- Installing scratch register 1 preserves all adjusted source variables. -/
theorem getVar_setScratch1 {C F : Type} (target : WordSemStateFiniteExact 64 C F)
    (n : Nat) (word : WordLocW 64) :
    WordSemStateFiniteExact.getVar (adjustVar n) (WordSemStateFiniteExact.setVar 1 word target) =
      WordSemStateFiniteExact.getVar (adjustVar n) target := by
  simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
    sptLookup_sptInsert_ne, adjustedVar_ne_scratch1]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
