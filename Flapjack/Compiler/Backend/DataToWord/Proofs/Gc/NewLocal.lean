import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocalUpdates
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber

/-! Installing newly represented values in corresponding locals. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- New joined pairs are either the inserted pair or an old joined pair. -/
theorem joinEnv_insert_subset (source : Spt DataSem.Value) (target : Spt (WordLocW 64))
    (dest : Nat) (value : DataSem.Value) (word : WordLocW 64) :
    ∀ pair ∈ joinEnv (sptInsert dest value source)
      (sptToAList (sptInter (sptInsert (adjustVar dest) word target) (adjustSet (sptInsert dest value source)))),
      pair ∈ (value, word) :: joinEnv source (sptToAList (sptInter target (adjustSet source))) := by
  intro ⟨v, w⟩ member
  obtain ⟨n, sourceLookup, targetLookup⟩ := joinEnv_localPair (sptInsert dest value source)
    (sptInsert (adjustVar dest) word target) v w member
  by_cases equal : n = dest
  · subst n
    rw [sptLookup_sptInsert_same] at sourceLookup targetLookup
    cases Option.some.inj sourceLookup
    cases Option.some.inj targetLookup
    exact List.mem_cons_self
  · have keyNe : adjustVar n ≠ adjustVar dest := by simp only [adjustVar]; omega
    rw [sptLookup_sptInsert_ne dest n value source equal] at sourceLookup
    rw [sptLookup_sptInsert_ne (adjustVar dest) (adjustVar n) word target keyNe] at targetLookup
    exact List.mem_cons_of_mem _ (localPair_mem_joinEnv source target n v w sourceLookup targetLookup)

/-- A represented pair can be installed at corresponding locals. Unlike the
copying lemma, the new pair need not already be in the old local environment. -/
theorem stateRel64_setNewLocal {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (dest : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (newMemory : Memory.memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((value, word) :: (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))) :
    stateRel64 conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  refine ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals, ?_, ?_,
    stack, locations, stackBound, maxBound, stackSize, localSize, limits, ?_⟩
  · intro _
    change sptLookup 0 (sptInsert (adjustVar dest) word target.locals) = some (.loc l1 l2)
    rw [sptLookup_sptInsert_ne]
    · exact zero rfl
    · simp [adjustVar]
  · intro n localPresent
    change (sptLookup n (sptInsert dest value source.locals)).isSome = true at localPresent
    change (sptLookup (adjustVar n) (sptInsert (adjustVar dest) word target.locals)).isSome = true
    by_cases eq : n = dest
    · subst n
      simp [sptLookup_sptInsert_same]
    · have keyNe : adjustVar n ≠ adjustVar dest := by simp only [adjustVar]; omega
      rw [sptLookup_sptInsert_ne dest n value source.locals eq] at localPresent
      rw [sptLookup_sptInsert_ne (adjustVar dest) (adjustVar n) word target.locals keyNe]
      exact locals n localPresent
  · apply Memory.memoryRel_rearrange conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain
      ((value, word) :: (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack))
    · intro pair member
      change pair ∈ joinEnv (sptInsert dest value source.locals)
          (sptToAList (sptInter (sptInsert (adjustVar dest) word target.locals)
            (adjustSet (sptInsert dest value source.locals)))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
      simp only [List.mem_append] at member
      rcases member with (newLocal | global) | frame
      · have inNew := joinEnv_insert_subset source.locals target.locals dest value word pair newLocal
        simp only [List.mem_cons] at inNew ⊢
        rcases inNew with same | old
        · exact Or.inl same
        · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ old))
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ global))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ frame)
    · exact newMemory

/-- A small integer constant can be installed without changing memory. -/
theorem stateRel64_setSmallInt {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (dest : Nat) (i : Int)
    (small : smallInt 64 i) :
    stateRel64 conf l1 l2 (DataSem.setVar dest (.number i) source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) (.word (smallnum i)) target) none locs := by
  apply stateRel64_setNewLocal conf l1 l2 source target locs related
  apply Memory.impMemoryRel_number
  exact ⟨Or.inr rfl, small, by simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Increasing the source stack-maximum bound preserves the relation. -/
theorem stateRel64_sourceStackMax {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs) (newMax : Option Nat)
    (increases : BackendProps.optionLe source.stackMax newMax) :
    stateRel64 conf l1 l2 { source with stackMax := newMax } target none locs := by
  rcases related with ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals,
    zero, locals, stack, locations, stackBound, maxBound, stackSize, localSize, limits, memory⟩
  exact ⟨ffi, clock, handler, gc, code, oracle, dimension, shift, timestamps, globals, zero, locals,
    stack, locations, stackBound, BackendProps.optionLe_trans _ _ _ ⟨maxBound, increases⟩,
    stackSize, localSize, limits, memory⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
