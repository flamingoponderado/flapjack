import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.ReturnRoots
import Mathlib.Tactic

/-! Updating locals while preserving the data-to-word memory invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Every joined local pair comes from matching source and target lookups. -/
theorem joinEnv_localPair (source : Spt DataSem.Value) (target : Spt (WordLocW 64))
    (value : DataSem.Value) (word : WordLocW 64)
    (member : (value, word) ∈ joinEnv source (sptToAList (sptInter target (adjustSet source)))) :
    ∃ n, sptLookup n source = some value ∧ sptLookup (adjustVar n) target = some word := by
  unfold joinEnv at member
  obtain ⟨⟨key, w⟩, filtered, equal⟩ := List.mem_map.mp member
  obtain ⟨entry, valid⟩ := List.mem_filter.mp filtered
  have lookup := (sptMemToAList (sptInter target (adjustSet source)) key w).mp entry
  rw [sptLookup_sptInterCases] at lookup
  cases ht : sptLookup key target with
  | none => simp [ht] at lookup
  | some v =>
    cases ha : sptLookup key (adjustSet source) with
    | none => simp [ht, ha] at lookup
    | some payload =>
      simp [ht, ha] at lookup
      subst w
      have dom : sptDomain (adjustSet source) key := (sptMem_iff_lookup key (adjustSet source)).mpr ⟨payload, ha⟩
      obtain ⟨n, keyEq, present⟩ := (adjustSet_domain source key).mp dom
      subst key
      have src := (sptMem_iff_lookup n source).mp present
      obtain ⟨x, sourceLookup⟩ := src
      have index : (adjustVar n - 2) / 2 = n := by simp [adjustVar]
      simp only [Prod.mk.injEq] at equal
      have veq : x = value := by simpa [index, sourceLookup, holThe] using equal.1
      have weq : v = word := equal.2
      exact ⟨n, by simpa [veq] using sourceLookup, by simpa [weq] using ht⟩

/-- Updating corresponding locals can only retain old pairs or duplicate the
pair installed at the destination. -/
theorem joinEnv_update_subset (source : Spt DataSem.Value) (target : Spt (WordLocW 64))
    (dest : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (present : (value, word) ∈ joinEnv source (sptToAList (sptInter target (adjustSet source)))) :
    ∀ pair ∈ joinEnv (sptInsert dest value source)
      (sptToAList (sptInter (sptInsert (adjustVar dest) word target) (adjustSet (sptInsert dest value source)))),
      pair ∈ joinEnv source (sptToAList (sptInter target (adjustSet source))) := by
  intro ⟨v, w⟩ member
  obtain ⟨n, sourceLookup, targetLookup⟩ := joinEnv_localPair (sptInsert dest value source)
    (sptInsert (adjustVar dest) word target) v w member
  by_cases equal : n = dest
  · subst n
    rw [sptLookup_sptInsert_same] at sourceLookup targetLookup
    cases Option.some.inj sourceLookup
    cases Option.some.inj targetLookup
    exact present
  · have keyNe : adjustVar n ≠ adjustVar dest := by simp only [adjustVar]; omega
    rw [sptLookup_sptInsert_ne dest n value source equal] at sourceLookup
    rw [sptLookup_sptInsert_ne (adjustVar dest) (adjustVar n) word target keyNe] at targetLookup
    exact localPair_mem_joinEnv source target n v w sourceLookup targetLookup

/-- Copying a related source/word pair into corresponding local names
preserves the candidate relation, including the saved return location. -/
theorem stateRel64_setLocal {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (related : stateRel64 conf l1 l2 source target none locs)
    (dest src : Nat) (value : DataSem.Value) (word : WordLocW 64)
    (sourceRun : DataSem.getVar src source.locals = some value)
    (targetRun : WordSemStateFiniteExact.getVar (adjustVar src) target = some word) :
    stateRel64 conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) none locs := by
  have present := localPair_mem_joinEnv source.locals target.locals src value word sourceRun targetRun
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
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    · intro pair member
      change pair ∈ joinEnv (sptInsert dest value source.locals)
          (sptToAList (sptInter (sptInsert (adjustVar dest) word target.locals)
            (adjustSet (sptInsert dest value source.locals)))) ++
          [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack at member
      simp only [List.mem_append] at member ⊢
      rcases member with (newLocal | global) | frame
      · exact Or.inl (Or.inl (joinEnv_update_subset source.locals target.locals dest value word present pair newLocal))
      · exact Or.inl (Or.inr global)
      · exact Or.inr frame
    · simpa using memory

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
