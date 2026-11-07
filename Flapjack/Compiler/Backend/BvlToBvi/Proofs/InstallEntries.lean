import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InstallNames

/-! Correspondence of installed source functions and generated BVI code. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Every source function contributes its translated entry and all of its
auxiliary code to the incremental compiler's output. -/
theorem compileProgramsSource_entry (start : Nat) (programs : List (Nat × Nat × Bvl.Exp))
    (name arity : Nat) (body : Bvl.Exp) (member : (name, arity, body) ∈ programs) :
    ∃ counter converted aux next,
      compileSingSource counter body = (converted, aux, next) ∧
      (bvlNumStubs + bvlToBviNamespaces * name, arity, BviLet.compileSing [] 0 converted) ∈
        appListAppend (compileProgramsSource start programs).1 ∧
      ∀ entry ∈ appListAppend aux, entry ∈ appListAppend (compileProgramsSource start programs).1 := by
  induction programs generalizing start with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨key, nargs, exp⟩
    rcases first : compileSingSource start exp with ⟨converted, aux, next⟩
    rcases remaining : compileProgramsSource next rest with ⟨other, finish⟩
    simp only [List.mem_cons] at member
    simp only [compileProgramsSource, compileSingleSource, first, remaining, appListAppend_smartAppend]
    rcases member with equal | tail
    · cases equal
      refine ⟨start, converted, aux, next, first, ?_, ?_⟩
      · simp [appListAppend, appendAux]
      · intro entry inAux
        simp only [List.mem_append]
        exact Or.inl (Or.inr inAux)
    · obtain ⟨counter, converted', aux', final, conversion, inOutput, auxSubset⟩ := ih next tail
      rw [remaining] at inOutput auxSubset
      refine ⟨counter, converted', aux', final, conversion, ?_, ?_⟩
      · exact List.mem_append.mpr (Or.inr inOutput)
      · intro entry inAux
        exact List.mem_append.mpr (Or.inr (auxSubset entry inAux))

/-- An association-list entry with a distinct key is found by sparse-tree
lookup. -/
theorem sptLookup_fromAList_of_distinct {α : Type} (entries : List (Nat × α))
    (key : Nat) (value : α) (distinct : (entries.map Prod.fst).Nodup)
    (member : (key, value) ∈ entries) : sptLookup key (sptFromAList entries) = some value := by
  rw [sptLookup_sptFromAList]
  apply sptAListLookup_eq_of_mem_unique key value entries member
  intro other otherMem
  have same := List.inj_on_of_nodup_map distinct member otherMem (by rfl)
  exact (Prod.mk.inj same).2.symm

/-- If all entries of a list occur in a distinct-key association list, then
they are installed by that list's sparse tree. -/
theorem auxCodeInstalled_fromAList {α β : Type} (aux entries : List (Nat × α × β))
    (distinct : (entries.map Prod.fst).Nodup)
    (subset : ∀ entry ∈ aux, entry ∈ entries) : auxCodeInstalled aux (sptFromAList entries) := by
  induction aux with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨key, arity, body⟩
    refine ⟨sptLookup_fromAList_of_distinct entries key (arity, body) distinct (subset _ (by simp)), ?_⟩
    apply ih
    intro entry member
    exact subset entry (by simp [member])

/-- Existing auxiliary code remains available in a left-biased code union. -/
theorem auxCodeInstalled_union_left {α β : Type} (aux : List (Nat × α × β)) (old fresh : Spt (α × β))
    (installed : auxCodeInstalled aux old) : auxCodeInstalled aux (sptUnion old fresh) := by
  induction aux with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨key, arity, body⟩
    rcases installed with ⟨lookup, tail⟩
    refine ⟨?_, ih tail⟩
    rw [sptLookup_sptUnion, lookup]

/-- Auxiliary entries from a disjoint association list are installed in the
union with existing code. -/
theorem auxCodeInstalled_union_right {α β : Type} (aux entries : List (Nat × α × β)) (old : Spt (α × β))
    (distinct : (entries.map Prod.fst).Nodup)
    (available : ∀ entry ∈ entries, sptLookup entry.1 old = none)
    (subset : ∀ entry ∈ aux, entry ∈ entries) : auxCodeInstalled aux (sptUnion old (sptFromAList entries)) := by
  induction aux with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨key, arity, body⟩
    have inEntries := subset (key, arity, body) (by simp)
    have oldNone := available (key, arity, body) inEntries
    have fresh := sptLookup_fromAList_of_distinct entries key (arity, body) distinct inEntries
    refine ⟨?_, ?_⟩
    · rw [sptLookup_sptUnion, oldNone, fresh]
    · apply ih
      intro entry member
      exact subset entry (by simp [member])

/-- After installation every source function still has the related compiled
target function and installed auxiliary entries. -/
theorem installed_code_correspondence {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target)
    (sourceAvailable : ∀ entry ∈ (source.compileOracle 0).2, sptLookup entry.1 source.code = none)
    (sourceDistinct : ((source.compileOracle 0).2.map Prod.fst).Nodup) :
    ∀ name arity body,
      sptLookup name (sptUnion source.code (sptFromAList (source.compileOracle 0).2)) = some (arity, body) →
      ∃ counter, let (converted, aux, _) := compileSingSource counter body
        sptLookup (bvlNumStubs + bvlToBviNamespaces * name)
          (sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)) =
            some (arity, BviLet.compileSing [] 0 converted) ∧
        auxCodeInstalled (appListAppend aux)
          (sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)) ∧
        BvlHandle.Proofs.handleOk [body] := by
  let programs := (source.compileOracle 0).2
  let compiled := (compileIncSource (source.compileOracle 0).1.1 programs).2
  have names : namesOk source.code target.code source.compileOracle := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have available : ∀ entry ∈ compiled, sptLookup entry.1 target.code = none :=
    compileIncSource_available source.code target.code source.compileOracle names sourceAvailable
  have distinct : (compiled.map Prod.fst).Nodup :=
    compileIncSource_names_nodup (source.compileOracle 0).1.1 programs sourceDistinct
  intro name arity body lookup
  rw [sptLookup_sptUnion] at lookup
  cases old : sptLookup name source.code with
  | some oldBody =>
    simp [old] at lookup
    subst oldBody
    obtain ⟨counter, oldEntry, oldAux, handles⟩ := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2 name arity body old
    refine ⟨counter, ?_, ?_, handles⟩
    · rw [sptLookup_sptUnion, oldEntry]
    · exact auxCodeInstalled_union_left _ _ _ oldAux
  | none =>
    simp only [old] at lookup
    rw [sptLookup_sptFromAList] at lookup
    have member : (name, arity, body) ∈ programs := sptAListLookup_mem name programs (arity, body) lookup
    obtain ⟨counter, converted, aux, next, conversion, translated, auxSubset⟩ :=
      compileProgramsSource_entry (source.compileOracle 0).1.1 programs name arity body member
    rcases compilation : compileProgramsSource (source.compileOracle 0).1.1 programs with ⟨tree, finish⟩
    have translated' : (bvlNumStubs + bvlToBviNamespaces * name, arity, BviLet.compileSing [] 0 converted) ∈ compiled := by
      simpa [compiled, compileIncSource, compilation] using translated
    have auxSubset' : ∀ entry ∈ appListAppend aux, entry ∈ compiled := by
      intro entry inAux
      simpa [compiled, compileIncSource, compilation] using auxSubset entry inAux
    have oldNone := available _ translated'
    have freshLookup := sptLookup_fromAList_of_distinct compiled _ _ distinct translated'
    refine ⟨counter, ?_⟩
    rw [conversion]
    refine ⟨?_, auxCodeInstalled_union_right _ compiled target.code distinct available auxSubset', ?_⟩
    · rw [sptLookup_sptUnion, oldNone, freshLookup]
    · exact namesOk_oracle source.code target.code source.compileOracle names 0 name arity body member

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
