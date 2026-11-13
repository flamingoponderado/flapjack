module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InstallNames

@[expose] public section

/-! Correspondence of installed source functions and generated BVI code. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- The first matching source function has a corresponding first matching
compiled entry and its complete auxiliary code occurs as a contiguous segment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_list_imp"]
theorem compileList_imp (n : Nat) (prog : List (Nat × Nat × Bvl.Exp))
    (code : AppList (Nat × Nat × Bvi.Exp)) (n' name arity : Nat) (exp : Bvl.Exp)
    (premises : compileProgramsSource n prog = (code, n') ∧ holALookup prog name = some (arity, exp)) :
    ∃ n0 c aux n1,
      compileListSource n0 [exp] = ([c], aux, n1) ∧
      holALookup (appListAppend code) (bvlToBviNamespaces * name + bvlNumStubs) =
        some (arity, BviLet.compileSing [] 0 c) ∧
      (appListAppend aux) <:+: (appListAppend code) := by
  induction prog generalizing n code n' with
  | nil => simp [holALookup] at premises
  | cons entry rest ih =>
    obtain ⟨key, args, body⟩ := entry
    rcases premises with ⟨compiled, lookup⟩
    cases hfirst : compileSingSource n body with
    | mk converted product =>
      cases product with
      | mk aux next =>
        cases hrest : compileProgramsSource next rest with
        | mk tree finish =>
          simp only [compileProgramsSource, compileSingleSource, hfirst, hrest] at compiled
          cases compiled
          by_cases equal : name = key
          · subst key
            simp [holALookup] at lookup
            rcases lookup with ⟨rfl, rfl⟩
            refine ⟨n, converted, aux, next, ?_, ?_, ?_⟩
            · have nilRight : smartAppend aux .nil = aux := by cases aux <;> rfl
              simp [compileListSource, hfirst, nilRight]
            · simp only [appListAppend_smartAppend]
              simp [appListAppend, appendAux, holALookup, Nat.mul_comm, Nat.add_comm]
            · simp only [appListAppend_smartAppend]
              change appListAppend aux <:+:
                (([(bvlNumStubs + bvlToBviNamespaces * name, args,
                    BviLet.compileSing [] 0 converted)] ++ appListAppend aux) ++ appListAppend tree)
              exact ⟨[(bvlNumStubs + bvlToBviNamespaces * name, args,
                BviLet.compileSing [] 0 converted)], appListAppend tree, by simp⟩
          · have tailLookup : holALookup rest name = some (arity, exp) := by
              simpa [holALookup, equal] using lookup
            obtain ⟨n0, c, foundAux, n1, compilation, found, segment⟩ := ih next tree n' ⟨hrest, tailLookup⟩
            have range := compileSingSource_auxNameRange n body
            rw [hfirst] at range
            dsimp only at range
            have noAux : holALookup (appListAppend aux) (bvlToBviNamespaces * name + bvlNumStubs) = none := by
              cases h : holALookup (appListAppend aux) (bvlToBviNamespaces * name + bvlNumStubs) with
              | none => rfl
              | some value =>
                have member := holALookup_member _ _ value h
                have keyMember : bvlToBviNamespaces * name + bvlNumStubs ∈ (appListAppend aux).map Prod.fst :=
                  List.mem_map.mpr ⟨_, member, rfl⟩
                obtain ⟨k, _, _, keyEq⟩ := auxNameRange_member range _ keyMember
                simp only [bvlToBviNamespaces] at keyEq
                omega
            refine ⟨n0, c, foundAux, n1, compilation, ?_, ?_⟩
            · have neHead : bvlToBviNamespaces * name + bvlNumStubs ≠
                  bvlNumStubs + bvlToBviNamespaces * key := by
                simp only [bvlToBviNamespaces]
                omega
              simp only [appListAppend_smartAppend]
              change holALookup (([(bvlNumStubs + bvlToBviNamespaces * key, args,
                  BviLet.compileSing [] 0 converted)] ++ appListAppend aux) ++ appListAppend tree)
                (bvlToBviNamespaces * name + bvlNumStubs) = _
              rw [holALookup_append, holALookup_append]
              simp [holALookup, neHead, noAux, found]
            · rcases segment with ⟨pre, post, segEq⟩
              simp only [appListAppend_smartAppend]
              change appListAppend foundAux <:+:
                (([(bvlNumStubs + bvlToBviNamespaces * key, args,
                    BviLet.compileSing [] 0 converted)] ++ appListAppend aux) ++ appListAppend tree)
              refine ⟨([(bvlNumStubs + bvlToBviNamespaces * key, args,
                BviLet.compileSing [] 0 converted)] ++ appListAppend aux) ++ pre, post, ?_⟩
              rw [← segEq]
              simp [List.append_assoc]

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
    have fresh := (sptLookupFromAList entries key).trans
      (holALookup_of_distinct_member entries key (arity, body) ⟨distinct, inEntries⟩)
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
    rcases compilation : compileProgramsSource (source.compileOracle 0).1.1 programs with ⟨tree, finish⟩
    obtain ⟨counter, converted, aux, next, singletonRun, translatedLookup, segment⟩ :=
      compileList_imp (source.compileOracle 0).1.1 programs tree finish name arity body
        ⟨compilation, holALookup_of_distinct_member programs name (arity, body) ⟨sourceDistinct, member⟩⟩
    have conversion : compileSingSource counter body = (converted, aux, next) := by
      rcases h : compileSingSource counter body with ⟨converted', aux', next'⟩
      have nilRight : smartAppend aux' .nil = aux' := by cases aux' <;> rfl
      simp only [compileListSource, h, nilRight, Prod.mk.injEq, List.cons.injEq] at singletonRun
      rcases singletonRun with ⟨⟨rfl, _⟩, rfl, rfl⟩
      rfl
    have translated : (bvlNumStubs + bvlToBviNamespaces * name, arity, BviLet.compileSing [] 0 converted) ∈ appListAppend tree := by
      apply holALookup_member
      simpa [Nat.add_comm] using translatedLookup
    have auxSubset : ∀ entry ∈ appListAppend aux, entry ∈ appListAppend tree := by
      intro entry member
      exact segment.mem member
    have translated' : (bvlNumStubs + bvlToBviNamespaces * name, arity, BviLet.compileSing [] 0 converted) ∈ compiled := by
      simpa [compiled, compileIncSource, compilation] using translated
    have auxSubset' : ∀ entry ∈ appListAppend aux, entry ∈ compiled := by
      intro entry inAux
      simpa [compiled, compileIncSource, compilation] using auxSubset entry inAux
    have oldNone := available _ translated'
    have freshLookup := (sptLookupFromAList compiled _).trans
      (holALookup_of_distinct_member compiled _ _ ⟨distinct, translated'⟩)
    refine ⟨counter, ?_⟩
    rw [conversion]
    refine ⟨?_, auxCodeInstalled_union_right _ compiled target.code distinct available auxSubset', ?_⟩
    · rw [sptLookup_sptUnion, oldNone, freshLookup]
    · exact namesOk_oracle source.code target.code source.compileOracle names 0 name arity body member

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
