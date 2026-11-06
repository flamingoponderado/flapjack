import Flapjack.Compiler.Backend.BviInline.Proofs.ProgramCache
import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation

/-! Code-entry relations for BVI program inlining. -/
namespace Flapjack.Compiler.Backend.BviInline

/-- Flapjack infrastructure: adding a cached wrapper already present in the
target code preserves cache inclusion. -/
theorem cache_insert_subspt (cache code : Spt (Nat × Bvi.Exp)) (name : Nat) (value : Nat × Bvi.Exp)
    (subset : sptSubspt cache code) (found : sptLookup name code = some value) :
    sptSubspt (sptInsert name value cache) code := by
  rw [sptSubsptLookup] at subset ⊢
  intro key item lookup
  by_cases same : key = name
  · subst key
    rw [sptLookup_sptInsert_same] at lookup
    cases lookup
    exact found
  · rw [sptLookup_sptInsert_ne name key value cache same] at lookup
    exact subset key item lookup

/-- Flapjack infrastructure: if every output entry is in the target code,
each source association-list lookup has a related transformed lookup. -/
theorem inlineAllSource_related_of_output (program : List (Nat × Nat × Bvi.Exp))
    (cache code : Spt (Nat × Bvi.Exp)) (subset : sptSubspt cache code)
    (entries : ∀ name arity body, (name, arity, body) ∈ (inlineAllSource cache program).2 →
      sptLookup name code = some (arity, body)) :
    ∀ name arity body, sptAListLookup name program = some (arity, body) →
      ∃ transformed, sptAListLookup name (inlineAllSource cache program).2 = some (arity, transformed) ∧
        ExpRel code body transformed := by
  induction program generalizing cache with
  | nil => simp [sptAListLookup]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    let body' := inlineExpSource cache body
    let cache' := if canonicalWrapper name arity body' then sptInsert name (arity, body') cache else cache
    have step : inlineAllSource cache ((name, arity, body) :: rest) =
        ((inlineAllSource cache' rest).1, (name, arity, body') :: (inlineAllSource cache' rest).2) := by
      simp [inlineAllSource, body', cache']
    have headFound : sptLookup name code = some (arity, body') := by
      apply entries name arity body'
      rw [step]
      simp
    have nextSubset : sptSubspt cache' code := by
      dsimp [cache']
      split
      · exact cache_insert_subspt cache code name (arity, body') subset headFound
      · exact subset
    have tailEntries : ∀ n a b, (n, a, b) ∈ (inlineAllSource cache' rest).2 →
        sptLookup n code = some (a, b) := by
      intro n a b present
      apply entries n a b
      rw [step]
      exact List.mem_cons_of_mem _ present
    intro key count original lookup
    rw [step]
    by_cases same : key = name
    · subst key
      simp [sptAListLookup] at lookup
      rcases lookup with ⟨rfl, rfl⟩
      exact ⟨body', by simp [sptAListLookup], inlineExpSource_rel cache code body subset⟩
    · have tailLookup : sptAListLookup key rest = some (count, original) := by
        simpa [sptAListLookup, same] using lookup
      obtain ⟨transformed, found, related⟩ := ih cache' nextSubset tailEntries key count original tailLookup
      exact ⟨transformed, by simpa [sptAListLookup, same] using found, related⟩

/-- Flapjack infrastructure: inlining distinct labels fresh in the old code
preserves each source entry as a related entry in the combined target code. -/
theorem inlineAllSource_related (program : List (Nat × Nat × Bvi.Exp))
    (cache base : Spt (Nat × Bvi.Exp)) (distinct : (program.map Prod.fst).Nodup)
    (subset : sptSubspt cache base) (disjoint : ∀ key, sptMem key base → key ∉ program.map Prod.fst)
    (name arity : Nat) (body : Bvi.Exp) (lookup : sptAListLookup name program = some (arity, body)) :
    ∃ transformed, sptAListLookup name (inlineAllSource cache program).2 = some (arity, transformed) ∧
      ExpRel (sptUnion base (sptFromAList (inlineAllSource cache program).2)) body transformed := by
  let output := (inlineAllSource cache program).2
  let target := sptUnion base (sptFromAList output)
  have targetSubset : sptSubspt cache target :=
    sptSubsptTrans cache base target ⟨subset, sptSubsptUnion base (sptFromAList output)⟩
  have outputDistinct : (output.map Prod.fst).Nodup := by
    dsimp [output]
    rw [inlineAllSource_names]
    exact distinct
  have entries : ∀ key a b, (key, a, b) ∈ output → sptLookup key target = some (a, b) := by
    intro key a b member
    have inOutput : key ∈ output.map Prod.fst := List.mem_map.mpr ⟨(key, a, b), member, rfl⟩
    have inProgram : key ∈ program.map Prod.fst := by
      simpa [output, inlineAllSource_names] using inOutput
    have absent : sptLookup key base = none := by
      cases found : sptLookup key base with
      | none => rfl
      | some value => exact False.elim (disjoint key ((sptMem_iff_lookup key base).2 ⟨value, found⟩) inProgram)
    dsimp [target]
    rw [sptLookup_sptUnion, absent]
    exact BviTailrec.sptFromAList_lookup_of_mem output key (a, b) outputDistinct member
  exact inlineAllSource_related_of_output program cache target targetSubset entries name arity body lookup

/-- Flapjack infrastructure: installing a fresh inlined segment preserves
the relation between source and target code lookups. -/
theorem inlineAllSource_union_related (program : List (Nat × Nat × Bvi.Exp))
    (cache source target : Spt (Nat × Bvi.Exp)) (distinct : (program.map Prod.fst).Nodup)
    (subset : sptSubspt cache target) (disjoint : ∀ key, sptMem key target → key ∉ program.map Prod.fst)
    (oldRelated : ∀ key arity body, sptLookup key source = some (arity, body) →
      ∃ transformed, sptLookup key target = some (arity, transformed) ∧ ExpRel target body transformed) :
    ∀ key arity body, sptLookup key (sptUnion source (sptFromAList program)) = some (arity, body) →
      ∃ transformed, sptLookup key (sptUnion target (sptFromAList (inlineAllSource cache program).2)) =
        some (arity, transformed) ∧
        ExpRel (sptUnion target (sptFromAList (inlineAllSource cache program).2)) body transformed := by
  intro key arity body found
  rw [sptLookup_sptUnion] at found
  cases old : sptLookup key source with
  | some entry =>
    simp [old] at found
    obtain ⟨rfl, rfl⟩ := found.symm
    obtain ⟨transformed, targetFound, related⟩ := oldRelated key arity body old
    refine ⟨transformed, ?_, expRel_mono target _ _ _ related (sptSubsptUnion target _)⟩
    simp [sptLookup_sptUnion, targetFound]
  | none =>
    have listFound : sptAListLookup key program = some (arity, body) := by
      simpa [old, sptLookup_sptFromAList] using found
    obtain ⟨transformed, outputFound, related⟩ :=
      inlineAllSource_related program cache target distinct subset disjoint key arity body listFound
    have member : key ∈ program.map Prod.fst := by
      have present := sptAListLookup_mem key program (arity, body) listFound
      exact List.mem_map.mpr ⟨(key, arity, body), present, rfl⟩
    have targetAbsent : sptLookup key target = none := by
      cases lookup : sptLookup key target with
      | none => rfl
      | some value => exact False.elim (disjoint key ((sptMem_iff_lookup key target).2 ⟨value, lookup⟩) member)
    refine ⟨transformed, ?_, related⟩
    rw [sptLookup_sptUnion, targetAbsent, sptLookup_sptFromAList]
    exact outputFound

end Flapjack.Compiler.Backend.BviInline
