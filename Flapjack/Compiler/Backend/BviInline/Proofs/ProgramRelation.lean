module

public import Flapjack.Compiler.Backend.BviInline.Proofs.ProgramCache
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeRelation

@[expose] public section

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

/-- Inlining a distinct program with labels fresh in the old target preserves
each association-list lookup as a related output lookup. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_ALOOKUP"]
theorem inlineAllALookup (program : List (Nat × Nat × Bvi.Exp))
    (cache base finalCache : Spt (Nat × Bvi.Exp)) (output : List (Nat × Nat × Bvi.Exp))
    (name arity : Nat) (body : Bvi.Exp)
    (premises : inlineAllSource cache program = (finalCache, output) ∧
      sptSubspt cache base ∧ Disjoint {key | key ∈ program.map Prod.fst} (sptDomain base) ∧
      (program.map Prod.fst).Nodup ∧ sptAListLookup name program = some (arity, body)) :
    ∃ transformed, sptAListLookup name output = some (arity, transformed) ∧
      ExpRel (sptUnion base (sptFromAList output)) body transformed := by
  obtain ⟨compiled, subset, disjoint, distinct, lookup⟩ := premises
  have outEq : (inlineAllSource cache program).2 = output := congrArg Prod.snd compiled
  subst output
  have fresh : ∀ key, sptMem key base → key ∉ program.map Prod.fst := by
    intro key present member
    exact Set.disjoint_left.mp disjoint member present
  let output := (inlineAllSource cache program).2
  let target := sptUnion base (sptFromAList output)
  have targetSubset : sptSubspt cache target :=
    sptSubsptTrans cache base target ⟨subset, sptSubsptUnion base (sptFromAList output)⟩
  have outputDistinct : (output.map Prod.fst).Nodup := by
    dsimp [output]
    rw [Proofs.inlineAll_mapFst]
    exact distinct
  have entries : ∀ key a b, (key, a, b) ∈ output → sptLookup key target = some (a, b) := by
    intro key a b member
    have inOutput : key ∈ output.map Prod.fst := List.mem_map.mpr ⟨(key, a, b), member, rfl⟩
    have inProgram : key ∈ program.map Prod.fst := by
      simpa [output, Proofs.inlineAll_mapFst] using inOutput
    have absent : sptLookup key base = none := by
      cases found : sptLookup key base with
      | none => rfl
      | some value => exact False.elim (fresh key ((sptMem_iff_lookup key base).2 ⟨value, found⟩) inProgram)
    dsimp [target]
    rw [sptLookup_sptUnion, absent]
    exact BviTailrec.sptFromAList_lookup_of_mem output key (a, b) outputDistinct member
  exact inlineAllSource_related_of_output program cache target targetSubset entries name arity body lookup

/-- Inlining a nonempty program preserves its first label and the labels of
the remaining entries. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_head_names"]
theorem inlineAllHeadNames (cache finalCache : Spt (Nat × Bvi.Exp))
    (name arity : Nat) (body : Bvi.Exp) (rest output : List (Nat × Nat × Bvi.Exp))
    (compiled : inlineAllSource cache ((name, arity, body) :: rest) = (finalCache, output)) :
    ∃ tail, output = (name, arity, inlineExpSource cache body) :: tail ∧
      tail.map Prod.fst = rest.map Prod.fst := by
  let body' := inlineExpSource cache body
  let cache' := if canonicalWrapper name arity body' then sptInsert name (arity, body') cache else cache
  have step : inlineAllSource cache ((name, arity, body) :: rest) =
      ((inlineAllSource cache' rest).1, (name, arity, body') :: (inlineAllSource cache' rest).2) := by
    simp [inlineAllSource, body', cache']
  rw [step] at compiled
  have outEq := congrArg Prod.snd compiled
  refine ⟨(inlineAllSource cache' rest).2, ?_, Proofs.inlineAll_mapFst cache' rest⟩
  exact outEq.symm

/-- Inlining a fresh segment preserves the relation between source and target
code lookups after their respective unions. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_lookup_union"]
theorem inlineAllLookupUnion (cache : Spt (Nat × Bvi.Exp))
    (program : List (Nat × Nat × Bvi.Exp)) (finalCache : Spt (Nat × Bvi.Exp))
    (output : List (Nat × Nat × Bvi.Exp)) (source target : Spt (Nat × Bvi.Exp))
    (premises : inlineAllSource cache program = (finalCache, output) ∧
      sptSubspt cache target ∧ sptDomain target = sptDomain source ∧
      (∀ key arity body, sptLookup key source = some (arity, body) →
        ∃ transformed, sptLookup key target = some (arity, transformed) ∧ ExpRel target body transformed) ∧
      Disjoint {key | key ∈ program.map Prod.fst} (sptDomain target) ∧
      (program.map Prod.fst).Nodup) :
    ∀ key arity body, sptLookup key (sptUnion source (sptFromAList program)) = some (arity, body) →
      ∃ transformed, sptLookup key (sptUnion target (sptFromAList output)) =
        some (arity, transformed) ∧ ExpRel (sptUnion target (sptFromAList output)) body transformed := by
  obtain ⟨compiled, subset, _domains, oldRelated, disjoint, distinct⟩ := premises
  have outEq : (inlineAllSource cache program).2 = output := congrArg Prod.snd compiled
  subst output
  have fresh : ∀ key, sptMem key target → key ∉ program.map Prod.fst := by
    intro key present member
    exact Set.disjoint_left.mp disjoint member present
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
      inlineAllALookup program cache target (inlineAllSource cache program).1
        (inlineAllSource cache program).2 key arity body
        ⟨(Prod.eta _).symm, subset, disjoint, distinct, listFound⟩
    have member : key ∈ program.map Prod.fst := by
      have present := sptAListLookup_mem key program (arity, body) listFound
      exact List.mem_map.mpr ⟨(key, arity, body), present, rfl⟩
    have targetAbsent : sptLookup key target = none := by
      cases lookup : sptLookup key target with
      | none => rfl
      | some value => exact False.elim (fresh key ((sptMem_iff_lookup key target).2 ⟨value, lookup⟩) member)
    refine ⟨transformed, ?_, related⟩
    rw [sptLookup_sptUnion, targetAbsent, sptLookup_sptFromAList]
    exact outputFound

end Flapjack.Compiler.Backend.BviInline
