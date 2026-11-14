module

public import Flapjack.Compiler.Backend.BviInline.Proofs.StateRelation
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section

/-! Cache invariants for BVI program inlining. -/
namespace Flapjack.Compiler.Backend.BviInline

/-- Flapjack infrastructure: a label absent from the input program is not
changed in the threaded inliner cache. -/
private theorem inlineAllSource_cache_untouched (program : List (Nat × Nat × Bvi.Exp))
    (cache : Spt (Nat × Bvi.Exp)) (key : Nat) (absent : key ∉ program.map Prod.fst) :
    sptLookup key (inlineAllSource cache program).1 = sptLookup key cache := by
  induction program generalizing cache with
  | nil => simp [inlineAllSource]
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    simp only [inlineAllSource]
    split
    · rw [ih _ absent.2]
      exact sptLookup_sptInsert_ne name key (arity, inlineExpSource cache body) cache absent.1
    · exact ih _ absent.2

/-- Flapjack infrastructure: a newly cached label with distinct input names
has exactly the corresponding transformed output entry. -/
private theorem inlineAllSource_lookup_new (program : List (Nat × Nat × Bvi.Exp))
    (cache : Spt (Nat × Bvi.Exp)) (key : Nat) (value : Nat × Bvi.Exp)
    (distinct : (program.map Prod.fst).Nodup) (fresh : sptLookup key cache = none)
    (found : sptLookup key (inlineAllSource cache program).1 = some value) :
    sptAListLookup key (inlineAllSource cache program).2 = some value := by
  induction program generalizing cache with
  | nil => simp [inlineAllSource, fresh] at found
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    have distinct' : name ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using distinct
    let body' := inlineExpSource cache body
    let cache' := if canonicalWrapper name arity body' then sptInsert name (arity, body') cache else cache
    have step : inlineAllSource cache ((name, arity, body) :: rest) =
        ((inlineAllSource cache' rest).1, (name, arity, body') :: (inlineAllSource cache' rest).2) := by
      simp [inlineAllSource, body', cache']
    rw [step] at found ⊢
    by_cases same : key = name
    · subst key
      have untouched := inlineAllSource_cache_untouched rest cache' name distinct'.1
      rw [untouched] at found
      by_cases use : canonicalWrapper name arity body' = true
      · have inserted : sptLookup name cache' = some (arity, body') := by
          simp [cache', use, sptLookup_sptInsert_same]
        rw [inserted] at found
        simp only [Option.some.injEq] at found
        subst value
        simp [sptAListLookup]
      · have unchanged : sptLookup name cache' = none := by simp [cache', use, fresh]
        rw [unchanged] at found
        contradiction
    · have fresh' : sptLookup key cache' = none := by
        dsimp [cache']
        split
        · rw [sptLookup_sptInsert_ne name key _ cache same, fresh]
        · exact fresh
      have tail := ih cache' distinct'.2 fresh' found
      simpa [sptAListLookup, same] using tail

/-- Inserting a fresh key preserves inclusion in the union of the old tree
and the singleton entry. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "subspt_insert_union_fresh"]
theorem subsptInsertUnionFresh {α : Type} (cache old : Spt α) (name : Nat) (value : α)
    (premises : sptSubspt cache old ∧ ¬ sptDomain old name) :
    sptSubspt (sptInsert name value cache) (sptUnion old (sptInsert name value .ln)) := by
  obtain ⟨subset, fresh⟩ := premises
  rw [sptSubsptLookup] at subset ⊢
  intro key item found
  by_cases same : key = name
  · subst key
    rw [sptLookup_sptInsert_same] at found
    cases found
    have absent : sptLookup name old = none := by
      cases lookup : sptLookup name old with
      | none => rfl
      | some entry => exact False.elim (fresh (by simp [sptDomain, lookup]))
    simp [sptLookup_sptUnion, absent, sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne name key value cache same] at found
    have oldFound := subset key item found
    simp [sptLookup_sptUnion, oldFound]

/-- The final inlining cache is contained in the old code plus the inlined
output when the original program has distinct, fresh labels. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "inline_all_cache_subspt"]
theorem inlineAllCacheSubspt (program : List (Nat × Nat × Bvi.Exp))
    (cache base finalCache : Spt (Nat × Bvi.Exp)) (output : List (Nat × Nat × Bvi.Exp))
    (premises : inlineAllSource cache program = (finalCache, output) ∧
      sptSubspt cache base ∧ Disjoint {key | key ∈ program.map Prod.fst} (sptDomain base) ∧
      (program.map Prod.fst).Nodup) :
    sptSubspt finalCache (sptUnion base (sptFromAList output)) := by
  obtain ⟨compiled, initialSub, disjoint, distinct⟩ := premises
  have cacheEq : (inlineAllSource cache program).1 = finalCache := congrArg Prod.fst compiled
  have outputEq : (inlineAllSource cache program).2 = output := congrArg Prod.snd compiled
  subst finalCache
  subst output
  have fresh : ∀ key, sptMem key base → key ∉ program.map Prod.fst := by
    intro key present member
    exact Set.disjoint_left.mp disjoint member present
  rw [sptSubsptLookup] at initialSub ⊢
  intro key value found
  by_cases inProgram : key ∈ program.map Prod.fst
  · have baseAbsent : sptLookup key base = none := by
      cases lookup : sptLookup key base with
      | none => rfl
      | some value => exact False.elim (fresh key ((sptMem_iff_lookup key base).2 ⟨value, lookup⟩) inProgram)
    have cacheAbsent : sptLookup key cache = none := by
      cases lookup : sptLookup key cache with
      | none => rfl
      | some value =>
        have present := initialSub key value lookup
        rw [baseAbsent] at present
        contradiction
    have outputFound := inlineAllSource_lookup_new program cache key value distinct cacheAbsent found
    rw [sptLookup_sptUnion, baseAbsent, sptLookup_sptFromAList]
    exact outputFound
  · have untouched := inlineAllSource_cache_untouched program cache key inProgram
    have initialFound : sptLookup key cache = some value := untouched.symm.trans found
    have baseFound := initialSub key value initialFound
    rw [sptLookup_sptUnion, baseFound]

end Flapjack.Compiler.Backend.BviInline
