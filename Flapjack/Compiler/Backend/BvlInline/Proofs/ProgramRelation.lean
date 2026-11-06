import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramCache
import Flapjack.Compiler.Backend.BvlInline.Proofs.TickInlineRel

/-! Expression relations preserved by BVL program inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl

/-- A traversal maintains the source relation when every input entry is
already present in the source code. This is a proof helper, not a HOL declaration. -/
theorem tickCompileProg_related_of_entries (limit : Nat)
    (program : List (Nat × Nat × Exp)) (source : Spt (Nat × Exp))
    (cache : Spt (Nat × Exp))
    (entries : ∀ name arity body, (name, arity, body) ∈ program →
      sptLookup name source = some (arity, body))
    (compatible : CacheRelated cache source) :
    ∀ key arity body, sptAListLookup key program = some (arity, body) →
      ∃ body', sptAListLookup key (tickCompileProg limit cache program).2 = some (arity, body') ∧
        ExpRel source [body] [body'] := by
  induction program generalizing cache with
  | nil => simp [sptAListLookup]
  | cons entry rest ih =>
    obtain ⟨name, argCount, original⟩ := entry
    let transformed := tickInlineSing cache original
    let nextCache := if mustInline name limit transformed then
      sptInsert name (argCount, transformed) cache else cache
    have rel : ExpRel source [original] [transformed] := by
      simpa [transformed, tickInline, tickInlineList] using
        expRelTickInline cache [original] source compatible
    have entryFound : sptLookup name source = some (argCount, original) :=
      entries name argCount original (by simp)
    have nextCompatible : CacheRelated nextCache source := by
      intro k a body found
      dsimp [nextCache] at found
      split at found
      · by_cases same : k = name
        · subst k
          rw [sptLookup_sptInsert_same] at found
          cases found
          exact ⟨original, entryFound, rel⟩
        · rw [sptLookup_sptInsert_ne name k _ cache same] at found
          exact compatible k a body found
      · exact compatible k a body found
    have restEntries : ∀ name arity body, (name, arity, body) ∈ rest →
        sptLookup name source = some (arity, body) := by
      intro n a b member
      exact entries n a b (List.mem_cons_of_mem _ member)
    have step : tickCompileProg limit cache ((name, argCount, original) :: rest) =
        ((tickCompileProg limit nextCache rest).1,
          (name, argCount, transformed) :: (tickCompileProg limit nextCache rest).2) := by
      simpa [transformed, nextCache] using tickCompileProg_cons limit cache name argCount original rest
    intro key arity body found
    rw [step]
    by_cases same : key = name
    · subst key
      simp [sptAListLookup] at found
      rcases found with ⟨rfl, rfl⟩
      exact ⟨transformed, by simp [sptAListLookup], rel⟩
    · have tailFound : sptAListLookup key rest = some (arity, body) := by
        simpa [sptAListLookup, same] using found
      obtain ⟨body', outputFound, bodyRel⟩ := ih nextCache restEntries nextCompatible key arity body tailFound
      exact ⟨body', by simpa [sptAListLookup, same] using outputFound, bodyRel⟩

/-- Distinct input labels make each member visible to association-list lookup.
This helper has no standalone HOL declaration. -/
theorem sptAListLookup_of_mem_nodup (program : List (Nat × Nat × Exp))
    (distinct : (program.map Prod.fst).Nodup) (name arity : Nat) (body : Exp)
    (member : (name, arity, body) ∈ program) :
    sptAListLookup name program = some (arity, body) := by
  induction program with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨head, headArity, headBody⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.mem_cons] at member
    rcases member with same | member
    · cases same
      simp [sptAListLookup]
    · have different : name ≠ head := by
        intro same
        apply distinct.1
        rw [← same]
        exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
      simpa [sptAListLookup, different] using ih distinct.2 member

/-- Program inlining preserves the expression relation for an input lookup.
The HOL theorem is local; its original proof and inferred types are replayed
in the BVL inlining state-relation probe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "tick_compile_prog_IMP_exp_rel"]
theorem tickCompileProg_related (limit : Nat) (cache : Spt (Nat × Exp))
    (program : List (Nat × Nat × Exp)) (finalCache : Spt (Nat × Exp))
    (output : List (Nat × Nat × Exp)) (key arity : Nat) (body : Exp)
    (source : Spt (Nat × Exp))
    (h : tickCompileProg limit cache program = (finalCache, output) ∧
      sptAListLookup key program = some (arity, body) ∧
      (program.map Prod.fst).Nodup ∧ CacheRelated cache source ∧
      (∀ name, sptDomain source name → name ∉ program.map Prod.fst) ∧
      (∀ name, sptDomain cache name → name ∉ program.map Prod.fst)) :
    ∃ result, sptAListLookup key output = some (arity, result) ∧
      ExpRel (sptUnion source (sptFromAList program)) [body] [result] := by
  rcases h with ⟨run, found, distinct, compatible, sourceFresh, _cacheFresh⟩
  let extended := sptUnion source (sptFromAList program)
  have sub : sptSubspt source extended := sptSubsptUnion source (sptFromAList program)
  have compatible' : CacheRelated cache extended := by
    intro name a v lookup
    obtain ⟨original, sourceFound, related⟩ := compatible name a v lookup
    exact ⟨original, (sptSubsptLookup source extended).1 sub name (a, original) sourceFound,
      subsptExpRel source extended [original] [v] sub related⟩
  have entries : ∀ name a b, (name, a, b) ∈ program →
      sptLookup name extended = some (a, b) := by
    intro name a b member
    have inNames : name ∈ program.map Prod.fst :=
      List.mem_map.mpr ⟨(name, a, b), member, rfl⟩
    have absent : sptLookup name source = none := by
      cases lookup : sptLookup name source with
      | none => rfl
      | some value =>
        have present : sptDomain source name := (sptMem_iff_lookup name source).2 ⟨value, lookup⟩
        exact False.elim (sourceFresh name present inNames)
    dsimp [extended]
    rw [sptLookup_sptUnion, absent, sptLookup_sptFromAList]
    exact sptAListLookup_of_mem_nodup program distinct name a b member
  obtain ⟨result, resultFound, related⟩ :=
    tickCompileProg_related_of_entries limit program extended cache entries compatible' key arity body found
  rw [run] at resultFound
  exact ⟨result, resultFound, related⟩

end Flapjack.Compiler.Backend.BvlInline.Proofs
