import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineStateRel
import Flapjack.Compiler.Backend.BvlInline.Proofs.ProgramRelation

/-! Code invariants for dynamic BVL installation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl BvlSem

/-- A cache contained in the target code inherits its correspondence with
source code. This helper has no standalone HOL declaration. -/
theorem cacheRelated_of_inStateRel {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) (cache : Spt (Nat × Bvl.Exp))
    (sub : sptSubspt cache target.code) : CacheRelated cache source.code := by
  intro name arity body found
  have targetFound := (sptSubsptLookup cache target.code).1 sub name (arity, body) found
  have targetPresent : sptDomain target.code name :=
    (sptMem_iff_lookup name target.code).2 ⟨(arity, body), targetFound⟩
  have sourcePresent : sptDomain source.code name := by
    rw [← related.2.2.2.2.2.2.2.1]
    exact targetPresent
  obtain ⟨⟨sourceArity, original⟩, sourceFound⟩ :=
    (sptMem_iff_lookup name source.code).1 sourcePresent
  obtain ⟨result, resultFound, resultRel⟩ :=
    related.2.2.2.2.2.2.2.2 name sourceArity original sourceFound
  rw [targetFound] at resultFound
  have equal : (arity, body) = (sourceArity, result) := Option.some.inj resultFound
  cases equal
  exact ⟨original, sourceFound, resultRel⟩

/-- The domain of an association-list tree consists exactly of its labels.
This proof helper has no standalone HOL declaration. -/
theorem fromAList_domain_names (program : List (Nat × Nat × Bvl.Exp)) (name : Nat) :
    sptDomain (sptFromAList program) name ↔ name ∈ program.map Prod.fst := by
  induction program with
  | nil => simp [sptDomain, sptFromAList]
  | cons entry rest ih =>
    obtain ⟨key, arity, body⟩ := entry
    by_cases same : name = key
    · subst name
      simp [sptDomain, sptFromAList, sptLookup_sptInsert_same]
    · simp [sptDomain, sptFromAList, sptLookup_sptInsert_ne key name _ _ same,
        same, ← ih, sptDomain]

/-- The installation freshness check depends only on code domains and program
labels. This helper has no standalone HOL declaration. -/
theorem installFresh_iff (source target : Spt (Nat × Bvl.Exp))
    (program output : List (Nat × Nat × Bvl.Exp))
    (domains : sptDomain target = sptDomain source)
    (names : output.map Prod.fst = program.map Prod.fst) :
    (∀ entry ∈ output, sptLookup entry.1 target = none) ↔
    (∀ entry ∈ program, sptLookup entry.1 source = none) := by
  have absent : ∀ name, sptLookup name target = none ↔ sptLookup name source = none := by
    intro name
    have h := congrFun domains name
    simpa [sptDomain] using congrArg Not h
  constructor
  · intro fresh entry member
    have nameMember : entry.1 ∈ output.map Prod.fst := by
      rw [names]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp nameMember
    apply (absent entry.1).1
    simpa [same] using fresh other otherMember
  · intro fresh entry member
    have nameMember : entry.1 ∈ program.map Prod.fst := by
      rw [← names]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp nameMember
    apply (absent entry.1).2
    simpa [same] using fresh other otherMember

/-- Installing a fresh, distinctly labelled program preserves the code portion
of the inlining state relation, and places the resulting cache within the new
target code. This is a proof helper for the original local application lemma. -/
theorem installCode_preserves {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) (cache finalCache : Spt (Nat × Bvl.Exp))
    (program output : List (Nat × Nat × Bvl.Exp))
    (run : tickCompileProg limit cache program = (finalCache, output))
    (distinct : (program.map Prod.fst).Nodup)
    (cacheSub : sptSubspt cache target.code)
    (fresh : ∀ name, sptDomain source.code name → name ∉ program.map Prod.fst) :
    let sourceCode := sptUnion source.code (sptFromAList program)
    let targetCode := sptUnion target.code (sptFromAList output)
    sptDomain targetCode = sptDomain sourceCode ∧ sptSubspt finalCache targetCode ∧
    ∀ name arity body, sptLookup name sourceCode = some (arity, body) →
      ∃ result, sptLookup name targetCode = some (arity, result) ∧
        ExpRel sourceCode [body] [result] := by
  dsimp only
  have domains := related.2.2.2.2.2.2.2.1
  have targetFresh : ∀ name, sptDomain target.code name → name ∉ program.map Prod.fst := by
    intro name present
    apply fresh name
    rwa [← domains]
  have cacheFresh : ∀ name, sptDomain cache name → name ∉ program.map Prod.fst := by
    intro name present
    exact targetFresh name (cacheSub name present).1
  have disjoint : (fun name => sptDomain target.code name ∧ name ∈ program.map Prod.fst) =
      (fun _ : Nat => False) := by
    funext name
    apply propext
    exact ⟨fun h => targetFresh name h.1 h.2, False.elim⟩
  have range := tickCompileProgResRange program limit output target.code cache finalCache
    ⟨run, distinct, cacheSub, disjoint⟩
  have names : output.map Prod.fst = program.map Prod.fst := by
    have h := mapFstTickInlineAll limit cache program
    change (tickCompileProg limit cache program).2.map Prod.fst = program.map Prod.fst at h
    simpa [run] using h
  refine ⟨?_, range, ?_⟩
  · rw [sptDomain_sptUnion, sptDomain_sptUnion, domains]
    funext name
    apply propext
    rw [fromAList_domain_names output name, fromAList_domain_names program name, names]
  · intro name arity body sourceFound
    rw [sptLookup_sptUnion] at sourceFound
    cases old : sptLookup name source.code with
    | some oldEntry =>
      rw [old] at sourceFound
      have same : oldEntry = (arity, body) := Option.some.inj sourceFound
      subst oldEntry
      obtain ⟨result, targetFound, bodyRel⟩ :=
        related.2.2.2.2.2.2.2.2 name arity body old
      refine ⟨result, ?_, subsptExpRel source.code _ [body] [result]
        (sptSubsptUnion source.code (sptFromAList program)) bodyRel⟩
      rw [sptLookup_sptUnion, targetFound]
    | none =>
      rw [old, sptLookup_sptFromAList] at sourceFound
      have targetAbsent : sptLookup name target.code = none := by
        cases found : sptLookup name target.code with
        | none => rfl
        | some value =>
          have present : sptDomain target.code name :=
            (sptMem_iff_lookup name target.code).2 ⟨value, found⟩
          rw [domains] at present
          simp [sptDomain, old] at present
      obtain ⟨result, resultFound, bodyRel⟩ :=
        tickCompileProg_related limit cache program finalCache output name arity body source.code
          ⟨run, sourceFound, distinct, cacheRelated_of_inStateRel limit source target related cache cacheSub,
            fresh, cacheFresh⟩
      refine ⟨result, ?_, bodyRel⟩
      rw [sptLookup_sptUnion, targetAbsent, sptLookup_sptFromAList, resultFound]

/-- The source and target state updates made by a successful installation
preserve the full inlining relation when the next oracle cache is the one
produced by the compiler. This helper has no standalone HOL declaration. -/
theorem inStateRel_after_install {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target)
    (finalCache : Spt (Nat × Bvl.Exp)) (output : List (Nat × Nat × Bvl.Exp))
    (run : tickCompileProg limit (source.compileOracle 0).1.1 (source.compileOracle 0).2 =
      (finalCache, output))
    (distinct : ((source.compileOracle 0).2.map Prod.fst).Nodup)
    (fresh : ∀ name, sptDomain source.code name →
      name ∉ (source.compileOracle 0).2.map Prod.fst)
    (nextCache : (source.compileOracle 1).1.1 = finalCache) :
    inStateRel limit
      { source with
        code := sptUnion source.code (sptFromAList (source.compileOracle 0).2)
        compileOracle := fun n => source.compileOracle (n + 1) }
      { target with
        code := sptUnion target.code (sptFromAList output)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  have code := installCode_preserves limit source target related (source.compileOracle 0).1.1
    finalCache (source.compileOracle 0).2 output run distinct related.2.2.2.2.2.1 fresh
  rcases code with ⟨domains, range, codeRel⟩
  rcases related with ⟨globals, refs, clock, ffi, oracle, _, compiler, _, _⟩
  refine ⟨globals, refs, clock, ffi, ?_, ?_, compiler, domains, codeRel⟩
  · funext n
    exact congrFun oracle (n + 1)
  · simpa [nextCache] using range

end Flapjack.Compiler.Backend.BvlInline.Proofs
