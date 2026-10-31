import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileByteRead

/-! Changing the relocation outside the allocated source reference domain. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

/-- Stored references have the same adjusted contents when relocations agree
on all allocated source addresses. -/
theorem adjustRef_eq_of_stateOk {C F : Type} (first second : Nat → Nat)
    (source : BvlSem.State C F) (key : Nat) (cell : Ref Value)
    (ok : stateOk source) (lookup : source.refs.lookup key = some cell)
    (agree : ∀ ptr, source.refs.lookup ptr ≠ none → first ptr = second ptr) :
    adjustRef first cell = adjustRef second cell := by
  cases cell with
  | valueArray values =>
    have valuesOk : bvOkList source.refs values := by simpa [lookup] using ok.2 key
    simp only [adjustRef, Ref.valueArray.injEq]
    exact adjustMap_eq_of_ok first second values source.refs valuesOk agree
  | thunk mode value =>
    have valueOk : bvOk source.refs value := by simpa [lookup] using ok.2 key
    simp only [adjustRef, Ref.thunk.injEq, true_and]
    exact adjustBv_eq_of_ok first value second source.refs valueOk agree
  | _ => rfl

/-- Replacing a relocation by one that agrees on the source domain preserves
its reference-store relation, assuming well-formed stored values. -/
theorem refsRel_relocate {C F : Type} (first second : Nat → Nat)
    (source : BvlSem.State C F) (target : HolFiniteMapExact Nat (Ref Value))
    (related : refsRel first source.refs target) (ok : stateOk source)
    (agree : ∀ ptr, source.refs.lookup ptr ≠ none → first ptr = second ptr) :
    refsRel second source.refs target := by
  constructor
  · intro ptr present
    rw [← agree ptr present]
    exact related.1 ptr present
  · constructor
    · intro left right leftPresent rightPresent equal
      apply related.2.1 left right leftPresent rightPresent
      simpa [agree left leftPresent, agree right rightPresent] using equal
    · intro ptr cell lookup
      have present : source.refs.lookup ptr ≠ none := by rw [lookup]; simp
      rw [← agree ptr present, ← adjustRef_eq_of_stateOk first second source ptr cell ok lookup agree]
      exact related.2.2 ptr cell lookup

/-- Changing a relocation outside the allocated domain preserves the full
state relation when source globals and stored values are well formed. -/
theorem stateRel_relocate {C F : Type} (first second : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel first source target) (ok : stateOk source)
    (agree : ∀ ptr, source.refs.lookup ptr ≠ none → first ptr = second ptr) :
    stateRel second source target := by
  rcases related with ⟨refs, ffi, globals, rest⟩
  refine ⟨refsRel_relocate first second source target.refs refs ok agree, ffi, ?_, rest⟩
  intro ptr globalPtr
  obtain ⟨separate, size, lookup, bound⟩ := globals ptr globalPtr
  refine ⟨?_, size, ?_, bound⟩
  · intro key present
    rw [← agree key present]
    exact separate key present
  · have globalsEq : source.globals.map (fun value => (value.map (adjustBv first)).getD (.number 0)) =
        source.globals.map (fun value => (value.map (adjustBv second)).getD (.number 0)) := by
      apply List.map_congr_left
      intro item member
      cases item with
      | none => rfl
      | some value =>
        have valueOk : bvOk source.refs value := by simpa using ok.1 (some value) member
        simp only [Option.map, Option.getD]
        exact adjustBv_eq_of_ok first value second source.refs valueOk agree
    rw [← globalsEq]
    exact lookup

/-- Fresh source and target cells can be added to a reference relation when
the relocation maps the new source address to the new target address. -/
theorem refsRel_insertFresh (relocate : Nat → Nat)
    (source target : HolFiniteMapExact Nat (Ref Value)) (key : Nat) (cell : Ref Value)
    (related : refsRel relocate source target)
    (targetFresh : target.lookup (relocate key) = none) :
    refsRel relocate (source.updateEq (key, cell))
      (target.updateEq (relocate key, adjustRef relocate cell)) := by
  have oldDifferent (other : Nat) (present : source.lookup other ≠ none) : relocate other ≠ relocate key := by
    intro equal
    have targetPresent := related.1 other present
    rw [equal, targetFresh] at targetPresent
    exact targetPresent rfl
  constructor
  · intro other present
    by_cases eq : other = key
    · subst other
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have prior : source.lookup other ≠ none := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using present
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, oldDifferent other prior] using related.1 other prior
  · constructor
    · intro left right leftPresent rightPresent equal
      by_cases leq : left = key
      · subst left
        by_cases req : right = key
        · exact req.symm
        · have prior : source.lookup right ≠ none := by
            simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, req] using rightPresent
          exact (oldDifferent right prior equal.symm).elim
      · by_cases req : right = key
        · subst right
          have prior : source.lookup left ≠ none := by
            simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, leq] using leftPresent
          exact (oldDifferent left prior equal).elim
        · have leftOld : source.lookup left ≠ none := by
            simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, leq] using leftPresent
          have rightOld : source.lookup right ≠ none := by
            simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, req] using rightPresent
          exact related.2.1 left right leftOld rightOld equal
    · intro other value lookup
      by_cases eq : other = key
      · subst other
        simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at lookup ⊢
        cases lookup
        rfl
      · have prior : source.lookup other = some value := by
          simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using lookup
        have present : source.lookup other ≠ none := by rw [prior]; simp
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, oldDifferent other present] using
          related.2.2 other value prior

/-- Fresh paired allocations preserve the full state relation, including the
global array, which must already occupy a target reference. -/
theorem stateRel_insertFresh {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (key : Nat) (cell : Ref Value) (related : stateRel relocate source target)
    (targetFresh : target.refs.lookup (relocate key) = none) :
    stateRel relocate { source with refs := source.refs.updateEq (key, cell) }
      { target with refs := target.refs.updateEq (relocate key, adjustRef relocate cell) } := by
  rcases related with ⟨refs, ffi, globals, rest⟩
  refine ⟨refsRel_insertFresh relocate source.refs target.refs key cell refs targetFresh, ffi, ?_, rest⟩
  intro ptr globalPtr
  obtain ⟨separate, size, lookup, bound⟩ := globals ptr globalPtr
  have different : ptr ≠ relocate key := by
    intro equal
    rw [equal, targetFresh] at lookup
    contradiction
  refine ⟨?_, size, ?_, bound⟩
  · intro other present
    by_cases eq : other = key
    · subst other
      exact different
    · apply separate other
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using present
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using lookup

/-- Independently chosen fresh source and target addresses extend the
relocation without changing it on existing source references, and the paired
allocations preserve the state relation. -/
theorem stateRel_allocateFresh {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (sourceKey targetKey : Nat) (cell : Ref Value)
    (related : stateRel relocate source target) (ok : stateOk source)
    (sourceFresh : source.refs.lookup sourceKey = none)
    (targetFresh : target.refs.lookup targetKey = none) :
    ∃ extended : Nat → Nat,
      extended sourceKey = targetKey ∧
      (∀ key, source.refs.lookup key ≠ none → relocate key = extended key) ∧
      stateRel extended { source with refs := source.refs.updateEq (sourceKey, cell) }
        { target with refs := target.refs.updateEq (targetKey, adjustRef extended cell) } := by
  let extended := fun key => if key = sourceKey then targetKey else relocate key
  have same : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
    intro key present
    have different : key ≠ sourceKey := by
      intro equal
      subst key
      exact present sourceFresh
    simp [extended, different]
  have keyEq : extended sourceKey = targetKey := by simp [extended]
  have relatedNew := stateRel_relocate relocate extended source target related ok same
  have newFresh : target.refs.lookup (extended sourceKey) = none := by simpa [keyEq] using targetFresh
  have inserted := stateRel_insertFresh extended source target sourceKey cell relatedNew newFresh
  refine ⟨extended, keyEq, same, ?_⟩
  simpa [keyEq] using inserted

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
