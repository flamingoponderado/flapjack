import Flapjack.Compiler.Backend.Semantics.BviSem.Thunk
import Flapjack.FiniteMap.CardinalityExact
/-! Finite-map recursion for BVI mutable-constructor finalisation. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

/-- Removing an existing key decreases the exact finite-map domain. -/
theorem card_eraseEq_lt {α β : Type} [DecidableEq α] (map : HolFiniteMapExact α β)
    (key : α) (present : map.lookup key ≠ none) : (map.eraseEq key).card < map.card := by
  classical
  have member : key ∈ map.domain_finite.toFinset := by
    simpa [HolFiniteMapExact.domain] using present
  have domainEq : (map.eraseEq key).domain_finite.toFinset = map.domain_finite.toFinset.erase key := by
    ext query
    simp [HolFiniteMapExact.domain, HolFiniteMapExact.eraseEq, FDOMSUB_HOL]
  unfold HolFiniteMapExact.card
  rw [domainEq, Finset.card_erase_of_mem member]
  have positive := Finset.card_pos.mpr ⟨key, member⟩
  omega

/-- Finalise mutable constructor chains, removing each visited reference
while descending. Untagged until the nested finite-map function/result
representation has an approved independent lookup witness. -/
noncomputable def finaliseCons (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (Value × HolFiniteMapExact Nat (Ref Value)) :=
  match value with
  | .refPtr flag ptr =>
    match _found : refs.lookup ptr with
    | some (.mutBlock tag finalised left child right) =>
      if finalised then none else
        match finaliseCons child (refs.eraseEq ptr) with
        | none => none
        | some (result, rest) =>
          some (.block tag (left ++ [result] ++ right),
            rest.updateEq (ptr, .mutBlock tag true left child right))
    | some _ => some (.refPtr flag ptr, refs)
    | none => none
  | other => some (other, refs)
termination_by refs.card
decreasing_by
  apply card_eraseEq_lt
  simp [_found]
/-- Flapjack infrastructure: successful finalisation restores every removed
key and preserves the reference domain. This supports the evaluator's domain
growth proof; it is not a separate HOL declaration. -/
theorem finaliseCons_domain (value result : Value) (refs rest : HolFiniteMapExact Nat (Ref Value))
    (run : finaliseCons value refs = some (result, rest)) :
    ∀ key, refs.lookup key ≠ none ↔ rest.lookup key ≠ none := by
  have all : ∀ n : Nat, ∀ (value result : Value) (refs rest : HolFiniteMapExact Nat (Ref Value)),
      refs.card = n → finaliseCons value refs = some (result, rest) →
      ∀ key, refs.lookup key ≠ none ↔ rest.lookup key ≠ none := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro value result refs rest size run key
      cases value with
      | refPtr flag ptr =>
        rw [finaliseCons.eq_def] at run
        dsimp only at run
        cases found : refs.lookup ptr with
        | none => rw [found] at run; contradiction
        | some entry =>
          rw [found] at run
          cases entry with
          | mutBlock tag finalised left child right =>
            cases finalised with
            | true => simp at run
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at run
              cases recursive : finaliseCons child (refs.eraseEq ptr) with
              | none => simp [recursive] at run
              | some pair =>
                obtain ⟨childResult, childRest⟩ := pair
                simp only [recursive, Option.some.injEq, Prod.mk.injEq] at run
                obtain ⟨_, rfl⟩ := run
                have smaller : (refs.eraseEq ptr).card < n := by
                  rw [← size]
                  exact card_eraseEq_lt refs ptr (by simp [found])
                have domain := ih (refs.eraseEq ptr).card smaller child childResult
                  (refs.eraseEq ptr) childRest rfl recursive key
                by_cases same : key = ptr
                · subst key
                  simp [found, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
                · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
                    HolFiniteMapExact.eraseEq, FDOMSUB_HOL, same] using domain
          | _ => simp at run; obtain ⟨_, rfl⟩ := run; rfl
      | _ => simp [finaliseCons.eq_def] at run; obtain ⟨_, rfl⟩ := run; rfl
  exact all refs.card value result refs rest rfl run

end Flapjack.Compiler.Backend.BviSem
