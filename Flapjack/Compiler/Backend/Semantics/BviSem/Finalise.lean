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
end Flapjack.Compiler.Backend.BviSem
