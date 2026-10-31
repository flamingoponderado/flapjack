import Flapjack.Compiler.Backend.BviTmc.Proofs.MutableBlockRelation
import Flapjack.Compiler.Backend.Semantics.BviSem.Finalise

/-! Weakening the old reference domain in the mutable-block relation. -/
namespace Flapjack.Compiler.Backend.BviTmc.MutableBlockOld
open BviTmc BvlSem

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_old_subset_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_old_subset_larger (larger : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup larger) larger.finiteSupport = larger := by cases larger; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_old_subset_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_old_subset_smaller (smaller : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup smaller) smaller.finiteSupport = smaller := by cases smaller; rfl

/-- A mutable-block relation remains valid when the old domain shrinks. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "mb_rel_refs_old_subset"
  (fmap_as_finite_support_parameters := [f, larger, refs, smaller])]
theorem mutableBlockRel_old_subset (f : HolFiniteMapExact Nat Nat)
    (larger : HolFiniteMapExact Nat (Ref Value)) (refs : HolFiniteMapExact Nat (Ref Value))
    (source target : Value) (smaller : HolFiniteMapExact Nat (Ref Value))
    (related : mutableBlockRel f larger refs source target)
    (subset : smaller.domain ⊆ larger.domain) : mutableBlockRel f smaller refs source target := by
  cases source with
  | block tag xs =>
    cases target with
    | refPtr flag ptr =>
      by_cases invalid : flag = true ∨ ptr ∈ mapRange f ∨ ptr ∈ larger.domain
      · rw [mutableBlockRel.eq_def] at related
        simp [invalid] at related
      · have valid : ¬(flag = true ∨ ptr ∈ mapRange f ∨ ptr ∈ smaller.domain) := by
          intro bad
          rcases bad with h | h | h
          · exact invalid (Or.inl h)
          · exact invalid (Or.inr (Or.inl h))
          · exact invalid (Or.inr (Or.inr (subset h)))
        rw [mutableBlockRel.eq_def] at related ⊢
        simp only [invalid, valid, if_false] at related ⊢
        cases found : refs.lookup ptr with
        | none => rw [found] at related; contradiction
        | some cell =>
          cases cell with
          | mutBlock tag' finalised left child right =>
            rw [found] at related
            simp only at related ⊢
            obtain ⟨tagEq, finalEq, left', child', right', shape, lrel, inner, rrel⟩ := related
            refine ⟨tagEq, finalEq, left', child', right', shape, lrel, ?_, rrel⟩
            exact mutableBlockRel_old_subset f larger (refs.eraseEq ptr) child' child smaller inner subset
          | _ => rw [found] at related; contradiction
    | _ => rw [mutableBlockRel.eq_def] at related ⊢; exact related
  | _ => cases target <;> rw [mutableBlockRel.eq_def] at related ⊢ <;> exact related
termination_by refs.card
decreasing_by
  apply BviSem.card_eraseEq_lt
  simp [found]

end Flapjack.Compiler.Backend.BviTmc.MutableBlockOld
