import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation

/-! Recursive relation between immutable source blocks and mutable TMC blocks. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private theorem erase_card_lt {α : Type} (refs : HolFiniteMapExact Nat α) (ptr : Nat)
    (present : refs.lookup ptr ≠ none) : (refs.eraseEq ptr).card < refs.card := by
  classical
  unfold HolFiniteMapExact.card
  have member : ptr ∈ refs.domain_finite.toFinset := by
    simpa [HolFiniteMapExact.domain] using present
  have erased : (refs.eraseEq ptr).domain_finite.toFinset = refs.domain_finite.toFinset.erase ptr := by
    ext key
    simp only [Set.Finite.mem_toFinset, Finset.mem_erase]
    by_cases equal : key = ptr
    · subst key; simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL]
    · simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, equal]
  rw [erased]
  exact Finset.card_erase_lt_of_mem member

private def maptoBroadlookup {α β : Type} (f : HolFiniteMapExact α β) : α → Option β := f.lookup
private def mapofBroad {α β : Type} (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact α β :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_old (old : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup old) old.finiteSupport = old := by cases old; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Relate a source value to an unfinished chain of target mutable blocks,
removing each visited pointer to make cyclic structures fail. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "mb_rel_def"
  (fmap_as_finite_support_parameters := [f, old, refs])]
noncomputable def mutableBlockRel (f : HolFiniteMapExact Nat Nat) (old : HolFiniteMapExact Nat (Ref Value))
    (refs : HolFiniteMapExact Nat (Ref Value)) (source target : Value) : Prop := by
  classical
  exact match source, target with
  | .block tag xs, .refPtr b ptr =>
    if b = true ∨ ptr ∈ mapRange f ∨ ptr ∈ old.domain then False
    else match h : refs.lookup ptr with
      | some (.mutBlock tag' finalised left' child' right') =>
        tag = tag' ∧ finalised = false ∧ ∃ left child right,
          xs = left ++ [child] ++ right ∧ List.Forall₂ (valueRel f) left left' ∧
          mutableBlockRel f old (refs.eraseEq ptr) child child' ∧ List.Forall₂ (valueRel f) right right'
      | _ => False
  | _, _ => valueRel f source target
termination_by refs.card
decreasing_by
  apply erase_card_lt
  simp [h]

theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_cons_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_cons_old (old : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup old) old.finiteSupport = old := by cases old; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_cons_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- A fresh unfinished mutable block extends a related child and related
left and right fields to a related source constructor. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "mb_rel_cons"
  (fmap_as_finite_support_parameters := [f, old, refs])]
theorem mutableBlockRel_cons (f : HolFiniteMapExact Nat Nat) (old : HolFiniteMapExact Nat (Ref Value))
    (refs : HolFiniteMapExact Nat (Ref Value)) (ptr tag : Nat) (left left' : List Value)
    (child child' : Value) (right right' : List Value)
    (inner : mutableBlockRel f old (refs.eraseEq ptr) child child')
    (leftRelated : List.Forall₂ (valueRel f) left left') (rightRelated : List.Forall₂ (valueRel f) right right')
    (found : refs.lookup ptr = some (.mutBlock tag false left' child' right'))
    (outsideRange : ptr ∉ mapRange f) (outsideOld : ptr ∉ old.domain) :
    mutableBlockRel f old refs (.block tag (left ++ [child] ++ right)) (.refPtr false ptr) := by
  rw [mutableBlockRel.eq_def]
  simp only [Bool.false_eq_true, outsideRange, outsideOld, or_self, ↓reduceIte]
  rw [found]
  simp only [true_and]
  exact ⟨left, child, right, rfl, leftRelated, inner, rightRelated⟩

end Flapjack.Compiler.Backend.BviTmc
