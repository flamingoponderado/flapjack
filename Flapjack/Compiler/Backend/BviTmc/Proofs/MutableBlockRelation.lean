import Flapjack.Compiler.Backend.BviTmc.Proofs.HoleRelation
import Flapjack.FiniteMap.MapKeys

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

/-- A target pointer absent from both the heap and the pointer-map range
cannot represent a source value. -/
private theorem mutableBlockRel_absent (f : HolFiniteMapExact Nat Nat) (old refs : HolFiniteMapExact Nat (Ref Value))
    (source : Value) (b : Bool) (ptr : Nat) (missing : refs.lookup ptr = none)
    (outside : ptr ∉ mapRange f) : ¬mutableBlockRel f old refs source (.refPtr b ptr) := by
  intro related
  cases source with
  | block tag xs =>
    rw [mutableBlockRel.eq_def] at related
    by_cases rejected : b = true ∨ ptr ∈ mapRange f ∨ ptr ∈ old.domain
    · simp [rejected] at related
    · simp only [rejected, if_false] at related
      rw [missing] at related
      exact related
  | refPtr sourceBool sourcePtr =>
    rw [mutableBlockRel.eq_def] at related
    cases related with
    | refPtr _ _ _ found => exact outside ⟨sourcePtr, found⟩
  | _ => rw [mutableBlockRel.eq_def] at related; cases related

private theorem erase_comm {α : Type} (refs : HolFiniteMapExact Nat α) (p q : Nat) :
    (refs.eraseEq p).eraseEq q = (refs.eraseEq q).eraseEq p := by
  apply HolFiniteMapExact.ext_lookup
  intro k
  by_cases hp : k = p <;> by_cases hq : k = q <;>
    simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, hp, hq]

theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_delete_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_delete_old (old : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup old) old.finiteSupport = old := by cases old; rfl
theorem holFmapAsFiniteSupportParamWitness_mutableBlockRel_delete_refs (refs : HolFiniteMapExact Nat (Ref Value)) :
    mapofBroad (maptoBroadlookup refs) refs.finiteSupport = refs := by cases refs; rfl

/-- Removing an unfinished block whose child pointer is fresh preserves any
existing mutable-block relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "mb_rel_del"
  (fmap_as_finite_support_parameters := [f, old, refs])]
theorem mutableBlockRel_delete (f : HolFiniteMapExact Nat Nat) (old : HolFiniteMapExact Nat (Ref Value))
    (refs : HolFiniteMapExact Nat (Ref Value)) (source target : Value) (ptr tag : Nat)
    (left : List Value) (childPtr : Nat) (right : List Value)
    (related : mutableBlockRel f old refs source target)
    (found : refs.lookup ptr = some (.mutBlock tag false left (.refPtr false childPtr) right))
    (childFresh : childPtr ∉ refs.domain) (childOldFresh : childPtr ∉ old.domain)
    (childOutside : childPtr ∉ mapRange f) : mutableBlockRel f old (refs.eraseEq ptr) source target := by
  cases source with
  | block sourceTag xs =>
    cases target with
    | refPtr b q =>
      by_cases invalid : b = true ∨ q ∈ mapRange f ∨ q ∈ old.domain
      · rw [mutableBlockRel.eq_def] at related
        simp [invalid] at related
      · rw [mutableBlockRel.eq_def] at related ⊢
        simp only [invalid, if_false] at related ⊢
        by_cases same : q = ptr
        · subst q
          rw [found] at related
          obtain ⟨_, _, sourceLeft, child, sourceRight, _, _, inner, _⟩ := related
          have missing : (refs.eraseEq ptr).lookup childPtr = none := by
            have orig : refs.lookup childPtr = none := by simpa [HolFiniteMapExact.domain] using childFresh
            by_cases equal : childPtr = ptr <;>
              simp [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, equal, orig]
          exact False.elim ((mutableBlockRel_absent f old (refs.eraseEq ptr) child false childPtr missing childOutside) inner)
        · cases hq : refs.lookup q with
          | none => rw [hq] at related; contradiction
          | some cell =>
            cases cell with
            | mutBlock tag' finalised left' child' right' =>
              rw [hq] at related
              have erasedLookup : (refs.eraseEq ptr).lookup q = some (.mutBlock tag' finalised left' child' right') := by
                simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, same] using hq
              rw [erasedLookup]
              obtain ⟨tagEq, finalEq, sourceLeft, child, sourceRight, shape, lrel, inner, rrel⟩ := related
              refine ⟨tagEq, finalEq, sourceLeft, child, sourceRight, shape, lrel, ?_, rrel⟩
              have found' : (refs.eraseEq q).lookup ptr = some (.mutBlock tag false left (.refPtr false childPtr) right) := by
                have ne : ptr ≠ q := Ne.symm same
                simpa [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, ne] using found
              have fresh' : childPtr ∉ (refs.eraseEq q).domain := by
                have orig : refs.lookup childPtr = none := by simpa [HolFiniteMapExact.domain] using childFresh
                by_cases eq : childPtr = q <;>
                  simp [HolFiniteMapExact.domain, HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, eq, orig]
              have recurse := mutableBlockRel_delete f old (refs.eraseEq q) child child' ptr tag left childPtr right
                inner found' fresh' childOldFresh childOutside
              simpa [erase_comm] using recurse
            | _ => rw [hq] at related; contradiction
    | _ => rw [mutableBlockRel.eq_def] at related ⊢; exact related
  | _ => cases target <;> rw [mutableBlockRel.eq_def] at related ⊢ <;> exact related
termination_by refs.card
decreasing_by
  apply erase_card_lt
  simp [hq]

end Flapjack.Compiler.Backend.BviTmc
