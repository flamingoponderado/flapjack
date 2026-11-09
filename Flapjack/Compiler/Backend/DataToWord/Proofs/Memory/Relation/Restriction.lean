module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Restriction
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Timestamps

@[expose] public section

/-! Restriction of timestamp maps in reference-cell invariants. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The domain of a restricted map is the intersection of the source domain
and the selected keys. This is Flapjack finite-map infrastructure. -/
theorem mapDomain_restrict (map : HolFiniteMapExact Nat Nat) (keep : Nat → Prop) (key : Nat) :
    mapDomain (restrictTimestampMap map keep) key ↔ keep key ∧ mapDomain map key := by
  constructor
  · rintro ⟨value, lookup⟩
    obtain ⟨selected, source⟩ := (restrictTimestampMap_lookup_some map keep key value).mp lookup
    exact ⟨selected, value, source⟩
  · rintro ⟨selected, value, lookup⟩
    exact ⟨value, (restrictTimestampMap_lookup_some map keep key value).mpr ⟨selected, lookup⟩⟩

/-- On its domain, applying the restricted map agrees with the source map.
This is Flapjack finite-map infrastructure. -/
theorem holFapply_restrict (map : HolFiniteMapExact Nat Nat) (keep : Nat → Prop) (key : Nat)
    (domain : mapDomain (restrictTimestampMap map keep) key) :
    holFapply (restrictTimestampMap map keep) key = holFapply map key := by
  obtain ⟨value, restricted⟩ := domain
  obtain ⟨_, original⟩ := (restrictTimestampMap_lookup_some map keep key value).mp restricted
  rw [holFapply_of_lookup restricted, holFapply_of_lookup original]

/-- Restriction preserves injectivity into a target set. This is Flapjack
finite-map infrastructure. -/
theorem mapInjInto_restrict (map : HolFiniteMapExact Nat Nat) (keep target : Nat → Prop)
    (injective : mapInjInto map target) : mapInjInto (restrictTimestampMap map keep) target := by
  constructor
  · intro key domain
    rw [holFapply_restrict map keep key domain]
    exact injective.1 key ((mapDomain_restrict map keep key).mp domain).2
  · intro x y domains equal
    apply injective.2 x y ⟨((mapDomain_restrict map keep x).mp domains.1).2,
      ((mapDomain_restrict map keep y).mp domains.2).2⟩
    simpa only [holFapply_restrict map keep x domains.1, holFapply_restrict map keep y domains.2] using equal

/-- Split pairwise relations across a prefix of pairs and aligned suffixes.
This is Flapjack list infrastructure for stack rearrangement. -/
theorem forall2_pairPrefix_split {α β : Type} (R : α → β → Prop) (pairs : List (α × β))
    (left : List α) (right : List β)
    (related : List.Forall₂ R (pairs.map Prod.fst ++ left) (pairs.map Prod.snd ++ right)) :
    (∀ pair, pair ∈ pairs → R pair.1 pair.2) ∧ List.Forall₂ R left right := by
  induction pairs with
  | nil => exact ⟨by simp, related⟩
  | cons pair pairs ih =>
      simp only [List.map_cons, List.cons_append] at related
      cases related with
      | cons head tail =>
          obtain ⟨pairwise, suffix⟩ := ih tail
          refine ⟨?_, suffix⟩
          intro candidate member
          rcases List.mem_cons.mp member with equal | inTail
          · subst candidate
            exact head
          · exact pairwise candidate inTail

/-- Build a pairwise relation from a prefix of individually related pairs
and aligned suffixes. This is Flapjack list infrastructure. -/
theorem forall2_pairPrefix_build {α β : Type} (R : α → β → Prop) (pairs : List (α × β))
    (left : List α) (right : List β)
    (pairwise : ∀ pair, pair ∈ pairs → R pair.1 pair.2) (suffix : List.Forall₂ R left right) :
    List.Forall₂ R (pairs.map Prod.fst ++ left) (pairs.map Prod.snd ++ right) := by
  induction pairs with
  | nil => exact suffix
  | cons pair pairs ih =>
      simp only [List.map_cons, List.cons_append]
      refine .cons (pairwise pair (by simp)) ?_
      exact ih (fun candidate member => pairwise candidate (List.mem_cons_of_mem pair member))

/-- Mapping a restricted list and retaining a common suffix preserves list
membership inclusion. This is Flapjack list infrastructure. -/
theorem mapAppend_subset {α β : Type} (project : α → β) (ys xs : List α) (tail : List β)
    (subset : ∀ value, value ∈ ys → value ∈ xs) :
    ∀ value, value ∈ ys.map project ++ tail → value ∈ xs.map project ++ tail := by
  intro value member
  rw [List.mem_append] at member ⊢
  rcases member with fromPrefix | fromTail
  · obtain ⟨item, inYs, equal⟩ := List.mem_map.mp fromPrefix
    exact Or.inl (List.mem_map.mpr ⟨item, subset item inYs, equal⟩)
  · exact Or.inr fromTail

/-- Restricting a timestamp map to the timestamps reachable from the current
references and stack preserves each reference-cell invariant. This Flapjack
helper isolates the reference cases of the source stack-permutation proof. -/
theorem bcRefInv_restrict {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : ValueHeap width) (bigEndian : Bool) (stack : List Value)
    (related : bcRefInv conf n refs (f, tf, heap, bigEndian)) :
    bcRefInv conf n refs (f, restrictTimestampMap tf (allTimestamps refs stack), heap, bigEndian) := by
  cases hmap : f.lookup n with
  | none => simp [bcRefInv, hmap] at related
  | some ptr =>
    cases hcell : sptLookup n refs with
    | none => simp [bcRefInv, hmap, hcell] at related
    | some cell =>
      cases cell with
      | valueArray values =>
          simp only [bcRefInv, hmap, hcell] at related ⊢
          obtain ⟨addresses, found, pair⟩ := related
          refine ⟨addresses, found, ?_⟩
          apply List.Forall₂.flip
          apply forall2_imp_member pair.flip
          intro value addr member valueRelated
          apply valueInv_tfRestrict conf value refs stack addr f tf heap (allTimestamps refs stack)
          refine ⟨valueRelated, ?_, fun _ h => h⟩
          intro ts timestamp
          apply mem_allTimestamps value ts stack refs
          exact ⟨Or.inl ⟨n, values, hcell, mem_valueListValues values value member⟩, timestamp⟩
      | byteArray compare bytes =>
          simpa only [bcRefInv, hmap, hcell] using related
      | thunk mode value =>
          simp only [bcRefInv, hmap, hcell] at related ⊢
          obtain ⟨addr, found, safe, valueRelated⟩ := related
          refine ⟨addr, found, safe, ?_⟩
          apply valueInv_tfRestrict conf value refs stack addr f tf heap (allTimestamps refs stack)
          exact ⟨valueRelated, fun ts member => thunkTimestampInAll refs stack n mode value hcell ts member,
            fun _ h => h⟩
      | mutBlock tag finalised left child right =>
          simp only [bcRefInv, hmap, hcell] at related ⊢
          obtain ⟨gc, fresh, addresses, found, pair⟩ := related
          refine ⟨gc, ?_, addresses, found, ?_⟩
          · intro unfinished ⟨stamp, ⟨address, restricted⟩, atPointer⟩
            have original := (restrictTimestampMap_lookup_some tf (allTimestamps refs stack) stamp address).mp restricted
            apply fresh unfinished
            refine ⟨stamp, ⟨address, original.2⟩, ?_⟩
            rw [holFapply_of_lookup restricted] at atPointer
            rw [holFapply_of_lookup original.2]
            exact atPointer
          · apply List.Forall₂.flip
            apply forall2_imp_member pair.flip
            intro value addr member valueRelated
            apply valueInv_tfRestrict conf value refs stack addr f tf heap (allTimestamps refs stack)
            refine ⟨valueRelated, ?_, fun _ h => h⟩
            intro ts timestamp
            apply mem_allTimestamps value ts stack refs
            exact ⟨Or.inr (Or.inr (Or.inl
              ⟨n, tag, finalised, left, child, right, hcell,
                mem_valueListValues (left ++ [child] ++ right) value member⟩)), timestamp⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
