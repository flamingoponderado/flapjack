module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateValue
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Restriction
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateRefInv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapStore

@[expose] public section

/-! Timestamp-map restriction after value-array updates. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A value that remains directly stored or on the stack retains its value
invariant after an array update and restriction of the timestamp map. -/
theorem valueInv_arrayUpdate_restrict {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr : Nat) (old replacement stack : List Value)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (value : Value)
    (found : sptLookup ptr refs = some (.valueArray old)) (heapInv : refBlockInv heap heap2)
    (related : valueInv conf value refs (address, f, tf, heap))
    (observed : (∃ index cell, sptLookup index (sptInsert ptr (.valueArray replacement) refs) = some cell ∧
      findRef cell value) ∨ value ∈ stack) :
    valueInv conf value (sptInsert ptr (.valueArray replacement) refs)
      (address, f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack), heap2) := by
  have updated := valueInv_insertValueArray conf value refs address f tf heap ptr replacement heap2
    ⟨heapInv, related, fun _ => ⟨old, found⟩⟩
  apply valueInv_tfRestrict conf value _ stack address f tf heap2 _
  exact ⟨updated, fun stamp member => ⟨value, observed, member⟩, fun _ member => member⟩

/-- A pairwise stack value relation survives the update and the corresponding
timestamp restriction, with the same stack and heap-address roots. -/
theorem valueListInv_arrayUpdate_restrict {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr : Nat) (old replacement stack : List Value)
    (addresses : List (HeapAddress (WordLocW width))) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (found : sptLookup ptr refs = some (.valueArray old)) (heapInv : refBlockInv heap heap2)
    (related : List.Forall₂ (fun value address => valueInv conf value refs (address, f, tf, heap)) stack addresses) :
    List.Forall₂ (fun value address => valueInv conf value (sptInsert ptr (.valueArray replacement) refs)
      (address, f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack), heap2))
      stack addresses := by
  apply forall2_imp_member related
  intro value address member valueInv
  exact valueInv_arrayUpdate_restrict conf refs ptr old replacement stack address f tf heap heap2 value
    found heapInv valueInv (Or.inr member)

/-- Each element of an updated value-array cell remains related under the
restricted timestamp map whenever its original value invariant holds. -/
theorem valueArrayInv_arrayUpdate_restrict {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr : Nat) (old replacement stack : List Value)
    (addresses : List (HeapAddress (WordLocW width))) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (found : sptLookup ptr refs = some (.valueArray old)) (heapInv : refBlockInv heap heap2)
    (related : List.Forall₂ (fun value address => valueInv conf value refs (address, f, tf, heap)) replacement addresses) :
    List.Forall₂ (fun value address => valueInv conf value (sptInsert ptr (.valueArray replacement) refs)
      (address, f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack), heap2))
      replacement addresses := by
  apply forall2_imp_member related
  intro value address member valueInv
  apply valueInv_arrayUpdate_restrict conf refs ptr old replacement stack address f tf heap heap2 value found heapInv valueInv
  left
  exact ⟨ptr, .valueArray replacement, sptLookup_sptInsert_same _ _ _, member⟩

/-- Restriction can only remove map entries and preserves their mapped
values. This is used for the mutable-block freshness condition. -/
theorem restrictTimestampMap_domain_apply (tf : HolFiniteMapExact Nat Nat) (keep : Nat → Prop) (key : Nat)
    (domain : mapDomain (restrictTimestampMap tf keep) key) :
    mapDomain tf key ∧ holFapply (restrictTimestampMap tf keep) key = holFapply tf key := by
  obtain ⟨mapped, lookup⟩ := domain
  obtain ⟨_, oldLookup⟩ := (restrictTimestampMap_lookup_some tf keep key mapped).mp lookup
  exact ⟨⟨mapped, oldLookup⟩, (holFapply_of_lookup lookup).trans (holFapply_of_lookup oldLookup).symm⟩

/-- A distinct reference cell retains its full invariant after updating the
array, replacing its heap reference block, and restricting timestamps. -/
theorem bcRefInv_arrayUpdate_other {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (before after : List (HeapAddress (WordLocW width)))
    (be : Bool) (ptr index : Nat) (old replacement stack : List Value)
    (sameLength : before.length = after.length) (found : sptLookup ptr refs = some (.valueArray old))
    (ptrMap : f.lookup ptr = some (heapLength pre))
    (injective : mapInjInto f (fun addr => isSomeDataElement (heapLookup addr (pre ++ [refBlock before] ++ post))))
    (different : index ≠ ptr)
    (valid : bcRefInv conf index refs (f, tf, pre ++ [refBlock before] ++ post, be)) :
    bcRefInv conf index (sptInsert ptr (.valueArray replacement) refs)
      (f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack),
        pre ++ [refBlock after] ++ post, be) := by
  have lookupRefs : sptLookup index (sptInsert ptr (.valueArray replacement) refs) = sptLookup index refs :=
    sptLookup_sptInsert_ne ptr index _ refs different
  have heapInv := refBlockInv_replace pre post before after sameLength
  cases fLookup : f.lookup index with
  | none => simp [bcRefInv, fLookup] at valid
  | some mapped =>
    have addressNe := byteUpdate_mappedAddress_ne f pre _ ptr index mapped ptrMap fLookup injective different
    have sameSize : elLength (refBlock before : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
        elLength (refBlock after : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) := by
      simp [refBlock, elLength, sameLength]
    have unchanged : heapLookup mapped (pre ++ [refBlock before] ++ post) =
        heapLookup mapped (pre ++ [refBlock after] ++ post) :=
      heapLookup_replace_ne pre post _ _ sameSize mapped addressNe
    cases refLookup : sptLookup index refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨addresses, cell, valuesInv⟩ := valid
        refine ⟨addresses, unchanged ▸ cell, ?_⟩
        apply List.Forall₂.flip
        apply forall2_imp_member valuesInv.flip
        intro value addr member related
        apply valueInv_arrayUpdate_restrict conf refs ptr old replacement stack addr f tf _ _ value found heapInv related
        left
        exact ⟨index, .valueArray values, by rw [lookupRefs, refLookup], member⟩
      | byteArray flag bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        exact unchanged ▸ valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨addr, cell, safe, valueInv⟩ := valid
        refine ⟨addr, unchanged ▸ cell, ?_, ?_⟩
        · intro evaluated
          exact destThunk_notThunk_insertValueArray value refs ptr replacement (safe evaluated)
        · apply valueInv_arrayUpdate_restrict conf refs ptr old replacement stack addr f tf _ _ value found heapInv valueInv
          left
          exact ⟨index, .thunk mode value, by rw [lookupRefs, refLookup], rfl⟩
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fLookup, lookupRefs, refLookup]
        obtain ⟨gen, fresh, addresses, cell, valuesInv⟩ := valid
        refine ⟨gen, ?_, addresses, unchanged ▸ cell, ?_⟩
        · intro notFinal ⟨stamp, domain, maps⟩
          obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ stamp domain
          exact fresh notFinal ⟨stamp, oldDomain, sameApply.symm.trans maps⟩
        · apply List.Forall₂.flip
          apply forall2_imp_member valuesInv.flip
          intro item addr member related
          apply valueInv_arrayUpdate_restrict conf refs ptr old replacement stack addr f tf _ _ item found heapInv related
          left
          exact ⟨index, .mutBlock tag finalised left value right, by rw [lookupRefs, refLookup], member⟩

/-- The updated reference cell satisfies its invariant when the replacement
values are related to the new reference-block pointers. -/
theorem bcRefInv_arrayUpdate_here {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (before after : List (HeapAddress (WordLocW width)))
    (be : Bool) (ptr : Nat) (old replacement stack : List Value)
    (sameLength : before.length = after.length) (found : sptLookup ptr refs = some (.valueArray old))
    (ptrMap : f.lookup ptr = some (heapLength pre))
    (valuesInv : List.Forall₂ (fun value address => valueInv conf value refs
      (address, f, tf, pre ++ [refBlock before] ++ post)) replacement after) :
    bcRefInv conf ptr (sptInsert ptr (.valueArray replacement) refs)
      (f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack),
        pre ++ [refBlock after] ++ post, be) := by
  simp only [bcRefInv, ptrMap, sptLookup_sptInsert_same]
  refine ⟨after, heapLookup_refBlock_here pre post after, ?_⟩
  exact (valueArrayInv_arrayUpdate_restrict conf refs ptr old replacement stack after f tf _ _ found
    (refBlockInv_replace pre post before after sameLength) valuesInv).flip

/-- All reference cells retain their invariants after a value-array update,
including the changed cell and all other reference kinds. -/
theorem bcRefInv_arrayUpdate {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post : ValueHeap width) (before after : List (HeapAddress (WordLocW width)))
    (be : Bool) (ptr index : Nat) (old replacement stack : List Value)
    (sameLength : before.length = after.length) (found : sptLookup ptr refs = some (.valueArray old))
    (ptrMap : f.lookup ptr = some (heapLength pre))
    (injective : mapInjInto f (fun addr => isSomeDataElement (heapLookup addr (pre ++ [refBlock before] ++ post))))
    (valuesInv : List.Forall₂ (fun value address => valueInv conf value refs
      (address, f, tf, pre ++ [refBlock before] ++ post)) replacement after)
    (valid : bcRefInv conf index refs (f, tf, pre ++ [refBlock before] ++ post, be)) :
    bcRefInv conf index (sptInsert ptr (.valueArray replacement) refs)
      (f, restrictTimestampMap tf (allTimestamps (sptInsert ptr (.valueArray replacement) refs) stack),
        pre ++ [refBlock after] ++ post, be) := by
  by_cases same : index = ptr
  · subst index
    exact bcRefInv_arrayUpdate_here conf refs f tf pre post before after be ptr old replacement stack sameLength found ptrMap valuesInv
  · exact bcRefInv_arrayUpdate_other conf refs f tf pre post before after be ptr index old replacement stack
      sameLength found ptrMap injective same valid

/-- Restricting an injective timestamp map and replacing a same-sized
reference block preserves injectivity into the new heap's data cells. -/
theorem mapInjInto_arrayUpdate_restrict {width : Nat} [NeZero width]
    (tf : HolFiniteMapExact Nat Nat) (keep : Nat → Prop) (pre post : ValueHeap width)
    (before after : List (HeapAddress (WordLocW width))) (sameLength : before.length = after.length)
    (valid : mapInjInto tf (fun addr => isSomeDataElement (heapLookup addr (pre ++ [refBlock before] ++ post)))) :
    mapInjInto (restrictTimestampMap tf keep)
      (fun addr => isSomeDataElement (heapLookup addr (pre ++ [refBlock after] ++ post))) := by
  refine ⟨?_, ?_⟩
  · intro key domain
    obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf keep key domain
    rw [sameApply]
    exact (refBlock_replace_isSomeData pre post before after sameLength _).mp (valid.1 key oldDomain)
  · intro x y ⟨domainX, domainY⟩ equal
    obtain ⟨oldX, sameX⟩ := restrictTimestampMap_domain_apply tf keep x domainX
    obtain ⟨oldY, sameY⟩ := restrictTimestampMap_domain_apply tf keep y domainY
    apply valid.2 x y ⟨oldX, oldY⟩
    exact sameX.symm.trans (equal.trans sameY)

/-- Split a pairwise relation at the distinguished source value after a
prefix, exposing the corresponding target prefix, value, and suffix. -/
theorem forall2_split_head {α β : Type} {rel : α → β → Prop}
    (pre : List α) (value : α) (tail : List α) (other : List β)
    (related : List.Forall₂ rel (pre ++ value :: tail) other) :
    ∃ pre2 value2 tail2, other = pre2 ++ value2 :: tail2 ∧
      List.Forall₂ rel pre pre2 ∧ rel value value2 ∧ List.Forall₂ rel tail tail2 := by
  induction pre generalizing other with
  | nil =>
    cases related with
    | cons head rest => exact ⟨[], _, _, rfl, .nil, head, rest⟩
  | cons first pre ih =>
    cases related with
    | cons head rest =>
      obtain ⟨pre2, value2, tail2, eq, prefixRel, valueRel, tailRel⟩ := ih _ rest
      subst eq
      exact ⟨_ :: pre2, value2, tail2, rfl, .cons head prefixRel, valueRel, tailRel⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
