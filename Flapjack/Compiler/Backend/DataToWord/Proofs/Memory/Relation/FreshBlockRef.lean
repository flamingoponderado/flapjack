module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlock
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.HeapExtend

@[expose] public section

/-! Reference invariants during allocation of a constructor. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A map into existing data cells cannot point at an unused allocation
boundary. This is Flapjack infrastructure for fresh block allocation. -/
theorem mapInjInto_unused_fresh {width : Nat} [NeZero width]
    (map : HolFiniteMapExact Nat Nat) (pre post : ValueHeap width) (unused : Nat)
    (valid : mapInjInto map (fun p => isSomeDataElement (heapLookup p (pre ++ [.unused unused] ++ post)))) :
    ∀ n, mapDomain map n → holFapply map n ≠ heapLength pre := by
  intro n domain equal
  have data := valid.1 n domain
  rw [equal] at data
  have lookup : heapLookup (heapLength pre) (pre ++ [.unused unused] ++ post) = some (.unused unused) := by
    simpa [List.append_assoc] using
      Flapjack.Compiler.Backend.heapLookup_prefix pre post (.unused unused : HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))
  rw [lookup] at data
  simp [isSomeDataElement] at data

/-- Existing reference-cell invariants are retained when an unused region is
replaced by a new constructor and the fresh timestamp is recorded. This also
covers unfinished mutable blocks, whose address must not acquire a timestamp. -/
theorem bcRefInv_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (pre post replacement : ValueHeap width) (unused next n : Nat) (be : Bool)
    (size : heapLength replacement = unused + 1)
    (bound : ∀ stamp ptr, tf.lookup stamp = some ptr → stamp < next)
    (fValid : mapInjInto f (fun p => isSomeDataElement (heapLookup p (pre ++ [.unused unused] ++ post))))
    (valid : bcRefInv conf n refs (f, tf, pre ++ [.unused unused] ++ post, be)) :
    bcRefInv conf n refs (f, tf.update (next, heapLength pre), pre ++ replacement ++ post, be) := by
  let oldHeap := pre ++ [.unused unused] ++ post
  let newHeap := pre ++ replacement ++ post
  let newTf := tf.update (next, heapLength pre)
  have timestamps : ∀ stamp ptr, tf.lookup stamp = some ptr → newTf.lookup stamp = some ptr := by
    intro stamp ptr lookup
    have smaller := bound stamp ptr lookup
    have different : next ≠ stamp := by omega
    simpa [newTf, HolFiniteMapExact.update, FUPDATE, different] using lookup
  have cells : ∀ ptr cell, isDataElement cell → heapLookup ptr oldHeap = some cell → heapLookup ptr newHeap = some cell := by
    intro ptr cell data found
    exact heapLookup_allocate_preservesData pre post replacement unused size ptr cell data found
  have fFresh := mapInjInto_unused_fresh f pre post unused fValid
  cases fLookup : f.lookup n with
  | none => simp [bcRefInv, fLookup] at valid
  | some ptr =>
    have ptrNe : ptr ≠ heapLength pre := by
      have ne := fFresh n ⟨ptr, fLookup⟩
      simpa [holFapply_of_lookup fLookup] using ne
    cases refLookup : sptLookup n refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨addresses, cell, related⟩ := valid
        refine ⟨addresses, cells ptr _ (by simp [isDataElement, refBlock]) cell, ?_⟩
        exact related.imp (fun address value h => valueInv_heapExtend conf refs f tf newTf oldHeap newHeap timestamps cells value address h)
      | byteArray compare bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        exact cells ptr _ (by simp [isDataElement, bytesRep]) valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨address, cell, safe, related⟩ := valid
        exact ⟨address, cells ptr _ (by simp [isDataElement, thunkBlock]) cell, safe,
          valueInv_heapExtend conf refs f tf newTf oldHeap newHeap timestamps cells value address related⟩
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨gen, noStamp, addresses, cell, related⟩ := valid
        refine ⟨gen, ?_, addresses, cells ptr _ (by simp [isDataElement, blockRep]) cell, ?_⟩
        · intro unfinished ⟨stamp, ⟨target, mapped⟩, equal⟩
          by_cases same : stamp = next
          · subst stamp
            have atNew : newTf.lookup next = some (heapLength pre) := by simp [newTf, HolFiniteMapExact.update, FUPDATE]
            rw [holFapply_of_lookup atNew] at equal
            exact ptrNe equal.symm
          · have oldMap : tf.lookup stamp = some target := by
              simpa [newTf, HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using mapped
            have oldEqual : holFapply tf stamp = ptr := by
              rw [holFapply_of_lookup mapped] at equal
              simpa [holFapply_of_lookup oldMap] using equal
            exact noStamp unfinished ⟨stamp, ⟨target, oldMap⟩, oldEqual⟩
        · exact related.imp (fun address item h => valueInv_heapExtend conf refs f tf newTf oldHeap newHeap timestamps cells item address h)

/-- A newly allocated nonempty constructor preserves the stack/reference
invariant. Its fields are selected from the old stack and paired with their
already-related abstract addresses. This does not yet establish the GC and
unused-space components of the complete abstract heap invariant. -/
theorem bcStackRefInv_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (stack children : List Value) (roots addresses : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref Value)) (pre post remainder : ValueHeap width)
    (unused next tag : Nat) (be : Bool)
    (nonempty : children ≠ []) (childrenOnStack : ∀ child, child ∈ children → child ∈ stack)
    (size : heapLength (blockRep tag addresses :: remainder) = unused + 1)
    (inv : bcStackRefInv conf next stack refs (roots, pre ++ [.unused unused] ++ post, be))
    (selectFields : ∀ f tf, List.Forall₂ (fun value address =>
        valueInv conf value refs (address, f, tf, pre ++ [.unused unused] ++ post)) stack roots →
      List.Forall₂ (fun value address =>
        valueInv conf value refs (address, f, tf, pre ++ [.unused unused] ++ post)) children addresses) :
    bcStackRefInv conf (next + 1) (.block next tag children :: stack) refs
      (.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)) :: roots,
       pre ++ (blockRep tag addresses :: remainder) ++ post, be) := by
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimes, tfBound, endian, unique, values, refInv⟩ := inv
  have childInv := selectFields f tf values
  let oldHeap := pre ++ [.unused unused] ++ post
  let newHeap := pre ++ (blockRep tag addresses :: remainder) ++ post
  let newTf := tf.update (next, heapLength pre)
  have bound : ∀ n ptr, tf.lookup n = some ptr → n < next := by
    intro n ptr lookup
    exact tfBound n ⟨ptr, lookup⟩
  have dataPreserved : ∀ ptr, isSomeDataElement (heapLookup ptr oldHeap) → isSomeDataElement (heapLookup ptr newHeap) := by
    intro ptr ⟨pointers, length, payload, lookup⟩
    exact ⟨pointers, length, payload,
      heapLookup_allocate_preservesData pre post (blockRep tag addresses :: remainder) unused size ptr _
        (by simp [isDataElement]) lookup⟩
  have newCell : isSomeDataElement (heapLookup (heapLength pre) newHeap) := by
    have found := Flapjack.Compiler.Backend.heapLookup_prefix pre (remainder ++ post) (blockRep tag addresses)
    have same : heapLookup (heapLength pre) newHeap = some (blockRep tag addresses) := by
      simpa [newHeap, List.append_assoc, List.cons_append] using found
    rw [same]
    simp [isSomeDataElement, blockRep]
  have fInjNew : mapInjInto f (fun p => isSomeDataElement (heapLookup p newHeap)) :=
    ⟨fun key domain => dataPreserved _ (fInj.1 key domain), fInj.2⟩
  have tfInjNew : mapInjInto newTf (fun p => isSomeDataElement (heapLookup p newHeap)) :=
    freshBlock_timestampMap_injective tf next (heapLength pre) _ _ tfInj dataPreserved newCell
      (mapInjInto_unused_fresh tf pre post unused tfInj)
  have timeProps := freshBlock_timestampMap refs stack children next tag (heapLength pre) tf childrenOnStack tfTimes tfBound
  have valueProps := valueInv_allocateBlock conf refs f tf pre post remainder unused next tag children addresses nonempty size bound childInv
  refine ⟨f, newTf, fInjNew, fDomain, tfInjNew, timeProps.1, timeProps.2, endian,
    blocksUnique_freshBlock refs stack children next tag childrenOnStack unique, ?_, ?_⟩
  · exact .cons valueProps.2 (values.imp (fun value address h => valueProps.1 value address h))
  · intro n ⟨reachable, domain⟩
    have oldReach := (reachableRefs_freshBlock refs stack children next tag n childrenOnStack).mp reachable
    exact bcRefInv_allocateBlock conf refs f tf pre post (blockRep tag addresses :: remainder) unused next n be
      size bound fInj (refInv n ⟨oldReach, domain⟩)

/-- Constructor fields occupying a corresponding stack prefix need no extra
field-relation premise: the existing stack invariant provides it directly. -/
theorem bcStackRefInv_allocateBlock_prefix {width : Nat} [NeZero width] (conf : Config)
    (children stack : List Value) (addresses roots : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref Value)) (pre post remainder : ValueHeap width)
    (unused next tag : Nat) (be : Bool) (nonempty : children ≠ [])
    (lengths : children.length = addresses.length)
    (size : heapLength (blockRep tag addresses :: remainder) = unused + 1)
    (inv : bcStackRefInv conf next (children ++ stack) refs
      (addresses ++ roots, pre ++ [.unused unused] ++ post, be)) :
    bcStackRefInv conf (next + 1) (.block next tag children :: children ++ stack) refs
      (.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)) :: addresses ++ roots,
       pre ++ (blockRep tag addresses :: remainder) ++ post, be) := by
  apply bcStackRefInv_allocateBlock conf (children ++ stack) children (addresses ++ roots) addresses refs
    pre post remainder unused next tag be nonempty (by intro child member; exact List.mem_append_left _ member) size inv
  intro f tf related
  have selected := List.forall₂_take children.length related
  simpa [lengths] using selected

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
