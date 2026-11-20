module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.HeapStoreRel
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Preserving all existing data cells retains each reference-cell invariant.
This Flapjack helper supplies the reference cases in HOL's `word64_alt_thm`. -/
private theorem bcRefInv_heapStoreRel {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (be : Bool)
    (rel : heapStoreRel heap heap2) (valid : bcRefInv conf n refs (f, tf, heap, be)) :
    bcRefInv conf n refs (f, tf, heap2, be) := by
  have cells : ∀ ptr cell, isDataElement cell → heapLookup ptr heap = some cell → heapLookup ptr heap2 = some cell := by
    intro ptr cell data found
    obtain ⟨xs, len, d, rfl⟩ := data
    exact (rel ptr ⟨xs, len, d, found⟩).trans found
  have valueRel : ∀ value address, valueInv conf value refs (address, f, tf, heap) →
      valueInv conf value refs (address, f, tf, heap2) := by
    intro value address inv
    exact heapStoreRel_valueInv conf refs f tf heap heap2 value address ⟨rel, inv⟩
  cases fLookup : f.lookup n with
  | none => simp [bcRefInv, fLookup] at valid
  | some ptr =>
    cases refLookup : sptLookup n refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray values =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨addresses, found, related⟩ := valid
        exact ⟨addresses, cells ptr _ (by simp [isDataElement, refBlock]) found,
          related.imp (fun address value h => valueRel value address h)⟩
      | byteArray compare bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        exact cells ptr _ (by simp [isDataElement, bytesRep]) valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨address, found, safe, related⟩ := valid
        exact ⟨address, cells ptr _ (by simp [isDataElement, thunkBlock]) found, safe,
          valueRel value address related⟩
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid ⊢
        obtain ⟨gen, noStamp, addresses, found, related⟩ := valid
        exact ⟨gen, noStamp, addresses, cells ptr _ (by simp [isDataElement, blockRep]) found,
          related.imp (fun address value h => valueRel value address h)⟩
/-- Existing stack and reference representations survive a heap-store
relation. This helper is used by HOL's Word64 allocation argument. -/
theorem bcStackRefInv_heapStoreRel {width : Nat} [NeZero width] (conf : Config) (next : Nat)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap heap2 : ValueHeap width) (be : Bool)
    (rel : heapStoreRel heap heap2) (valid : bcStackRefInv conf next stack refs (roots, heap, be)) :
    bcStackRefInv conf next stack refs (roots, heap2, be) := by
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimes, tfBound, endian, unique, values, refsValid⟩ := valid
  have preserve (map : HolFiniteMapExact Nat Nat)
      (inv : mapInjInto map (fun ptr => isSomeDataElement (heapLookup ptr heap))) :
      mapInjInto map (fun ptr => isSomeDataElement (heapLookup ptr heap2)) := by
    refine ⟨?_, inv.2⟩
    intro key domain
    have found := inv.1 key domain
    rw [rel _ found]
    exact found
  refine ⟨f, tf, preserve f fInj, fDomain, preserve tf tfInj, tfTimes, tfBound, endian, unique, ?_, ?_⟩
  · exact values.imp (fun value address related =>
      heapStoreRel_valueInv conf refs f tf heap heap2 value address ⟨rel, related⟩)
  · intro n condition
    exact bcRefInv_heapStoreRel conf n refs f tf heap heap2 be rel (refsValid n condition)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
