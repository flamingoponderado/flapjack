import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Relocation

/-! Relocation of abstract reference cells by a collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- A pairwise value relation relocates when every pointer in its address
list belongs to the collector domain. -/
theorem valueInvList_gcRelated {width : Nat} [NeZero width] (conf : Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (related : gcRelated g heap heap2)
    (addresses : List (HeapAddress (WordLocW width))) (values : List Value)
    (pairs : List.Forall₂ (fun addr value => valueInv conf value refs (addr, f, tf, heap)) addresses values)
    (domain : ∀ ptr u, .pointer ptr u ∈ addresses → g.lookup ptr ≠ none) :
    List.Forall₂ (fun addr value => valueInv conf value refs
      (addr, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2))
      (addrMap (holFapply g) addresses) values := by
  induction pairs with
  | nil => exact .nil
  | @cons addr value rest values head tail ih =>
    have headDomain : ∀ ptr u, addr = .pointer ptr u → g.lookup ptr ≠ none := by
      intro ptr u eq
      apply domain ptr u
      simp [← eq]
    have tailDomain : ∀ ptr u, .pointer ptr u ∈ rest → g.lookup ptr ≠ none := by
      intro ptr u member
      apply domain ptr u
      simp [member]
    have moved := valueInv_gcRelated conf value refs addr f tf g heap heap2 related headDomain head
    have tailMoved := ih tailDomain
    cases addr <;> simp only [addrMap] <;> apply List.Forall₂.cons
    all_goals first | simpa [addrApply] using moved | exact tailMoved

/-- A reference cell remains valid when the collector relocates its address
and every pointer stored in the cell. This is Flapjack proof infrastructure;
the source theorem's finite-map representation requires separate review. -/
theorem bcRefInv_gcRelated {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Value)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (bigEndian : Bool)
    (related : gcRelated g heap heap2)
    (valid : bcRefInv conf n refs (f, tf, heap, bigEndian))
    (domain : g.lookup (holFapply f n) ≠ none) :
    bcRefInv conf n refs (HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2, bigEndian) := by
  cases first : f.lookup n with
  | none => simp [bcRefInv, first] at valid
  | some ptr =>
    have applyFirst : holFapply f n = ptr := holFapply_of_lookup first
    have defined : g.lookup ptr ≠ none := by simpa [applyFirst] using domain
    cases second : g.lookup ptr with
    | none => exact False.elim (defined second)
    | some target =>
      have composed := HolFiniteMapExact.lookup_compose_of_lookup g f n ptr target first second
      cases found : sptLookup n refs with
      | none => simp [bcRefInv, first, found] at valid
      | some ref =>
        cases ref with
        | valueArray values =>
          simp only [bcRefInv, first, found] at valid
          obtain ⟨addresses, cell, pairs⟩ := valid
          have original : heapLookup ptr heap = some (.dataElement addresses addresses.length (.refTag, [])) := by
            simpa [refBlock] using cell
          obtain ⟨moved, children⟩ := related.2.2.2 ptr addresses addresses.length (.refTag, []) defined original
          simp only [bcRefInv, composed, found]
          refine ⟨addrMap (holFapply g) addresses, ?_, valueInvList_gcRelated conf refs f tf g heap heap2 related addresses values pairs children⟩
          simpa [refBlock, holFapply_of_lookup second, ← addrMap_length addresses (holFapply g)] using moved
        | byteArray compareByContents bytes =>
          simp only [bcRefInv, first, found] at valid
          simp only [bcRefInv, composed, found]
          have original := related.2.2.2 ptr []
            (writeBytes bytes (List.replicate (bytes.length / (width / 8) + 1) 0) bigEndian).length
            (.bytesTag compareByContents bytes.length,
              (writeBytes bytes (List.replicate (bytes.length / (width / 8) + 1) 0) bigEndian).map .word)
            defined (by simpa [bytesRep] using valid)
          simpa [bytesRep, addrMap, holFapply_of_lookup second] using original.1
        | thunk mode value =>
          simp only [bcRefInv, first, found] at valid
          obtain ⟨addr, cell, safe, childValid⟩ := valid
          have original : heapLookup ptr heap = some (.dataElement [addr] 1 (.thunkTag mode, [])) := by
            simpa [thunkBlock] using cell
          obtain ⟨moved, children⟩ := related.2.2.2 ptr [addr] 1 (.thunkTag mode, []) defined original
          have childDomain : ∀ p u, addr = .pointer p u → g.lookup p ≠ none := by
            intro p u eq
            apply children p u
            simp [← eq]
          simp only [bcRefInv, composed, found]
          refine ⟨addrApply (holFapply g) addr, ?_, safe,
            valueInv_gcRelated conf value refs addr f tf g heap heap2 related childDomain childValid⟩
          cases addr <;> simpa [thunkBlock, addrMap, addrApply, holFapply_of_lookup second] using moved
        | mutBlock tag finalised left value right =>
          simp only [bcRefInv, first, found] at valid
          obtain ⟨noGen, fresh, addresses, cell, pairs⟩ := valid
          have original : heapLookup ptr heap = some (.dataElement addresses addresses.length (.blockTag tag, [])) := by
            simpa [blockRep] using cell
          obtain ⟨moved, children⟩ := related.2.2.2 ptr addresses addresses.length (.blockTag tag, []) defined original
          simp only [bcRefInv, composed, found]
          refine ⟨noGen, ?_, addrMap (holFapply g) addresses, ?_,
            valueInvList_gcRelated conf refs f tf g heap heap2 related addresses (left ++ [value] ++ right) pairs children⟩
          · intro notFinal ⟨stamp, stampDomain, equal⟩
            obtain ⟨middle, firstStamp, _, secondStamp⟩ := (mapDomain_compose g tf stamp).mp stampDomain
            have stampDefined : g.lookup middle ≠ none := by rw [secondStamp]; simp
            have stampApply : holFapply tf stamp = middle := holFapply_of_lookup firstStamp
            have composedApply : holFapply (HolFiniteMapExact.compose g tf) stamp = holFapply g middle := by
              rw [holFapply_of_lookup (HolFiniteMapExact.lookup_compose_of_lookup g tf stamp middle _ firstStamp secondStamp), holFapply_of_lookup secondStamp]
            have equalMiddle : middle = ptr := related.2.1 middle ptr stampDefined defined (by
              simpa [composedApply, holFapply_of_lookup second] using equal)
            exact fresh notFinal ⟨stamp, ⟨middle, firstStamp⟩, by simpa [stampApply] using equalMiddle⟩
          · simpa [blockRep, holFapply_of_lookup second, ← addrMap_length addresses (holFapply g)] using moved

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
