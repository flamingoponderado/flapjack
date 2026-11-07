import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.CollectorPartial
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapStore
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockRef

/-! Collector bookkeeping for allocating a constructor in free space. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.GcCombined

/-- A split before an allocation boundary keeps its prefix when the whole
suffix is replaced. This is Flapjack infrastructure. -/
theorem heapSplit_before_suffix {α β : Type} (pre old new : List (HeapElement α β))
    (offset : Nat) (bound : offset ≤ heapLength pre) (first second : List (HeapElement α β))
    (split : heapSplit offset (pre ++ old) = some (first, second)) :
    ∃ second', heapSplit offset (pre ++ new) = some (first, second') := by
  induction pre generalizing offset first second with
  | nil =>
    have zero : offset = 0 := by simpa [heapLength] using bound
    subst offset
    have splitZero (heap : List (HeapElement α β)) : heapSplit 0 heap = some ([], heap) := by
      cases heap <;> simp [heapSplit]
    simp only [List.nil_append, splitZero, Option.some.injEq, Prod.mk.injEq] at split
    obtain ⟨rfl, rfl⟩ := split
    exact ⟨new, by simpa using splitZero new⟩
  | cons head tail ih =>
    by_cases zero : offset = 0
    · subst offset
      simp [heapSplit] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨head :: (tail ++ new), by simp [heapSplit]⟩
    · by_cases inside : offset < elLength head
      · simp [heapSplit, zero, inside] at split
      · have remain : offset - elLength head ≤ heapLength tail := by
          change offset ≤ elLength head + heapLength tail at bound
          omega
        cases tailSplit : heapSplit (offset - elLength head) (tail ++ old) with
        | none => simp [heapSplit, zero, inside, tailSplit] at split
        | some pair =>
          obtain ⟨left, right⟩ := pair
          have eq : (head :: left, right) = (first, second) := by
            simpa [heapSplit, zero, inside, tailSplit] using split
          cases eq
          obtain ⟨right', split'⟩ := ih _ remain left second tailSplit
          exact ⟨right', by simp [heapSplit, zero, inside, split']⟩

/-- All old generation-start restrictions remain true when allocation
changes only the suffix at the allocation boundary. -/
theorem genStateOk_allocateSuffix {α β : Type} (pre old new : List (HeapElement α β))
    (refsStart advance : Nat) (gens : GenState)
    (valid : genStateOk (heapLength pre) refsStart (pre ++ old) gens) :
    genStateOk (heapLength pre + advance) refsStart (pre ++ new) gens := by
  cases gens with
  | genState _ starts =>
    constructor
    · intro start member
      have original := valid.1 start member
      omega
    · intro start member
      obtain ⟨first, second, split, pointers⟩ := valid.2 start member
      obtain ⟨second', split'⟩ := heapSplit_before_suffix pre old new start (valid.1 start member) first second split
      exact ⟨first, second', split', pointers⟩

/-- Allocating a data cell from a free region leaves the rest as an unused
region at the advanced allocation boundary. -/
theorem unusedSpaceInv_allocateData {α β : Type} (pre post : List (HeapElement α β))
    (ptrs : List (HeapAddress α)) (len free : Nat) (payload : β)
    (preData : ∀ element ∈ pre, isDataElement element) :
    unusedSpaceInv (heapLength pre + (len + 1)) (free - (len + 1))
      (pre ++ [.dataElement ptrs len payload] ++ heapExpand (free - (len + 1)) ++ post) := by
  have allData : ∀ element ∈ pre ++ [.dataElement ptrs len payload], isDataElement element := by
    intro element member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact preData element old
    · simp [isDataElement]
  have result := unusedSpaceInv_heapExpand_suffix (pre ++ [.dataElement ptrs len payload]) post
    (free - (len + 1)) allData
  simpa [heapLength_append, heapLength, elLength, List.append_assoc] using result

/-- Allocating an immutable constructor from the available region preserves
the collector invariant. The allocation fits in `sp`, so the reference
boundary stays fixed even for a generational collector. -/
theorem gcKindInv_allocateBlock {α β : Type} (conf : Config)
    (pre post : List (HeapElement α (HeapTag × List β))) (addresses : List (HeapAddress α))
    (sp sp1 tag : Nat) (gens : GenState) (enough : addresses.length + 1 ≤ sp)
    (valid : gcKindInv conf (heapLength pre) sp sp1 gens (pre ++ heapExpand (sp + sp1) ++ post)) :
    gcKindInv conf (heapLength pre + (addresses.length + 1)) (sp - (addresses.length + 1)) sp1 gens
      (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post) := by
  have boundary : heapLength pre + sp + sp1 =
      (heapLength pre + (addresses.length + 1)) + (sp - (addresses.length + 1)) + sp1 := by omega
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    simp only [gcKindInv, kind] at valid ⊢
    obtain ⟨oldGens, first, second, oldSplit, noRefs, refs⟩ := valid
    have oldIndex : heapLength (pre ++ heapExpand (sp + sp1)) = heapLength pre + sp + sp1 := by
      simp [heapLength_append, heapLength_heapExpand]
      omega
    have knownSplit := Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.heapSplit_append (pre ++ heapExpand (sp + sp1)) post
    rw [oldIndex] at knownSplit
    have splitEq : (first, second) = (pre ++ heapExpand (sp + sp1), post) := by
      have same : some (first, second) = some (pre ++ heapExpand (sp + sp1), post) := by
        rw [← oldSplit]
        simpa [List.append_assoc] using knownSplit
      exact Option.some.inj same
    obtain ⟨rfl, rfl⟩ := splitEq
    let newPrefix := pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1))
    have newIndex : heapLength newPrefix = heapLength pre + sp + sp1 := by
      simp only [newPrefix, heapLength_append, heapLength_heapExpand]
      have one : heapLength [blockRep (β := β) tag addresses] = addresses.length + 1 := by
        simp [heapLength, blockRep, elLength]
      rw [one]
      omega
    have newGens := genStateOk_allocateSuffix pre (heapExpand (sp + sp1) ++ post)
      ([blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post)
      (heapLength pre + sp + sp1) (addresses.length + 1) gens (by simpa [List.append_assoc] using oldGens)
    refine ⟨?_, newPrefix, post, ?_, ?_, refs⟩
    · simpa [boundary, List.append_assoc] using newGens
    · rw [← boundary, ← newIndex]
      simpa [newPrefix, List.append_assoc] using Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.heapSplit_append newPrefix post
    · intro element member
      simp only [newPrefix, List.mem_append, List.mem_singleton] at member
      rcases member with (fromPre | same) | fromFree
      · exact noRefs element (List.mem_append_left _ fromPre)
      · subst element
        simp [isRef, isMutTag, blockRep]
      · by_cases zero : sp + sp1 - (addresses.length + 1) = 0
        · simp [heapExpand, zero] at fromFree
        · simp [heapExpand, zero] at fromFree
          subst element
          simp [isRef]

/-- The data prefix recorded by the unused-space invariant is the actual
prefix at that heap boundary. -/
theorem dataUpTo_prefix_data {α β : Type} (pre suffix : List (HeapElement α β))
    (valid : dataUpTo (heapLength pre) (pre ++ suffix)) :
    ∀ element ∈ pre, isDataElement element := by
  obtain ⟨first, second, split, data⟩ := valid
  have known := Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.heapSplit_append pre suffix
  rw [known] at split
  have eq := Option.some.inj split
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
  exact data

/-- Replacing an unused region with a constructor and the remaining free
space preserves root and heap validity when the constructor fields are roots. -/
theorem heapOk_allocateBlock {α β : Type}
    (pre post : List (HeapElement α (HeapTag × List β))) (roots addresses : List (HeapAddress α))
    (free tag limit : Nat) (annotation : α) (enough : addresses.length + 1 ≤ free)
    (rootValid : rootsOk roots (pre ++ heapExpand free ++ post))
    (heapValid : heapOk (pre ++ heapExpand free ++ post) limit)
    (fieldRoots : ∀ address ∈ addresses, address ∈ roots) :
    rootsOk (.pointer (heapLength pre) annotation :: roots)
        (pre ++ [blockRep tag addresses] ++ heapExpand (free - (addresses.length + 1)) ++ post) ∧
      heapOk (pre ++ [blockRep tag addresses] ++ heapExpand (free - (addresses.length + 1)) ++ post) limit := by
  let remaining := free - (addresses.length + 1)
  let oldHeap := pre ++ heapExpand free ++ post
  let newHeap := pre ++ [blockRep tag addresses] ++ heapExpand remaining ++ post
  have positive : free ≠ 0 := by omega
  have oldShape : oldHeap = pre ++ [.unused (free - 1)] ++ post := by simp [oldHeap, heapExpand, positive]
  have size : heapLength (blockRep (β := β) tag addresses :: heapExpand remaining) = (free - 1) + 1 := by
    have one : heapLength [blockRep (β := β) tag addresses] = addresses.length + 1 := by
      simp [heapLength, blockRep, elLength]
    change heapLength ([blockRep tag addresses] ++ heapExpand remaining) = _
    rw [heapLength_append, one, heapLength_heapExpand]
    dsimp [remaining]
    omega
  have preserved : ∀ ptr, isSomeDataElement (heapLookup ptr oldHeap) → isSomeDataElement (heapLookup ptr newHeap) := by
    intro ptr ⟨xs, len, payload, found⟩
    have result := heapLookup_allocate_preservesData pre post (blockRep tag addresses :: heapExpand remaining)
      (free - 1) size ptr (.dataElement xs len payload) (by simp [isDataElement]) (by simpa [oldShape] using found)
    exact ⟨xs, len, payload, by simpa [newHeap, List.append_assoc] using result⟩
  have newCell : isSomeDataElement (heapLookup (heapLength pre) newHeap) := by
    have found := Flapjack.Compiler.Backend.heapLookup_prefix pre (heapExpand remaining ++ post) (blockRep (β := β) tag addresses)
    have eq : heapLookup (heapLength pre) newHeap = some (blockRep tag addresses) := by
      simpa [newHeap, List.append_assoc] using found
    rw [eq]
    simp [isSomeDataElement, blockRep]
  constructor
  · intro ptr value member
    rcases List.mem_cons.mp member with equal | old
    · cases equal
      exact newCell
    · exact preserved ptr (rootValid ptr value old)
  · refine ⟨?_, ?_, ?_⟩
    · have oldLength : heapLength oldHeap = limit := heapValid.1
      have newLength : heapLength newHeap = heapLength oldHeap := by
        simp only [newHeap, oldHeap, heapLength_append, heapLength_heapExpand]
        have one : heapLength [blockRep (β := β) tag addresses] = addresses.length + 1 := by
          simp [heapLength, blockRep, elLength]
        rw [one]
        dsimp [remaining]
        omega
      exact newLength.trans oldLength
    · have oldFiltered := heapValid.2.1
      by_cases remainingZero : remaining = 0 <;>
        simpa [newHeap, oldHeap, heapExpand, positive, remainingZero, List.filter_append,
          blockRep, isForwardPointer] using oldFiltered
    · intro xs len payload ptr value ⟨member, pointer⟩
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with ((old | here) | freeMember) | old
      · exact preserved ptr (heapValid.2.2 xs len payload ptr value
          ⟨by simp [old], pointer⟩)
      · have pointers : xs = addresses := by
          have eq := HeapElement.dataElement.inj here
          exact eq.1
        subst xs
        exact preserved ptr (rootValid ptr value (fieldRoots _ pointer))
      · by_cases zero : remaining = 0
        · simp [heapExpand] at freeMember
        · simp [heapExpand] at freeMember
      · exact preserved ptr (heapValid.2.2 xs len payload ptr value
          ⟨by simp [old], pointer⟩)

/-- Allocating a nonempty constructor from free space preserves the complete
abstract ML invariant. Its field roots form a prefix of the existing roots;
the allocation consumes only space before the collector's reference boundary. -/
theorem absMlInv_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (children stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (addresses roots : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (pre post : ValueHeap width) (sp sp1 next tag limit : Nat) (be : Bool) (gens : GenState)
    (nonempty : children ≠ []) (lengths : children.length = addresses.length)
    (enough : addresses.length + 1 ≤ sp)
    (inv : absMlInv conf (children ++ stack) refs
      (addresses ++ roots, pre ++ heapExpand (sp + sp1) ++ post, be,
        heapLength pre, sp, sp1, gens) limit next) :
    absMlInv conf (.block next tag children :: children ++ stack) refs
      (.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)) :: addresses ++ roots,
       pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post,
       be, heapLength pre + (addresses.length + 1), sp - (addresses.length + 1), sp1, gens) limit (next + 1) := by
  obtain ⟨rootsValid, heapValid, gcValid, unused, stackValid⟩ := inv
  have preData : ∀ element ∈ pre, isDataElement element :=
    dataUpTo_prefix_data pre (heapExpand (sp + sp1) ++ post) (by simpa [List.append_assoc] using unused.2.2)
  have heapResult := heapOk_allocateBlock pre post (addresses ++ roots) addresses (sp + sp1) tag limit
    (.word (ptrBits conf tag addresses.length)) (by omega) rootsValid heapValid
    (by intro address member; exact List.mem_append_left _ member)
  have gcResult := gcKindInv_allocateBlock conf pre post addresses sp sp1 tag gens enough gcValid
  have unusedResult := unusedSpaceInv_allocateData pre post addresses addresses.length (sp + sp1) (.blockTag tag, []) preData
  have remainingEq : (sp + sp1) - (addresses.length + 1) = (sp - (addresses.length + 1)) + sp1 := by omega
  have positive : sp + sp1 ≠ 0 := by omega
  have oldShape : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [ite_eq_right positive]
  have size : heapLength (blockRep (β := WordLocW width) tag addresses :: heapExpand ((sp + sp1) - (addresses.length + 1))) =
      (sp + sp1 - 1) + 1 := by
    change heapLength ([blockRep tag addresses] ++ heapExpand ((sp + sp1) - (addresses.length + 1))) = _
    rw [heapLength_append, heapLength_heapExpand]
    have one : heapLength [blockRep (β := WordLocW width) tag addresses] = addresses.length + 1 := by
      simp [heapLength, blockRep, elLength]
    rw [one]
    omega
  have stackResult := bcStackRefInv_allocateBlock_prefix conf children stack addresses roots refs pre post
    (heapExpand ((sp + sp1) - (addresses.length + 1))) (sp + sp1 - 1) next tag be nonempty lengths size
    (by simpa only [oldShape, List.append_assoc, List.singleton_append] using stackValid)
  refine ⟨heapResult.1, heapResult.2, gcResult, ?_, ?_⟩
  · simpa [remainingEq, blockRep, List.append_assoc] using unusedResult
  · simpa [List.append_assoc] using stackResult

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
