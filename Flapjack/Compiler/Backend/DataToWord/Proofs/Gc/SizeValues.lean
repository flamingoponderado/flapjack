module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapTraversal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Misc.Multiword.Length
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking

@[expose] public section

/-! Source heap sizing facts used by collector soundness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Sizing a cons list first processes its tail, then its head. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_cons"]
theorem sizeOfValues_cons (limits : DataSem.Limits) (x : DataSem.Value) (xs : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (x :: xs) refs seen =
      let (n1, refs1, seen1) := DataSem.sizeOfValues limits xs refs seen
      let (n2, refs2, seen2) := DataSem.sizeOfValues limits [x] refs1 seen1
      (n1 + n2, refs2, seen2) := by
  cases xs with
  | nil => simp [DataSem.sizeOfValues]
  | cons y ys => simp only [DataSem.sizeOfValues, DataSem.checkRes_sizeOfValues]

/-- The optional global and its default value have identical sizing effects. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_global_to_vs"]
theorem sizeOfValues_global (limits : DataSem.Limits) (values : List DataSem.Value) (global : Option Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (values ++ DataSem.globalToValues global) refs seen =
      DataSem.sizeOfValues limits (values ++ [theGlobal global]) refs seen := by
  induction values generalizing refs seen with
  | nil =>
    cases global with
    | none =>
      cases arch : limits.arch64Bit <;>
        simp [DataSem.globalToValues, theGlobal, DataSem.sizeOfValues, DataSem.smallNum, arch]
    | some addr => simp [DataSem.globalToValues, theGlobal]
  | cons head tail ih =>
    simp only [List.cons_append]
    conv_lhs => rw [sizeOfValues_cons, ih]
    conv_rhs => rw [sizeOfValues_cons]

/-- A block costs nothing when empty or already seen; otherwise its fields
are sized after recording its timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_Block"]
theorem sizeOfValues_block (limits : DataSem.Limits) (stamp tag : Nat) (values : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits [.block stamp tag values] refs seen =
      if values = [] ∨ (sptLookup stamp seen).isSome = true then (0, refs, seen)
      else
        let (n, refs1, seen1) := DataSem.sizeOfValues limits values refs (sptInsert stamp () seen)
        (n + values.length + 1, refs1, seen1) := by
  cases values with
  | nil => simp [DataSem.sizeOfValues]
  | cons head tail => simp [DataSem.sizeOfValues]

/-- Flapjack infrastructure: on a supported architecture, the word-digit
encoding length is exactly the source sizing function's digit count. -/
theorem n2mw_length_eq_bignumDigits {width : Nat} [NeZero width] (n : Nat)
    (good : goodDimindex width) :
    (Misc.Multiword.n2mw (width := width) n).length = DataSem.bignumDigits (decide (width = 64)) n := by
  have widthEq : (if decide (width = 64) then 64 else 32) = width := by
    rcases good with rfl | rfl <;> decide
  by_cases zero : n = 0
  · subst n
    simp [Misc.Multiword.n2mw, DataSem.bignumDigits]
  · rw [Misc.Multiword.n2mw, DataSem.bignumDigits]
    simp only [zero, ↓reduceIte, List.length_cons, widthEq]
    have smaller : n / 2 ^ width < n := by
      apply Nat.div_lt_self (Nat.pos_of_ne_zero zero)
      rcases good with rfl | rfl <;> decide
    have next := n2mw_length_eq_bignumDigits (width := width) (n / 2 ^ width) good
    omega
termination_by n

/-- The source bignum digit estimate bounds the encoded word-list length. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LENGTH_n2mw_LE_bignum_digits"
  (words_as_type_indexed_bitvec)]
theorem n2mw_length_le_bignumDigits {width : Nat} [NeZero width] (n m : Nat)
    (good : goodDimindex width) (bound : n ≤ m) :
    (Misc.Multiword.n2mw n : List (BitVec width)).length ≤ DataSem.bignumDigits (decide (width = 64)) m := by
  rw [← n2mw_length_eq_bignumDigits m good]
  exact Misc.Multiword.n2mw_length_mono n m bound

/-- Flapjack infrastructure: a represented large integer occupies no more
heap words than the source bignum size calculation charges. -/
theorem lookupLen_bignum_le {width : Nat} [NeZero width] {α : Type}
    (limits : DataSem.Limits) (heap : List (HeapElement α (Memory.HeapTag × List (WordLocW width))))
    (ptr : Nat) (value : Int) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64))
    (found : heapLookup ptr heap = some (Memory.bignumRep value)) :
    Memory.lookupLen heap ptr ≤ DataSem.bignumSize limits.arch64Bit value := by
  have digits := n2mw_length_le_bignumDigits (width := width) value.natAbs value.natAbs good (Nat.le_refl _)
  simp only [Memory.lookupLen, found, Memory.bignumRep, Misc.Multiword.i2mw, elLength,
    DataSem.bignumSize, architecture]
  omega

/-- Flapjack infrastructure: the source's three-word charge for a Word64
value bounds the 32-bit and 64-bit heap representations. -/
theorem lookupLen_word64_le {width : Nat} [NeZero width] {α : Type}
    (heap : List (HeapElement α (Memory.HeapTag × List (WordLocW width))))
    (ptr : Nat) (value : BitVec 64)
    (found : heapLookup ptr heap = some (Memory.word64Rep value)) :
    Memory.lookupLen heap ptr ≤ 3 := by
  simp only [Memory.lookupLen, found, Memory.word64Rep]
  split <;> simp [elLength]

/-- Flapjack infrastructure: a bignum cell can be traversed while charging
at most the source bignum size. -/
theorem traverse_bignum_size {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (heap : List (HeapElement (WordLocW width) (Memory.HeapTag × List (WordLocW width)))) (visited : List Nat)
    (ptr : Nat) (value : Int) (annotation : WordLocW width) (good : goodDimindex width)
    (architecture : limits.arch64Bit = decide (width = 64))
    (found : heapLookup ptr heap = some (Memory.bignumRep value)) :
    traverseHeap heap visited [.pointer ptr annotation] (ptr :: visited) ∧
    (Memory.lookupLen heap ptr :: visited.map (Memory.lookupLen heap)).sum ≤
      DataSem.bignumSize limits.arch64Bit value + (visited.map (Memory.lookupLen heap)).sum := by
  refine ⟨?_, ?_⟩
  · apply traverseHeap.visit (children := [])
    · simpa [Memory.bignumRep, Misc.Multiword.i2mw] using found
    · exact traverseHeap.empty _
  · simp only [List.sum_cons]
    have size := lookupLen_bignum_le limits heap ptr value good architecture found
    omega

/-- Flapjack infrastructure: a represented Word64 can be traversed for no
more than the source's three-word charge. -/
theorem traverse_word64_size {width : Nat} [NeZero width]
    (heap : List (HeapElement (WordLocW width) (Memory.HeapTag × List (WordLocW width)))) (visited : List Nat) (ptr : Nat)
    (value : BitVec 64) (annotation : WordLocW width)
    (found : heapLookup ptr heap = some (Memory.word64Rep value)) :
    traverseHeap heap visited [.pointer ptr annotation] (ptr :: visited) ∧
    (Memory.lookupLen heap ptr :: visited.map (Memory.lookupLen heap)).sum ≤
      3 + (visited.map (Memory.lookupLen heap)).sum := by
  refine ⟨?_, ?_⟩
  · by_cases narrow : width < 64
    · apply traverseHeap.visit (children := [])
      · simpa [Memory.word64Rep, narrow] using found
      · exact traverseHeap.empty _
    · apply traverseHeap.visit (children := [])
      · simpa [Memory.word64Rep, narrow] using found
      · exact traverseHeap.empty _
  · simp only [List.sum_cons]
    have size := lookupLen_word64_le heap ptr value found
    omega

/-- Flapjack infrastructure: supported source and target architectures agree
on the immediate-integer range. -/
theorem smallNum_iff_smallInt {width : Nat} [NeZero width] (limits : DataSem.Limits)
    (i : Int) (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64)) :
    DataSem.smallNum limits.arch64Bit i ↔ smallInt width i := by
  rcases good with rfl | rfl <;>
    simp [DataSem.smallNum, smallInt, architecture]

/-- Flapjack infrastructure: a represented source number admits a heap
traversal whose added cost is bounded by the source singleton size. -/
theorem sizeOf_number_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (i : Int)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (related : Memory.valueInv conf (.number i) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.number i] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  have number := (Memory.valueInv_number conf i refs address f tf heap).mp related
  by_cases small : smallInt width i
  · have sourceSmall := (smallNum_iff_smallInt limits i good architecture).mpr small
    simp only [small, ↓reduceIte] at number
    subst address
    refine ⟨visited, traverseHeap.data visited _, ?_⟩
    simp [DataSem.sizeOfValues, sourceSmall]
  · have sourceBig : ¬ DataSem.smallNum limits.arch64Bit i := by
      intro sourceSmall
      exact small ((smallNum_iff_smallInt limits i good architecture).mp sourceSmall)
    simp only [small, ↓reduceIte] at number
    obtain ⟨ptr, rfl, found⟩ := number
    obtain ⟨run, cost⟩ := traverse_bignum_size limits heap visited ptr i (.word 0) good architecture found
    refine ⟨ptr :: visited, run, ?_⟩
    simpa [DataSem.sizeOfValues, sourceBig] using cost

/-- Flapjack infrastructure: a represented Word64 admits a traversal whose
added cost is bounded by its source singleton size. -/
theorem sizeOf_word64_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (value : BitVec 64)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.word64 value) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.word64 value] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  obtain ⟨ptr, rfl, found⟩ := (Memory.valueInv_word64 conf value refs address f tf heap).mp related
  obtain ⟨run, cost⟩ := traverse_word64_size heap visited ptr value (.word 0) found
  exact ⟨ptr :: visited, run, by simpa [DataSem.sizeOfValues] using cost⟩

/-- Flapjack infrastructure: a code pointer is an immediate value and adds
no heap traversal cost. -/
theorem sizeOf_codePtr_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (value : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.codePtr value) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.codePtr value] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  have equal := (Memory.valueInv_codePtr conf value refs address f tf heap).mp related
  subst address
  exact ⟨visited, traverseHeap.data visited _, by simp [DataSem.sizeOfValues]⟩

/-- Flapjack infrastructure: a nullary block is immediate and needs no heap
traversal or source-size charge. -/
theorem sizeOf_emptyBlock_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag []) refs (address, f, tf, heap)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.block stamp tag []] refs seen).1 + (visited.map (Memory.lookupLen heap)).sum := by
  have block := (Memory.valueInv_block conf stamp tag [] refs address f tf heap).mp related
  simp only [↓reduceIte] at block
  obtain ⟨rfl, _, _⟩ := block
  exact ⟨visited, traverseHeap.data visited _, by simp [DataSem.sizeOfValues]⟩

/-- Flapjack infrastructure: a previously sized nonempty block points to an
already visited heap cell and incurs no second traversal charge. -/
theorem sizeOf_seenBlock_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat) (head : DataSem.Value)
    (tail : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag (head :: tail)) refs (address, f, tf, heap))
    (already : (sptLookup stamp seen).isSome = true)
    (seenVisited : ∀ key ptr, (sptLookup key seen).isSome = true → tf.lookup key = some ptr → ptr ∈ visited) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.block stamp tag (head :: tail)] refs seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have block := (Memory.valueInv_block conf stamp tag (head :: tail) refs address f tf heap).mp related
  simp only [List.cons_ne_nil, ↓reduceIte] at block
  obtain ⟨ptr, children, _, timestamp, rfl, _⟩ := block
  have present := seenVisited stamp ptr already timestamp
  refine ⟨visited, traverseHeap.seen visited ptr _ present, ?_⟩
  simp [DataSem.sizeOfValues, already]

/-- Flapjack infrastructure: the recursive traversal of an unseen block's
children extends to the block itself, charging its header and fields once. -/
theorem sizeOf_freshBlock_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (stamp tag : Nat) (head : DataSem.Value)
    (tail : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.block stamp tag (head :: tail)) refs (address, f, tf, heap))
    (fresh : (sptLookup stamp seen).isSome = false)
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun value addr => Memory.valueInv conf value refs (addr, f, tf, heap)) (head :: tail) children →
      tf.lookup stamp = some ptr → heapLookup ptr heap = some (Memory.blockRep tag children) →
      ∃ after, traverseHeap heap (ptr :: visited) children after ∧
        (after.map (Memory.lookupLen heap)).sum ≤
          (DataSem.sizeOfValues limits (head :: tail) refs (sptInsert stamp () seen)).1 +
            ((ptr :: visited).map (Memory.lookupLen heap)).sum) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.block stamp tag (head :: tail)] refs seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have block := (Memory.valueInv_block conf stamp tag (head :: tail) refs address f tf heap).mp related
  simp only [List.cons_ne_nil, ↓reduceIte] at block
  obtain ⟨ptr, children, valuesRel, timestamp, rfl, found⟩ := block
  obtain ⟨after, traversal, bound⟩ := childrenSound ptr children valuesRel timestamp found
  refine ⟨after, ?_, ?_⟩
  · apply traverseHeap.visit (children := children)
    · simpa [Memory.blockRep] using found
    · exact traversal
  · have lengths := valuesRel.length_eq
    have ptrCost : Memory.lookupLen heap ptr = (head :: tail).length + 1 := by
      simp [Memory.lookupLen, found, Memory.blockRep, elLength, ← lengths]
    simp only [List.map_cons, List.sum_cons, ptrCost] at bound
    cases result : DataSem.sizeOfValues limits (head :: tail) refs (sptInsert stamp () seen) with
    | mk n rest =>
      cases rest
      rw [result] at bound
      simp [DataSem.sizeOfValues, fresh, result] at ⊢
      simp only [List.length_cons] at bound
      omega

/-- Flapjack infrastructure: the source singleton sizing equation for a
reference to a value array. -/
theorem sizeOfValues_refArray (limits : DataSem.Limits) (bit : Bool) (index : Nat)
    (values : List DataSem.Value) (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (found : sptLookup index refs = some (.valueArray values)) :
    DataSem.sizeOfValues limits [.refPtr bit index] refs seen =
      let (n, refs1, seen1) := DataSem.sizeOfValues limits values (sptDelete index refs) seen
      (n + values.length + 1, refs1, seen1) := by
  rw [DataSem.sizeOfValues]
  split <;> simp_all

/-- Flapjack infrastructure: a live value-array reference traverses its
represented cell and children within the source sizing charge, provided the
recursive child traversal meets its corresponding bound. -/
theorem sizeOf_refArray_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (values : List DataSem.Value) (remaining refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs)
    (subset : sptSubspt remaining refs) (found : sptLookup index remaining = some (.valueArray values))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be))
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun addr value => Memory.valueInv conf value refs (addr, f, tf, heap)) children values →
      f.lookup index = some ptr → heapLookup ptr heap = some (Memory.refBlock children) →
      ∃ after, traverseHeap heap (ptr :: visited) children after ∧
        (after.map (Memory.lookupLen heap)).sum ≤
          (DataSem.sizeOfValues limits values (sptDelete index remaining) seen).1 +
            ((ptr :: visited).map (Memory.lookupLen heap)).sum) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.refPtr bit index] remaining seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have original := (sptSubsptLookup remaining refs).mp subset index (.valueArray values) found
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  subst address
  have cell := refInv
  simp only [Memory.bcRefInv, mapFound, original] at cell
  obtain ⟨children, heapFound, valuesRel⟩ := cell
  obtain ⟨after, traversal, bound⟩ := childrenSound ptr children valuesRel mapFound heapFound
  refine ⟨after, ?_, ?_⟩
  · rw [holFapply_of_lookup mapFound]
    apply traverseHeap.visit (children := children)
    · simpa [Memory.refBlock] using heapFound
    · exact traversal
  · have lengths := valuesRel.length_eq
    have ptrCost : Memory.lookupLen heap ptr = values.length + 1 := by
      simp [Memory.lookupLen, heapFound, Memory.refBlock, elLength, lengths]
    simp only [List.map_cons, List.sum_cons, ptrCost] at bound
    rw [sizeOfValues_refArray limits bit index values remaining seen found]
    cases result : DataSem.sizeOfValues limits values (sptDelete index remaining) seen with
    | mk n rest =>
      cases rest
      rw [result] at bound
      dsimp only at bound ⊢
      omega

/-- Flapjack infrastructure: the source singleton sizing equation for a
reference to a mutable block. -/
theorem sizeOfValues_mutBlock (limits : DataSem.Limits) (bit : Bool) (index tag : Nat) (finalised : Bool)
    (left : List DataSem.Value) (value : DataSem.Value) (right : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (found : sptLookup index refs = some (.mutBlock tag finalised left value right)) :
    DataSem.sizeOfValues limits [.refPtr bit index] refs seen =
      let (n, refs1, seen1) := DataSem.sizeOfValues limits (left ++ [value] ++ right) (sptDelete index refs) seen
      (n + left.length + right.length + 2, refs1, seen1) := by
  rw [DataSem.sizeOfValues]
  split <;> simp_all

/-- Flapjack infrastructure: a live mutable-block reference traverses its
represented cell and children within the source sizing charge, assuming the
corresponding recursive child traversal bound. -/
theorem sizeOf_mutBlock_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index tag : Nat) (finalised : Bool)
    (left : List DataSem.Value) (value : DataSem.Value) (right : List DataSem.Value)
    (remaining refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs)
    (subset : sptSubspt remaining refs) (found : sptLookup index remaining = some (.mutBlock tag finalised left value right))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be))
    (childrenSound : ∀ ptr children,
      List.Forall₂ (fun addr item => Memory.valueInv conf item refs (addr, f, tf, heap)) children (left ++ [value] ++ right) →
      f.lookup index = some ptr → heapLookup ptr heap = some (Memory.blockRep tag children) →
      ∃ after, traverseHeap heap (ptr :: visited) children after ∧
        (after.map (Memory.lookupLen heap)).sum ≤
          (DataSem.sizeOfValues limits (left ++ [value] ++ right) (sptDelete index remaining) seen).1 +
            ((ptr :: visited).map (Memory.lookupLen heap)).sum) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.refPtr bit index] remaining seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have original := (sptSubsptLookup remaining refs).mp subset index (.mutBlock tag finalised left value right) found
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  subst address
  have cell := refInv
  simp only [Memory.bcRefInv, mapFound, original] at cell
  obtain ⟨_, _, children, heapFound, valuesRel⟩ := cell
  obtain ⟨after, traversal, bound⟩ := childrenSound ptr children valuesRel mapFound heapFound
  refine ⟨after, ?_, ?_⟩
  · rw [holFapply_of_lookup mapFound]
    apply traverseHeap.visit (children := children)
    · simpa [Memory.blockRep] using heapFound
    · exact traversal
  · have lengths := valuesRel.length_eq
    have ptrCost : Memory.lookupLen heap ptr = left.length + right.length + 2 := by
      simp [Memory.lookupLen, heapFound, Memory.blockRep, elLength, lengths]
      omega
    simp only [List.map_cons, List.sum_cons, ptrCost] at bound
    rw [sizeOfValues_mutBlock limits bit index tag finalised left value right remaining seen found]
    cases result : DataSem.sizeOfValues limits (left ++ [value] ++ right) (sptDelete index remaining) seen with
    | mk n rest =>
      cases rest
      rw [result] at bound
      dsimp only at bound ⊢
      omega

/-- Flapjack infrastructure: a source reference already removed from the
remaining tree has zero sizing cost. -/
theorem sizeOfValues_missingRef (limits : DataSem.Limits) (bit : Bool) (index : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (missing : sptLookup index refs = none) :
    DataSem.sizeOfValues limits [.refPtr bit index] refs seen = (0, refs, seen) := by
  rw [DataSem.sizeOfValues]
  split <;> simp_all

/-- Flapjack infrastructure: an already processed reference is traversed as
an existing visited pointer and adds no source-size charge. -/
theorem sizeOf_seenRef_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (remaining refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (visited : List Nat)
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (missing : sptLookup index remaining = none)
    (mapInRefs : ∀ key ptr, f.lookup key = some ptr → sptLookup key refs ≠ none)
    (removedVisited : ∀ key ptr, sptLookup key refs ≠ none → sptLookup key remaining = none →
      f.lookup key = some ptr → ptr ∈ visited) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.refPtr bit index] remaining seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have present := removedVisited index ptr (mapInRefs index ptr mapFound) missing mapFound
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  rw [address']
  refine ⟨visited, traverseHeap.seen visited ptr _ present, ?_⟩
  simp [sizeOfValues_missingRef limits bit index remaining seen missing]

/-- Flapjack infrastructure: the source singleton sizing equation for a
reference to a byte array. -/
theorem sizeOfValues_byteArray (limits : DataSem.Limits) (bit : Bool) (index : Nat)
    (compareByContents : Bool) (bytes : List (BitVec 8))
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (found : sptLookup index refs = some (.byteArray compareByContents bytes)) :
    DataSem.sizeOfValues limits [.refPtr bit index] refs seen =
      (bytes.length / (DataSem.archSize limits / 8) + 2, sptDelete index refs, seen) := by
  rw [DataSem.sizeOfValues]
  split <;> simp_all

/-- Flapjack infrastructure: a represented byte array is traversed for the
same word count charged by source sizing. -/
theorem sizeOf_byteArray_traversal {width : Nat} [NeZero width]
    (limits : DataSem.Limits) (conf : Config) (bit : Bool) (index : Nat)
    (compareByContents : Bool) (bytes : List (BitVec 8))
    (remaining refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit)
    (address : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : Memory.ValueHeap width) (be : Bool) (visited : List Nat)
    (good : goodDimindex width) (architecture : limits.arch64Bit = decide (width = 64))
    (related : Memory.valueInv conf (.refPtr bit index) refs (address, f, tf, heap))
    (noThunks : DataSem.noThunksInRefs refs) (subset : sptSubspt remaining refs)
    (found : sptLookup index remaining = some (.byteArray compareByContents bytes))
    (refInv : Memory.bcRefInv conf index refs (f, tf, heap, be)) :
    ∃ after, traverseHeap heap visited [address] after ∧
      (after.map (Memory.lookupLen heap)).sum ≤
        (DataSem.sizeOfValues limits [.refPtr bit index] remaining seen).1 +
          (visited.map (Memory.lookupLen heap)).sum := by
  have original := (sptSubsptLookup remaining refs).mp subset index (.byteArray compareByContents bytes) found
  have direct := (Memory.valueInv_refPtr_notThunk conf bit index refs address f tf heap
    (noThunks index)).mp related
  obtain ⟨⟨ptr, mapFound⟩, _, addressEq⟩ := direct
  have address' : address = .pointer ptr (Memory.refPtrAnnot conf (sptLookup index refs)) := by
    simpa [holFapply_of_lookup mapFound] using addressEq
  subst address
  have cell := refInv
  simp only [Memory.bcRefInv, mapFound, original] at cell
  have widthEq : DataSem.archSize limits = width := by
    rcases good with rfl | rfl <;> simp [DataSem.archSize, architecture]
  refine ⟨ptr :: visited, ?_, ?_⟩
  · rw [holFapply_of_lookup mapFound]
    apply traverseHeap.visit (children := [])
    · simpa [Memory.bytesRep] using cell
    · exact traverseHeap.empty _
  · simp only [List.map_cons, List.sum_cons]
    rw [sizeOfValues_byteArray limits bit index compareByContents bytes remaining seen found]
    simp only [widthEq]
    have size : Memory.lookupLen heap ptr = bytes.length / (width / 8) + 2 := by
      simp [Memory.lookupLen, cell, Memory.bytesRep, Memory.writeBytes_wordCount, elLength]
    omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
