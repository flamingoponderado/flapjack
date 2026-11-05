import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Timestamps
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

/-! Reachability invariants for allocating a fresh nonempty constructor. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Pushing a new block whose children are existing roots adds only the new
block to the reachable values. This is Flapjack allocation infrastructure. -/
theorem allValues_freshBlock (refs : Spt (BvlSem.Ref Value)) (stack children : List Value)
    (stamp tag : Nat) (childrenOnStack : ∀ child, child ∈ children → child ∈ stack) (value : Value) :
    allValues refs (.block stamp tag children :: stack) value ↔
      value = .block stamp tag children ∨ allValues refs stack value := by
  constructor
  · intro member
    rcases member with inArray | inThunk | inMut | inStack
    · exact Or.inr (Or.inl inArray)
    · exact Or.inr (Or.inr (Or.inl inThunk))
    · exact Or.inr (Or.inr (Or.inr (Or.inl inMut)))
    · simp only [valueListValues, List.mem_cons, List.mem_append] at inStack
      rcases inStack with (equal | nested) | old
      · exact Or.inl equal
      · obtain ⟨child, inChildren, inChild⟩ := valueListValues_member_origin children value nested
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (valueListValues_singleton_subset stack child value (childrenOnStack child inChildren) inChild))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr old)))
  · rintro (rfl | old)
    · exact mem_stack_allValues _ _ _ (by simp)
    · rcases old with inArray | inThunk | inMut | inStack
      · exact Or.inl inArray
      · exact Or.inr (Or.inl inThunk)
      · exact Or.inr (Or.inr (Or.inl inMut))
      · exact Or.inr (Or.inr (Or.inr (by simp [valueListValues, inStack])))

/-- Allocating a block at the next timestamp preserves uniqueness, advancing
its bound by one. Existing children may be shared or repeated. -/
theorem blocksUnique_freshBlock (refs : Spt (BvlSem.Ref Value)) (stack children : List Value)
    (next tag : Nat) (childrenOnStack : ∀ child, child ∈ children → child ∈ stack)
    (unique : blocksUnique next (allValues refs stack)) :
    blocksUnique (next + 1) (allValues refs (.block next tag children :: stack)) := by
  intro stamp tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
  rw [allValues_freshBlock refs stack children next tag childrenOnStack] at first second
  rcases first with first | first <;> rcases second with second | second
  · cases first
    cases second
    exact ⟨rfl, rfl, by omega⟩
  · have bound := (unique stamp tag2 xs2 tag2 xs2 ⟨second, nonempty2, second, nonempty2⟩).2.2
    cases first
    omega
  · have bound := (unique stamp tag1 xs1 tag1 xs1 ⟨first, nonempty1, first, nonempty1⟩).2.2
    cases second
    omega
  · obtain ⟨sameTag, sameValues, bound⟩ := unique stamp tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
    exact ⟨sameTag, sameValues, by omega⟩

/-- The timestamps reachable after allocating a block are the fresh timestamp
and the timestamps already reachable before allocation. -/
theorem allTimestamps_freshBlock (refs : Spt (BvlSem.Ref Value)) (stack children : List Value)
    (stamp tag : Nat) (childrenOnStack : ∀ child, child ∈ children → child ∈ stack) (ts : Nat) :
    allTimestamps refs (.block stamp tag children :: stack) ts ↔
      ts = stamp ∨ allTimestamps refs stack ts := by
  constructor
  · rintro ⟨value, inRefs | inStack, timestamp⟩
    · exact Or.inr ⟨value, Or.inl inRefs, timestamp⟩
    · rcases List.mem_cons.mp inStack with same | old
      · subst value
        simp only [valueTimestamps, List.mem_cons, List.mem_flatMap] at timestamp
        rcases timestamp with same | ⟨child, member, childTimestamp⟩
        · exact Or.inl same
        · exact Or.inr ⟨child, Or.inr (childrenOnStack child member), childTimestamp⟩
      · exact Or.inr ⟨value, Or.inr old, timestamp⟩
  · rintro (rfl | ⟨value, inRefs | inStack, timestamp⟩)
    · exact ⟨.block ts tag children, Or.inr (by simp), by simp [valueTimestamps]⟩
    · exact ⟨value, Or.inl inRefs, timestamp⟩
    · exact ⟨value, Or.inr (List.mem_cons_of_mem _ inStack), timestamp⟩

/-- Extending the timestamp map for a freshly allocated block preserves the
domain-to-reachability and upper-bound conditions of `bcStackRefInv`. -/
theorem freshBlock_timestampMap (refs : Spt (BvlSem.Ref Value)) (stack children : List Value)
    (next tag ptr : Nat) (tf : HolFiniteMapExact Nat Nat)
    (childrenOnStack : ∀ child, child ∈ children → child ∈ stack)
    (times : ∀ n, mapDomain tf n → allTimestamps refs stack n)
    (bound : ∀ n, mapDomain tf n → n < next) :
    (∀ n, mapDomain (tf.update (next, ptr)) n →
      allTimestamps refs (.block next tag children :: stack) n) ∧
    (∀ n, mapDomain (tf.update (next, ptr)) n → n < next + 1) := by
  constructor
  · intro n ⟨value, lookup⟩
    by_cases same : n = next
    · subst n
      exact (allTimestamps_freshBlock refs stack children next tag childrenOnStack next).2 (Or.inl rfl)
    · have old : mapDomain tf n := by
        refine ⟨value, ?_⟩
        simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      exact (allTimestamps_freshBlock refs stack children next tag childrenOnStack n).2 (Or.inr (times n old))
  · intro n ⟨value, lookup⟩
    by_cases same : n = next
    · omega
    · have old : mapDomain tf n := by
        refine ⟨value, ?_⟩
        simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      have := bound n old
      omega

/-- Extending an injective timestamp map with an unused heap location keeps
it injective into the enlarged set of valid heap cells. -/
theorem freshBlock_timestampMap_injective (tf : HolFiniteMapExact Nat Nat) (next ptr : Nat)
    (oldTarget newTarget : Nat → Prop) (injective : mapInjInto tf oldTarget)
    (preserved : ∀ p, oldTarget p → newTarget p) (newCell : newTarget ptr)
    (fresh : ∀ n, mapDomain tf n → holFapply tf n ≠ ptr) :
    mapInjInto (tf.update (next, ptr)) newTarget := by
  have lookupNew : (tf.update (next, ptr)).lookup next = some ptr := by
    simp [HolFiniteMapExact.update, FUPDATE]
  have lookupOld : ∀ n, n ≠ next → (tf.update (next, ptr)).lookup n = tf.lookup n := by
    intro n ne
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm ne]
  constructor
  · intro n ⟨value, lookup⟩
    by_cases same : n = next
    · subst n
      rw [holFapply_of_lookup lookupNew]
      exact newCell
    · have oldLookup : tf.lookup n = some value := by rw [← lookupOld n same]; exact lookup
      rw [holFapply_of_lookup lookup, ← holFapply_of_lookup oldLookup]
      exact preserved _ (injective.1 n ⟨value, oldLookup⟩)
  · intro x y ⟨⟨a, ax⟩, ⟨b, byLookup⟩⟩ equal
    by_cases xNew : x = next
    · subst x
      by_cases yNew : y = next
      · exact yNew.symm
      · have oldLookup : tf.lookup y = some b := by rw [← lookupOld y yNew]; exact byLookup
        have oldEq : holFapply tf y = ptr := by
          rw [holFapply_of_lookup lookupNew, holFapply_of_lookup byLookup] at equal
          rw [holFapply_of_lookup oldLookup]
          exact equal.symm
        exact False.elim (fresh y ⟨b, oldLookup⟩ oldEq)
    · by_cases yNew : y = next
      · subst y
        have oldLookup : tf.lookup x = some a := by rw [← lookupOld x xNew]; exact ax
        have oldEq : holFapply tf x = ptr := by
          rw [holFapply_of_lookup ax, holFapply_of_lookup lookupNew] at equal
          rw [holFapply_of_lookup oldLookup]
          exact equal
        exact False.elim (fresh x ⟨a, oldLookup⟩ oldEq)
      · have oldX : tf.lookup x = some a := by rw [← lookupOld x xNew]; exact ax
        have oldY : tf.lookup y = some b := by rw [← lookupOld y yNew]; exact byLookup
        apply injective.2 x y ⟨⟨a, oldX⟩, ⟨b, oldY⟩⟩
        rw [holFapply_of_lookup ax, holFapply_of_lookup byLookup] at equal
        simpa [holFapply_of_lookup oldX, holFapply_of_lookup oldY] using equal

/-- A new block whose fields are existing roots introduces no new reachable
references; it can only add another path to existing references. -/
theorem reachableRefs_freshBlock (refs : Spt (BvlSem.Ref Value)) (stack children : List Value)
    (stamp tag target : Nat) (childrenOnStack : ∀ child, child ∈ children → child ∈ stack) :
    reachableRefs (.block stamp tag children :: stack) refs target ↔ reachableRefs stack refs target := by
  constructor
  · rintro ⟨root, start, inStack, inRoot, path⟩
    rcases List.mem_cons.mp inStack with equal | old
    · subst root
      simp only [getRefs, List.mem_flatMap] at inRoot
      obtain ⟨child, childMem, inChild⟩ := inRoot
      exact ⟨child, start, childrenOnStack child childMem, inChild, path⟩
    · exact ⟨root, start, old, inRoot, path⟩
  · rintro ⟨root, start, inStack, inRoot, path⟩
    exact ⟨root, start, List.mem_cons_of_mem _ inStack, inRoot, path⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
