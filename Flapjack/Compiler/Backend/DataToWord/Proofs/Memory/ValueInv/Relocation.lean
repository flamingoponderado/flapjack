import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference
import Flapjack.Compiler.Backend.GcShared.Related
import Flapjack.FiniteMap.Composition

/-! Finite-map relocation facts used by the collector value invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- A composed map is defined precisely when both maps are defined along its
lookup path. This Flapjack lemma exposes the canonical map representation. -/
theorem mapDomain_compose (outer inner : HolFiniteMapExact Nat Nat) (key : Nat) :
    mapDomain (HolFiniteMapExact.compose outer inner) key ↔
      ∃ intermediate, inner.lookup key = some intermediate ∧ mapDomain outer intermediate := by
  constructor
  · rintro ⟨value, found⟩
    obtain ⟨intermediate, first, second⟩ :=
      (HolFiniteMapExact.lookup_compose_some outer inner key value).mp found
    exact ⟨intermediate, first, value, second⟩
  · rintro ⟨intermediate, first, value, second⟩
    exact ⟨value, HolFiniteMapExact.lookup_compose_of_lookup outer inner key intermediate value first second⟩

/-- Composing an injective reference map with a collector's heap relation
preserves injectivity into the relocated heap. This is a Flapjack proof step
for the stack/reference invariant. -/
theorem mapInjInto_gcRelated_compose {α β : Type}
    (f g : HolFiniteMapExact Nat Nat) (heap heap2 : List (HeapElement α β))
    (oldInjective : mapInjInto f (fun ptr => isSomeDataElement (heapLookup ptr heap)))
    (related : gcRelated g heap heap2) :
    mapInjInto (HolFiniteMapExact.compose g f) (fun ptr => isSomeDataElement (heapLookup ptr heap2)) := by
  constructor
  · intro key defined
    obtain ⟨middle, first, value, second⟩ := (mapDomain_compose g f key).mp defined
    have applied := HolFiniteMapExact.apply_compose_of_lookup g f key middle value first second
    rw [applied, holFapply_of_lookup first]
    exact related.1 middle (by rw [second]; simp)
  · intro x y domains equal
    obtain ⟨middleX, firstX, valueX, secondX⟩ := (mapDomain_compose g f x).mp domains.1
    obtain ⟨middleY, firstY, valueY, secondY⟩ := (mapDomain_compose g f y).mp domains.2
    have applyX := HolFiniteMapExact.apply_compose_of_lookup g f x middleX valueX firstX secondX
    have applyY := HolFiniteMapExact.apply_compose_of_lookup g f y middleY valueY firstY secondY
    rw [applyX, applyY, holFapply_of_lookup firstX, holFapply_of_lookup firstY] at equal
    have equalMiddle := related.2.1 middleX middleY (by rw [secondX]; simp) (by rw [secondY]; simp) equal
    apply oldInjective.2 x y ⟨⟨middleX, firstX⟩, ⟨middleY, firstY⟩⟩
    rw [holFapply_of_lookup firstX, holFapply_of_lookup firstY, equalMiddle]

/-- Collector relocation preserves the value invariant for numbers. This is
a Flapjack case of the larger value-relocation proof, not the full HOL result. -/
theorem valueInv_number_gcRelated {width : Nat} [NeZero width] (conf : Config) (i : Int)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (related : gcRelated g heap heap2)
    (domain : ∀ ptr u, x = .pointer ptr u → g.lookup ptr ≠ none)
    (valid : valueInv conf (.number i) refs (x, f, tf, heap)) :
    valueInv conf (.number i) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  have source := (valueInv_number conf i refs x f tf heap).mp valid
  apply (valueInv_number conf i refs (addrApply (holFapply g) x)
    (HolFiniteMapExact.compose g f) (HolFiniteMapExact.compose g tf) heap2).mpr
  by_cases small : smallInt width i
  · simp [small] at source ⊢
    subst x
    rfl
  · simp only [small, if_false] at source ⊢
    obtain ⟨ptr, rfl, found⟩ := source
    have defined := domain ptr (.word 0) rfl
    cases parts : Misc.Multiword.i2mw (width := width) i with
    | mk sign words =>
      have original : heapLookup ptr heap = some (.dataElement [] words.length (.numTag sign, words.map .word)) := by
        simpa [bignumRep, parts] using found
      obtain ⟨moved, _⟩ := related.2.2.2 ptr [] words.length (.numTag sign, words.map .word) defined original
      refine ⟨holFapply g ptr, rfl, ?_⟩
      simpa [bignumRep, parts, addrMap] using moved

/-- Collector relocation preserves the value invariant for fixed-width words.
This is a Flapjack case of the larger value-relocation proof. -/
theorem valueInv_word64_gcRelated {width : Nat} [NeZero width] (conf : Config) (word : BitVec 64)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (related : gcRelated g heap heap2)
    (domain : ∀ ptr u, x = .pointer ptr u → g.lookup ptr ≠ none)
    (valid : valueInv conf (.word64 word) refs (x, f, tf, heap)) :
    valueInv conf (.word64 word) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  obtain ⟨ptr, rfl, found⟩ := (valueInv_word64 conf word refs x f tf heap).mp valid
  have defined := domain ptr (.word 0) rfl
  obtain ⟨words, representation⟩ := word64RepDataElement (width := width) word
  rw [representation] at found
  obtain ⟨moved, _⟩ := related.2.2.2 ptr [] words.length (.word64Tag, words) defined found
  apply (valueInv_word64 conf word refs (addrApply (holFapply g) (.pointer ptr (.word 0)))
    (HolFiniteMapExact.compose g f) (HolFiniteMapExact.compose g tf) heap2).mpr
  refine ⟨holFapply g ptr, rfl, ?_⟩
  simpa [representation, addrMap] using moved

/-- Code pointers remain valid under heap relocation. This is a Flapjack case
of the larger value-relocation proof. -/
theorem valueInv_codePtr_gcRelated {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (valid : valueInv conf (.codePtr n) refs (x, f, tf, heap)) :
    valueInv conf (.codePtr n) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  have source := (valueInv_codePtr conf n refs x f tf heap).mp valid
  subst x
  exact (valueInv_codePtr conf n refs _ _ _ heap2).mpr rfl

/-- Empty blocks remain valid under heap relocation. This is a Flapjack case
of the larger value-relocation proof. -/
theorem valueInv_emptyBlock_gcRelated {width : Nat} [NeZero width] (conf : Config) (stamp tag : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (valid : valueInv conf (.block stamp tag []) refs (x, f, tf, heap)) :
    valueInv conf (.block stamp tag []) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  obtain ⟨rfl, bound, stampEq⟩ := (valueInv_emptyBlock conf stamp tag refs x f tf heap).mp valid
  exact (valueInv_emptyBlock conf stamp tag refs _ _ _ heap2).mpr ⟨rfl, bound, stampEq⟩

/-- Relocation preserves references that do not point to thunks. This is a
case of the Flapjack value-relocation proof. -/
theorem valueInv_refPtr_nonThunk_gcRelated {width : Nat} [NeZero width]
    (conf : Config) (bit : Bool) (n : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (noThunk : ∀ mode value, sptLookup n refs ≠ some (.thunk mode value))
    (domain : ∀ ptr u, x = .pointer ptr u → g.lookup ptr ≠ none)
    (valid : valueInv conf (.refPtr bit n) refs (x, f, tf, heap)) :
    valueInv conf (.refPtr bit n) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  obtain ⟨⟨ptr, first⟩, noMut, position⟩ :=
    (valueInv_refPtr_notThunk conf bit n refs x f tf heap noThunk).mp valid
  have applyFirst : holFapply f n = ptr := holFapply_of_lookup first
  have defined : g.lookup ptr ≠ none := domain ptr _ (by simpa [applyFirst] using position)
  cases second : g.lookup ptr with
  | none => exact False.elim (defined second)
  | some target =>
    have composed := HolFiniteMapExact.lookup_compose_of_lookup g f n ptr target first second
    apply (valueInv_refPtr_notThunk conf bit n refs _ _ _ heap2 noThunk).mpr
    refine ⟨⟨target, composed⟩, noMut, ?_⟩
    simp [position, addrApply, applyFirst, holFapply_of_lookup second, holFapply_of_lookup composed]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
