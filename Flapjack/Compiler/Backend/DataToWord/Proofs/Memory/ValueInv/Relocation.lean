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

/-- A nonempty block can be relocated once its children satisfy the recursive
clocked relocation step. The collector relation supplies their pointer domains. -/
theorem clockValueInv_block_gcRelated {width : Nat} [NeZero width]
    (ck : Nat) (conf : Config) (stamp tag : Nat)
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (nonempty : values ≠ [])
    (related : gcRelated g heap heap2)
    (domain : ∀ ptr u, x = .pointer ptr u → g.lookup ptr ≠ none)
    (valid : valueInv conf (.block stamp tag values) refs (x, f, tf, heap))
    (recursive : ∀ child addr, valueInv conf child refs (addr, f, tf, heap) →
      (∀ ptr u, addr = .pointer ptr u → g.lookup ptr ≠ none) →
      ClockValueInv (ck - 1) conf child refs
        (addrApply (holFapply g) addr, HolFiniteMapExact.compose g f,
          HolFiniteMapExact.compose g tf, heap2)) :
    ClockValueInv ck conf (.block stamp tag values) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  obtain ⟨ptr, addresses, pair, timestamp, rfl, cell⟩ :=
    (valueInv_nonemptyBlock conf stamp tag values refs x f tf heap nonempty).mp valid
  have defined := domain ptr (.word (ptrBits conf tag addresses.length)) rfl
  have original : heapLookup ptr heap = some (.dataElement addresses addresses.length (.blockTag tag, [])) := by
    simpa [blockRep] using cell
  obtain ⟨moved, children⟩ := related.2.2.2 ptr addresses addresses.length (.blockTag tag, []) defined original
  have timestampMoved : (HolFiniteMapExact.compose g tf).lookup stamp = some (holFapply g ptr) := by
    cases found : g.lookup ptr with
    | none => exact False.elim (defined found)
    | some target =>
      simpa [holFapply_of_lookup found] using
        HolFiniteMapExact.lookup_compose_of_lookup g tf stamp ptr target timestamp found
  have movedCell : heapLookup (holFapply g ptr) heap2 = some (blockRep tag (addrMap (holFapply g) addresses)) := by
    simpa [blockRep, ← addrMap_length addresses (holFapply g)] using moved
  have relocateList : ∀ vs xs,
      List.Forall₂ (fun child addr => valueInv conf child refs (addr, f, tf, heap)) vs xs →
      (∀ ptr u, .pointer ptr u ∈ xs → g.lookup ptr ≠ none) →
      List.Forall₂ (fun child addr => ClockValueInv (ck - 1) conf child refs
        (addr, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2))
        vs (addrMap (holFapply g) xs) := by
    intro vs xs pair
    induction pair with
    | nil => intro _; exact .nil
    | @cons child addr rest addrs childValid tail ih =>
      intro children
      have childDomain : ∀ ptr u, addr = .pointer ptr u → g.lookup ptr ≠ none := by
        intro p u eq
        apply children p u
        simp [← eq]
      have head := recursive child addr childValid childDomain
      have tailChildren : ∀ ptr u, .pointer ptr u ∈ addrs → g.lookup ptr ≠ none := by
        intro p u member
        apply children p u
        simp [member]
      have tailRelocated := ih tailChildren
      cases addr <;> simp only [addrMap] <;> apply List.Forall₂.cons
      all_goals first | simpa [addrApply] using head | exact tailRelocated
  have relocated := relocateList values addresses pair children
  have result := ClockValueInv.blockCons ck conf stamp tag (holFapply g ptr) values
    (addrMap (holFapply g) addresses) refs (HolFiniteMapExact.compose g f)
    (HolFiniteMapExact.compose g tf) heap2 nonempty
    (fun _ => (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr relocated) timestampMoved movedCell
  simpa [addrApply, ← addrMap_length addresses (holFapply g)] using result

/-- Relocate an unevaluated thunk reference, using the recursive relocation
step for the thunk's payload. -/
theorem clockValueInv_unevaluatedThunk_gcRelated {width : Nat} [NeZero width]
    (ck : Nat) (conf : Config) (n : Nat) (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f tf g : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width)
    (found : sptLookup n refs = some (.thunk .notEvaluated value))
    (related : gcRelated g heap heap2)
    (domain : ∀ ptr u, x = .pointer ptr u → g.lookup ptr ≠ none)
    (valid : valueInv conf (.refPtr false n) refs (x, f, tf, heap))
    (recursive : ∀ addr, valueInv conf value refs (addr, f, tf, heap) →
      (∀ ptr u, addr = .pointer ptr u → g.lookup ptr ≠ none) →
      ClockValueInv (ck - 1) conf value refs
        (addrApply (holFapply g) addr, HolFiniteMapExact.compose g f,
          HolFiniteMapExact.compose g tf, heap2)) :
    ClockValueInv ck conf (.refPtr false n) refs
      (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) := by
  obtain ⟨addr, rfl, ⟨ptr, first⟩, cell, childValid⟩ :=
    (valueInv_refPtr_notEvaluated conf n value refs x f tf heap found).mp valid
  have applyFirst : holFapply f n = ptr := holFapply_of_lookup first
  have defined : g.lookup ptr ≠ none := by
    apply domain ptr (.word 0)
    simp [applyFirst]
  have original : heapLookup ptr heap = some (.dataElement [addr] 1 (.thunkTag .notEvaluated, [])) := by
    simpa [thunkBlock, applyFirst] using cell
  obtain ⟨moved, children⟩ := related.2.2.2 ptr [addr] 1 (.thunkTag .notEvaluated, []) defined original
  have childDomain : ∀ p u, addr = .pointer p u → g.lookup p ≠ none := by
    intro p u eq
    apply children p u
    simp [← eq]
  have childMoved := recursive addr childValid childDomain
  cases second : g.lookup ptr with
  | none => exact False.elim (defined second)
  | some target =>
    have composed := HolFiniteMapExact.lookup_compose_of_lookup g f n ptr target first second
    have movedCell : heapLookup (holFapply (HolFiniteMapExact.compose g f) n) heap2 =
        some (thunkBlock .notEvaluated (addrApply (holFapply g) addr)) := by
      cases addr <;> simpa [thunkBlock, addrMap, addrApply, holFapply_of_lookup composed,
        holFapply_of_lookup second] using moved
    have result := ClockValueInv.refPtrThunk ck conf .notEvaluated n value
      (addrApply (holFapply g) addr) refs (HolFiniteMapExact.compose g f)
      (HolFiniteMapExact.compose g tf) heap2 found (by intro impossible; cases impossible)
      ⟨target, composed⟩ movedCell (fun _ => childMoved)
    simpa [addrApply, applyFirst, holFapply_of_lookup composed, holFapply_of_lookup second] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
