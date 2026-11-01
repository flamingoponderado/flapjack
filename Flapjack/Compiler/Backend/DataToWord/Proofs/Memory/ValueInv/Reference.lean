import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv

/-! Reference cases for the data-to-word value relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The unbounded relation holds exactly when the clocked relation holds at
every clock, with the source's explicit tuple components. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_eq"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_eq_explicit {width : Nat} [NeZero width] (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat)
    (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf value refs (x,f,tf,heap) ↔
      ∀ ck, ClockValueInv ck conf value refs (x,f,tf,heap) := Iff.rfl

/-- Lowering the clock preserves a related data value. The two finite maps
are explicit here, matching the source theorem's quantified parameters. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_ck_mono"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem clockValueInv_mono_explicit {width : Nat} [NeZero width] (ck : Nat) (conf : Config)
    (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat)
    (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    ClockValueInv ck conf value refs (x,f,tf,heap) →
      ∀ ck', ck' ≤ ck → ClockValueInv ck' conf value refs (x,f,tf,heap) :=
  clockValueInv_mono ck conf value refs (x,f,tf,heap)

/-- A non-mutable-block cell has the zero reference annotation. -/
private theorem refPtrAnnot_zero_of_noMut {width : Nat} [NeZero width] {α : Type} (conf : Config)
    (cell : Option (BvlSem.Ref α))
    (noMut : ∀ tag finalised left child right, cell ≠ some (.mutBlock tag finalised left child right)) :
    refPtrAnnot (width := width) conf cell = .word 0 := by
  cases cell with
  | none => rfl
  | some cell =>
      cases cell with
      | valueArray _ => rfl
      | byteArray _ _ => rfl
      | thunk _ _ => rfl
      | mutBlock tag finalised left child right => exact False.elim (noMut tag finalised left child right rfl)

/-- Pointer-comparison references exclude thunks and mutable blocks. This is a Flapjack case helper. -/
theorem valueInv_refPtr_true {width : Nat} [NeZero width] (conf : Config) (n : Nat) (refs : Spt (BvlSem.Ref Value))
    (x : HeapAddress (WordLocW width)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.refPtr true n) refs (x,f,tf,heap) ↔
      (∃ ptr, f.lookup n = some ptr) ∧
      (∀ mode value, sptLookup n refs ≠ some (.thunk mode value)) ∧
      (∀ tag finalised left child right, sptLookup n refs ≠ some (.mutBlock tag finalised left child right)) ∧
      x = .pointer (holFapply f n) (.word 0) := by
  constructor
  · intro all
    have related := all 0
    cases related with
    | refPtr _ _ _ _ _ _ _ _ domain noThunk noMut =>
        have noMut' : ∀ tag finalised left child right,
            sptLookup n refs ≠ some (.mutBlock tag finalised left child right) := by
          intro tag finalised left child right found
          have bad := noMut tag finalised left child right found
          cases bad
        refine ⟨domain, noThunk, noMut', ?_⟩
        rw [refPtrAnnot_zero_of_noMut conf _ noMut']
  · rintro ⟨domain, noThunk, noMut, position⟩ ck
    have annot := refPtrAnnot_zero_of_noMut (width := width) conf (sptLookup n refs) noMut
    rw [position, ← annot]
    exact .refPtr true ck conf n refs f tf heap domain noThunk
      (by intro tag finalised left child right found; exact False.elim (noMut tag finalised left child right found))


/-- Non-thunk references use the direct reference-pointer case. This is a Flapjack case helper. -/
theorem valueInv_refPtr_notThunk {width : Nat} [NeZero width] (conf : Config) (bit : Bool) (n : Nat)
    (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (noThunk : ∀ mode value, sptLookup n refs ≠ some (.thunk mode value)) :
    valueInv conf (.refPtr bit n) refs (x,f,tf,heap) ↔
      (∃ ptr, f.lookup n = some ptr) ∧
      (∀ tag finalised left child right,
        sptLookup n refs = some (.mutBlock tag finalised left child right) → bit = false) ∧
      x = .pointer (holFapply f n) (refPtrAnnot conf (sptLookup n refs)) := by
  constructor
  · intro all
    have related := all 0
    cases related with
    | refPtr _ _ _ _ _ _ _ _ domain _ noMut => exact ⟨domain, noMut, rfl⟩
    | refPtrThunk _ _ mode _ value _ _ _ _ _ found _ _ _ _ =>
        exact False.elim (noThunk mode value found)
    | refPtrThunkInlined _ _ _ value _ _ _ _ _ found _ _ =>
        exact False.elim (noThunk .evaluated value found)
  · rintro ⟨domain, noMut, rfl⟩ ck
    exact .refPtr bit ck conf n refs f tf heap domain noThunk noMut


/-- Invert a clocked reference to an unevaluated thunk. This is a Flapjack case helper. -/
theorem clockValueInv_notEvaluated {width : Nat} [NeZero width] (ck : Nat) (conf : Config) (n : Nat)
    (value : Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (found : sptLookup n refs = some (.thunk .notEvaluated value))
    (related : ClockValueInv ck conf (.refPtr false n) refs (x, f, tf, heap)) :
    ∃ addr, x = .pointer (holFapply f n) (.word 0) ∧ (∃ ptr, f.lookup n = some ptr) ∧
      heapLookup (holFapply f n) heap = some (thunkBlock .notEvaluated addr) ∧
      (ck ≠ 0 → ClockValueInv (ck - 1) conf value refs (addr, f, tf, heap)) := by
  cases related with
  | refPtr _ _ _ _ _ _ _ _ _ noThunk _ =>
      exact False.elim (noThunk .notEvaluated value found)
  | refPtrThunk _ _ mode _ child addr _ _ _ _ found2 _ domain cell recursive =>
      have eq : BvlSem.Ref.thunk mode child = .thunk .notEvaluated value :=
        Option.some.inj (found2.symm.trans found)
      cases eq
      exact ⟨addr, rfl, domain, cell, recursive⟩
  | refPtrThunkInlined _ _ _ child _ _ _ _ _ found2 _ _ =>
      have eq : BvlSem.Ref.thunk .evaluated child = .thunk .notEvaluated value :=
        Option.some.inj (found2.symm.trans found)
      cases eq

/-- Unevaluated-thunk references have one fixed related heap payload. This is a Flapjack case helper. -/
theorem valueInv_refPtr_notEvaluated {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (value : Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (found : sptLookup n refs = some (.thunk .notEvaluated value)) :
    valueInv conf (.refPtr false n) refs (x,f,tf,heap) ↔
      ∃ addr, x = .pointer (holFapply f n) (.word 0) ∧ (∃ ptr, f.lookup n = some ptr) ∧
        heapLookup (holFapply f n) heap = some (thunkBlock .notEvaluated addr) ∧
        valueInv conf value refs (addr, f, tf, heap) := by
  constructor
  · intro all
    obtain ⟨addr, xpos, domain, cell, _⟩ := clockValueInv_notEvaluated 0 conf n value refs x f tf heap found (all 0)
    refine ⟨addr, xpos, domain, cell, ?_⟩
    intro ck
    obtain ⟨addr2, _, _, cell2, recursive⟩ :=
      clockValueInv_notEvaluated (ck + 1) conf n value refs x f tf heap found (all (ck + 1))
    have ha : addr2 = addr := by
      have he := Option.some.inj (cell2.symm.trans cell)
      simp only [thunkBlock, HeapElement.dataElement.injEq, and_true, List.cons.injEq] at he
      exact he
    subst addr2
    have recResult := recursive (by omega)
    simpa using recResult
  · rintro ⟨addr, rfl, domain, cell, recursive⟩ ck
    refine .refPtrThunk ck conf .notEvaluated n value addr refs f tf heap found ?_ domain cell ?_
    · intro impossible; cases impossible
    · intro _; exact recursive (ck - 1)


/-- Flapjack proof infrastructure: two downward-closed clock predicates whose disjunction holds at every clock have one disjunct holding at every clock. -/
theorem allClocks_or_of_monotone (A B : Nat → Prop)
    (monoA : ∀ high low, low ≤ high → A high → A low)
    (monoB : ∀ high low, low ≤ high → B high → B low)
    (both : ∀ ck, A ck ∨ B ck) : (∀ ck, A ck) ∨ (∀ ck, B ck) := by
  classical
  by_cases allA : ∀ ck, A ck
  · exact Or.inl allA
  · right
    obtain ⟨bad, hbad⟩ := not_forall.mp allA
    intro ck
    rcases both (max bad ck) with ha | hb
    · exact False.elim (hbad (monoA _ _ (Nat.le_max_left _ _) ha))
    · exact monoB _ _ (Nat.le_max_right _ _) hb

/-- Invert a clocked evaluated thunk into stored or inlined alternatives. This is a Flapjack case helper. -/
theorem clockValueInv_evaluated {width : Nat} [NeZero width] (ck : Nat) (conf : Config) (n : Nat)
    (value : Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (found : sptLookup n refs = some (.thunk .evaluated value))
    (related : ClockValueInv ck conf (.refPtr false n) refs (x, f, tf, heap)) :
    (∃ addr, x = .pointer (holFapply f n) (.word 0) ∧ (∃ ptr, f.lookup n = some ptr) ∧
      heapLookup (holFapply f n) heap = some (thunkBlock .evaluated addr) ∧
      (ck ≠ 0 → ClockValueInv (ck - 1) conf value refs (addr, f, tf, heap))) ∨
      (ck ≠ 0 → ClockValueInv (ck - 1) conf value refs (x, f, tf, heap)) := by
  cases related with
  | refPtr _ _ _ _ _ _ _ _ _ noThunk _ => exact False.elim (noThunk .evaluated value found)
  | refPtrThunk _ _ mode _ child addr _ _ _ _ found2 _ domain cell recursive =>
      have eq : BvlSem.Ref.thunk mode child = .thunk .evaluated value := Option.some.inj (found2.symm.trans found)
      cases eq
      exact Or.inl ⟨addr, rfl, domain, cell, recursive⟩
  | refPtrThunkInlined _ _ _ child _ _ _ _ _ found2 _ recursive =>
      have eq : BvlSem.Ref.thunk .evaluated child = .thunk .evaluated value := Option.some.inj (found2.symm.trans found)
      cases eq
      exact Or.inr recursive

/-- An evaluated thunk has a uniformly stored or uniformly inlined value representation at all clocks. This is a Flapjack case helper. -/
theorem valueInv_refPtr_evaluated {width : Nat} [NeZero width] (conf : Config) (n : Nat)
    (value : Value) (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (found : sptLookup n refs = some (.thunk .evaluated value))
    (safe : destThunk value refs = .notThunk) :
    valueInv conf (.refPtr false n) refs (x,f,tf,heap) ↔
      (∃ addr, x = .pointer (holFapply f n) (.word 0) ∧ (∃ ptr, f.lookup n = some ptr) ∧
        heapLookup (holFapply f n) heap = some (thunkBlock .evaluated addr) ∧
        valueInv conf value refs (addr, f, tf, heap)) ∨ valueInv conf value refs (x, f, tf, heap) := by
  let A : Nat → Prop := fun ck => ∃ addr, x = .pointer (holFapply f n) (.word 0) ∧
    (∃ ptr, f.lookup n = some ptr) ∧ heapLookup (holFapply f n) heap = some (thunkBlock .evaluated addr) ∧
    ClockValueInv ck conf value refs (addr, f, tf, heap)
  let B : Nat → Prop := fun ck => ClockValueInv ck conf value refs (x, f, tf, heap)
  have monoA : ∀ high low, low ≤ high → A high → A low := by
    intro high low bound ⟨addr, xpos, domain, cell, related⟩
    exact ⟨addr, xpos, domain, cell, clockValueInv_mono high conf value refs _ related low bound⟩
  have monoB : ∀ high low, low ≤ high → B high → B low := by
    intro high low bound related
    exact clockValueInv_mono high conf value refs _ related low bound
  constructor
  · intro all
    have choices : ∀ ck, A ck ∨ B ck := by
      intro ck
      rcases clockValueInv_evaluated (ck + 1) conf n value refs x f tf heap found (all (ck + 1)) with h | h
      · obtain ⟨addr, xpos, domain, cell, recursive⟩ := h
        left
        exact ⟨addr, xpos, domain, cell, by simpa using recursive (by omega)⟩
      · right
        simpa using h (by omega)
    rcases allClocks_or_of_monotone A B monoA monoB choices with allA | allB
    · obtain ⟨addr, xpos, domain, cell, _⟩ := allA 0
      left
      refine ⟨addr, xpos, domain, cell, ?_⟩
      intro ck
      obtain ⟨addr2, _, _, cell2, related⟩ := allA ck
      have ha : addr2 = addr := by
        have he := Option.some.inj (cell2.symm.trans cell)
        simp only [thunkBlock, HeapElement.dataElement.injEq, and_true, List.cons.injEq] at he
        exact he
      subst addr2
      exact related
    · exact Or.inr allB
  · intro alternatives ck
    rcases alternatives with ⟨addr, rfl, domain, cell, recursive⟩ | recursive
    · refine .refPtrThunk ck conf .evaluated n value addr refs f tf heap found ?_ domain cell ?_
      · intro _; exact safe
      · intro _; exact recursive (ck - 1)
    · exact .refPtrThunkInlined ck conf n value x refs f tf heap found safe
        (fun _ => recursive (ck - 1))


/-- Reference-pointer helper for the assembled source case theorem. -/
theorem valueInv_refPtr {width : Nat} [NeZero width] (conf : Config) (bit : Bool) (n : Nat)
    (refs : Spt (BvlSem.Ref Value)) (x : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    valueInv conf (.refPtr bit n) refs (x,f,tf,heap) ↔
      ((∃ ptr, f.lookup n = some ptr) ∧
       (∀ mode value, sptLookup n refs ≠ some (.thunk mode value)) ∧
       (∀ tag finalised left child right, sptLookup n refs = some (.mutBlock tag finalised left child right) → bit = false) ∧
       x = .pointer (holFapply f n) (refPtrAnnot conf (sptLookup n refs))) ∨
      (∃ mode value addr, sptLookup n refs = some (.thunk mode value) ∧
       (mode = .evaluated → destThunk value refs = .notThunk) ∧ (∃ ptr, f.lookup n = some ptr) ∧
       heapLookup (holFapply f n) heap = some (thunkBlock mode addr) ∧
       valueInv conf value refs (addr,f,tf,heap) ∧ bit = false ∧ x = .pointer (holFapply f n) (.word 0)) ∨
      (∃ value, sptLookup n refs = some (.thunk .evaluated value) ∧
       destThunk value refs = .notThunk ∧ bit = false ∧ valueInv conf value refs (x,f,tf,heap)) := by
  constructor
  · intro all
    have related := all 0
    cases related with
    | refPtr _ _ _ _ _ _ _ _ domain noThunk noMut =>
        exact Or.inl ⟨domain, noThunk, noMut, rfl⟩
    | refPtrThunk _ _ mode _ value addr _ _ _ _ found safe _ _ _ =>
        cases mode with
        | notEvaluated =>
            obtain ⟨addr, xpos, domain, cell, recInv⟩ := (valueInv_refPtr_notEvaluated conf n value refs _ f tf heap found).mp all
            exact Or.inr (Or.inl ⟨.notEvaluated, value, addr, found, safe, domain, cell, recInv, rfl, xpos⟩)
        | evaluated =>
            rcases (valueInv_refPtr_evaluated conf n value refs _ f tf heap found (safe rfl)).mp all with ⟨addr, xpos, domain, cell, recInv⟩ | recInv
            · exact Or.inr (Or.inl ⟨.evaluated, value, addr, found, by intro _; exact safe rfl, domain, cell, recInv, rfl, xpos⟩)
            · exact Or.inr (Or.inr ⟨value, found, safe rfl, rfl, recInv⟩)
    | refPtrThunkInlined _ _ _ value _ _ _ _ _ found safe _ =>
        rcases (valueInv_refPtr_evaluated conf n value refs _ f tf heap found safe).mp all with ⟨addr, xpos, domain, cell, recInv⟩ | recInv
        · exact Or.inr (Or.inl ⟨.evaluated, value, addr, found, by intro _; exact safe, domain, cell, recInv, rfl, xpos⟩)
        · exact Or.inr (Or.inr ⟨value, found, safe, rfl, recInv⟩)
  · intro alternative ck
    rcases alternative with ⟨domain, noThunk, noMut, rfl⟩ | ⟨mode, value, addr, found, safe, domain, cell, recInv, rfl, rfl⟩ | ⟨value, found, safe, rfl, recInv⟩
    · exact .refPtr bit ck conf n refs f tf heap domain noThunk noMut
    · exact .refPtrThunk ck conf mode n value addr refs f tf heap found safe domain cell (fun _ => recInv (ck - 1))
    · exact .refPtrThunkInlined ck conf n value x refs f tf heap found safe (fun _ => recInv (ck - 1))

/-- All five unbounded value-invariant equations together, in source order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_def"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_cases {width : Nat} [NeZero width] (conf : Config) (i : Int)
    (word : BitVec 64) (n : Nat) (bit : Bool) (stamp : Nat)
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (x : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width) :
    (valueInv conf (.number i) refs (x,f,tf,heap) ↔
      if smallInt width i then x = .data (.word (smallnum i)) else
        ∃ ptr, x = .pointer ptr (.word 0) ∧ heapLookup ptr heap = some (bignumRep i)) ∧
    (valueInv conf (.word64 word) refs (x,f,tf,heap) ↔
      ∃ ptr, x = .pointer ptr (.word 0) ∧ heapLookup ptr heap = some (word64Rep word)) ∧
    (valueInv conf (.codePtr n) refs (x,f,tf,heap) ↔ x = .data (.loc n 0)) ∧
    (valueInv conf (.refPtr bit n) refs (x,f,tf,heap) ↔
      ((∃ ptr, f.lookup n = some ptr) ∧
       (∀ mode value, sptLookup n refs ≠ some (.thunk mode value)) ∧
       (∀ tag finalised left child right,
         sptLookup n refs = some (.mutBlock tag finalised left child right) → bit = false) ∧
       x = .pointer (holFapply f n) (refPtrAnnot conf (sptLookup n refs))) ∨
      (∃ mode value addr, sptLookup n refs = some (.thunk mode value) ∧
       (mode = .evaluated → destThunk value refs = .notThunk) ∧
       (∃ ptr, f.lookup n = some ptr) ∧
       heapLookup (holFapply f n) heap = some (thunkBlock mode addr) ∧
       valueInv conf value refs (addr,f,tf,heap) ∧ bit = false ∧
       x = .pointer (holFapply f n) (.word 0)) ∨
      (∃ value, sptLookup n refs = some (.thunk .evaluated value) ∧
       destThunk value refs = .notThunk ∧ bit = false ∧ valueInv conf value refs (x,f,tf,heap))) ∧
    (valueInv conf (.block stamp n values) refs (x,f,tf,heap) ↔
      if values = [] then
        x = .data (.word (blockNil n)) ∧ n < 2 ^ width / 16 ∧ stamp = 0
      else
        ∃ ptr xs, List.Forall₂ (fun value addr => valueInv conf value refs (addr,f,tf,heap)) values xs ∧
          tf.lookup stamp = some ptr ∧ x = .pointer ptr (.word (ptrBits conf n xs.length)) ∧
          heapLookup ptr heap = some (blockRep n xs)) := by
  exact ⟨valueInv_number conf i refs x f tf heap,
    valueInv_word64 conf word refs x f tf heap,
    valueInv_codePtr conf n refs x f tf heap,
    valueInv_refPtr conf bit n refs x f tf heap,
    valueInv_block conf stamp n values refs x f tf heap⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
