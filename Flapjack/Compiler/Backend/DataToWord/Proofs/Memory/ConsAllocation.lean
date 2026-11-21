module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.GcRefinement
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.HolArb

@[expose] public section

/-!
# Heap predicates and allocation of multiple cons cells

Counterparts of `isUnused_def`, `isSomeUnused_def`, `isDataElement_lemmas` and
the `list_to_BlockReps` group (through `list_to_v_get_refs`) of
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL `EVERY`
is a bounded universal, `MEM` is list membership and `cons_tag` is
`BackendCommon.consTag`. The unspecified `list_to_BlockReps conf t a [] = ARB`
clause is the reviewed `holArb`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.BackendCommon

/-- HOL `isUnused_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isUnused_def"]
def isUnused {α β : Type} (x : HeapElement α β) : Prop := ∃ k, x = .unused k

/-- HOL `isSomeUnused_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isSomeUnused_def"]
def isSomeUnused {α β : Type} (x : Option (HeapElement α β)) : Prop := ∃ k, x = some (.unused k)

/-- HOL `isDataElement_lemmas`; every conjunct has its own carriers, as
inferred by HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "isDataElement_lemmas"
  (words_as_type_indexed_bitvec)]
theorem isDataElement_lemmas {wa : Nat} {wi : Nat} {wn : Nat} [NeZero wa] [NeZero wi] [NeZero wn]
    {β γ δ ε ζ η θ κ κ' μ : Type}
    (x1 : List (HeapAddress β)) (x2 : Nat) (x3 : γ) (tag : Nat) (ys1 : List (HeapAddress δ))
    (w : BitVec 64) (ws : List (HeapAddress η)) (y1 y2 : Bool) (y3 : List (BitVec 8))
    (y4 : List (BitVec wi)) (ev : AstHOL.ThunkMode) (v : HeapAddress κ) (i : Int) :
    isDataElement (HeapElement.dataElement x1 x2 x3) ∧
      isDataElement (blockRep tag ys1 : HeapElement δ (HeapTag × List ε)) ∧
      isDataElement (word64Rep w : HeapElement ζ (HeapTag × List (WordLocW wa))) ∧
      isDataElement (refBlock ws : HeapElement η (HeapTag × List θ)) ∧
      isDataElement (bytesRep y1 y2 y3 y4) ∧
      isDataElement (thunkBlock ev v : HeapElement κ (HeapTag × List κ')) ∧
      isDataElement (bignumRep i : HeapElement μ (HeapTag × List (WordLocW wn))) := by
  refine ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ?_, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩,
    ⟨_, _, _, rfl⟩⟩
  unfold word64Rep
  split <;> exact ⟨_, _, _, rfl⟩

/-- HOL `list_to_BlockReps_def`: consecutive cons blocks for a list, the last
pointing to `t`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_def"
  (words_as_type_indexed_bitvec)]
noncomputable def listToBlockReps {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (t : HeapAddress (WordLocW width)) (a : Nat) :
    List (HeapAddress (WordLocW width)) → List (HeapElement (WordLocW width) (HeapTag × List β))
  | [] => holArb _
  | h :: l =>
    match l with
    | [] => [blockRep consTag [h, t]]
    | _ :: _ =>
      blockRep consTag [h, .pointer (a + 3) (.word (ptrBits conf consTag 2))] ::
        listToBlockReps conf t (a + 3) l

/-- The two non-trivial unfolding cases. -/
theorem listToBlockReps_single {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (t h : HeapAddress (WordLocW width)) (a : Nat) :
    (listToBlockReps conf t a [h] : List (HeapElement _ (HeapTag × List β))) = [blockRep consTag [h, t]] := by
  simp [listToBlockReps]

theorem listToBlockReps_cons {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (t h h' : HeapAddress (WordLocW width)) (a : Nat)
    (l : List (HeapAddress (WordLocW width))) :
    (listToBlockReps conf t a (h :: h' :: l) : List (HeapElement _ (HeapTag × List β))) =
      blockRep consTag [h, .pointer (a + 3) (.word (ptrBits conf consTag 2))] ::
        listToBlockReps conf t (a + 3) (h' :: l) := by
  simp [listToBlockReps]

/-- HOL `list_to_BlockReps_heap_length`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_heap_length"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_heapLength {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) :
    ∀ (xs : List (HeapAddress (WordLocW width))) (len : Nat), xs ≠ [] →
      heapLength (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))) = 3 * xs.length := by
  intro xs
  induction xs with
  | nil => intro len h; exact absurd rfl h
  | cons h l ih =>
    intro len _
    cases l with
    | nil => simp [listToBlockReps_single, heapLength, elLength, blockRep]
    | cons h' l' =>
      rw [listToBlockReps_cons]
      have := ih (len + 3) (by simp)
      simp only [heapLength, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
      simp [elLength, blockRep]
      omega

/-- HOL `heap_lookup_heap_length`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_heap_length"]
theorem heapLookup_heapLength {α β : Type} (h1 h2 : List (HeapElement α β)) :
    heapLookup (heapLength h1) (h1 ++ h2) = heapLookup 0 h2 := by
  rw [heapLookup_append1 h1 _ h2 (Nat.le_refl _), Nat.sub_self]

/-- HOL `list_to_BlockReps_heap_lookup_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_heap_lookup_0"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_heapLookup_zero {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (xs : List (HeapAddress (WordLocW width))) :
    xs ≠ [] →
      isSomeDataElement (heapLookup 0 (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β)))) := by
  intro ne
  match xs, ne with
  | [h], _ => simp [listToBlockReps_single, heapLookup, blockRep, isSomeDataElement]
  | h :: h' :: l, _ => simp [listToBlockReps_cons, heapLookup, blockRep, isSomeDataElement]

/-- HOL `list_to_BlockReps_isDataElement`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_isDataElement"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_isDataElement {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) :
    ∀ (xs : List (HeapAddress (WordLocW width))) (x : HeapAddress (WordLocW width)) (len : Nat), xs ≠ [] →
      ∀ e ∈ (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))), isDataElement e := by
  intro xs
  induction xs with
  | nil => intro x len h; exact absurd rfl h
  | cons h l ih =>
    intro x len _
    cases l with
    | nil =>
      intro e member
      rw [listToBlockReps_single, List.mem_singleton] at member
      subst member
      exact ⟨_, _, _, rfl⟩
    | cons h' l' =>
      intro e member
      rw [listToBlockReps_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, _, _, rfl⟩
      · exact ih x (len + 3) (by simp) e member

/-- HOL `list_to_BlockReps_data_up_to_lem`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_data_up_to_lem"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_dataUpTo_lem {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (xs : List (HeapAddress (WordLocW width))) (h1 h2 : List (HeapElement (WordLocW width) (HeapTag × List β))) :
    xs ≠ [] ∧ h1 = listToBlockReps conf x len xs → dataUpTo (heapLength h1) (h1 ++ h2) := by
  rintro ⟨ne, rfl⟩
  exact (dataUpTo_append _ h2).mpr (listToBlockReps_isDataElement conf xs x len ne)

/-- HOL `list_to_BlockReps_data_up_to`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_data_up_to"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_dataUpTo {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (xs : List (HeapAddress (WordLocW width))) (h2 : List (HeapElement (WordLocW width) (HeapTag × List β))) :
    xs ≠ [] →
      dataUpTo (heapLength (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))))
        (listToBlockReps conf x len xs ++ h2) :=
  fun ne => listToBlockReps_dataUpTo_lem conf x len xs _ h2 ⟨ne, rfl⟩

/-- HOL `list_to_BlockReps_ForwardPointer`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_ForwardPointer"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_forwardPointer {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (xs : List (HeapAddress (WordLocW width))) :
    xs ≠ [] →
      (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))).filter isForwardPointer = [] := by
  intro ne
  rw [List.filter_eq_nil_iff]
  intro e member
  obtain ⟨_, _, _, rfl⟩ := listToBlockReps_isDataElement conf xs x len ne e member
  simp [isForwardPointer]

/-- HOL `list_to_BlockReps_Ref`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_Ref"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_ref {width : Nat} [NeZero width] {β : Type} :
    ∀ (xs : List (HeapAddress (WordLocW width))) (len : Nat) (x : HeapAddress (WordLocW width))
      (conf : Flapjack.Compiler.Backend.DataToWord.Config), xs ≠ [] →
      ∀ v ∈ (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))), ¬ isRef v := by
  intro xs
  induction xs with
  | nil => intro len x conf h; exact absurd rfl h
  | cons h l ih =>
    intro len x conf _
    cases l with
    | nil =>
      intro e member
      rw [listToBlockReps_single, List.mem_singleton] at member
      subst member
      simp [isRef, blockRep, isMutTag]
    | cons h' l' =>
      intro e member
      rw [listToBlockReps_cons, List.mem_cons] at member
      rcases member with rfl | member
      · simp [isRef, blockRep, isMutTag]
      · exact ih (len + 3) x conf (by simp) e member

/-- HOL `list_to_BlockReps_NULL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_NULL"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_ne_nil {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (xs : List (HeapAddress (WordLocW width))) :
    xs ≠ [] → (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))) ≠ [] := by
  intro ne
  match xs, ne with
  | [h], _ => simp [listToBlockReps_single]
  | h :: h' :: l, _ => simp [listToBlockReps_cons]

/-- HOL `list_to_BlockReps_MEM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_MEM"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_mem {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) (len : Nat)
    (h : HeapAddress (WordLocW width)) (t : List (HeapAddress (WordLocW width)))
    (v : HeapElement (WordLocW width) (HeapTag × List β)) :
    v ∈ (listToBlockReps conf x len (h :: t) : List (HeapElement _ (HeapTag × List β))) →
      v ∈ (listToBlockReps conf x (len + 3) t : List (HeapElement _ (HeapTag × List β))) ∨
        v = blockRep consTag [h, .pointer (len + 3) (.word (ptrBits conf consTag 2))] ∨
        v = blockRep consTag [h, x] := by
  intro member
  cases t with
  | nil =>
    rw [listToBlockReps_single, List.mem_singleton] at member
    exact Or.inr (Or.inr member)
  | cons h' l =>
    rw [listToBlockReps_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl member

/-- A two-address block occupies three heap words. -/
theorem heapLength_cons_blockRep2 {α β : Type} (tag : Nat) (a b : HeapAddress α)
    (rest : List (HeapElement α (HeapTag × List β))) :
    heapLength (blockRep tag [a, b] :: rest) = 3 + heapLength rest := by
  simp [heapLength, elLength, blockRep]

/-- Lookup past a leading two-address block. -/
theorem heapLookup_cons_blockRep2 {α β : Type} (tag : Nat) (a b : HeapAddress α)
    (rest : List (HeapElement α (HeapTag × List β))) (n : Nat) (h : 3 ≤ n) :
    heapLookup n (blockRep tag [a, b] :: rest) = heapLookup (n - 3) rest := by
  have := heapLookup_append1 [blockRep tag [a, b]] n rest (by simp [heapLength, elLength, blockRep]; omega)
  simpa [heapLength, elLength, blockRep] using this

/-- HOL `list_to_BlockReps_Pointer_lem` (its `let` is the local name `allocd`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_Pointer_lem"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_pointer_lem {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) :
    ∀ (xs : List (HeapAddress (WordLocW width))) (len : Nat) (ys : List (HeapAddress (WordLocW width)))
      (l : Nat) (d : HeapTag × List β) (ptr : Nat) (u : WordLocW width),
      let allocd := (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β)))
      xs ≠ [] ∧ HeapElement.dataElement ys l d ∈ allocd ∧ HeapAddress.pointer ptr u ∈ ys →
        HeapAddress.pointer ptr u = x ∨ HeapAddress.pointer ptr u ∈ xs ∨
          (ptr < len + heapLength allocd ∧ ptr > len ∧ isSomeDataElement (heapLookup (ptr - len) allocd)) := by
  intro xs
  induction xs with
  | nil =>
    intro len ys l d ptr u
    dsimp only
    rintro ⟨h, _⟩
    exact absurd rfl h
  | cons h t ih =>
    intro len ys l d ptr u
    dsimp only
    rintro ⟨_, member, pointer⟩
    cases t with
    | nil =>
      rw [listToBlockReps_single, List.mem_singleton] at member
      simp only [blockRep, HeapElement.dataElement.injEq] at member
      obtain ⟨rfl, -, -⟩ := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at pointer
      rcases pointer with eq | eq
      · exact Or.inr (Or.inl (by simp [eq]))
      · exact Or.inl eq
    | cons h' t' =>
      rw [listToBlockReps_cons] at member ⊢
      rw [List.mem_cons] at member
      have restLen := listToBlockReps_heapLength (β := β) conf x (h' :: t') (len + 3) (by simp)
      rw [heapLength_cons_blockRep2]
      rcases member with member | member
      · simp only [blockRep, HeapElement.dataElement.injEq] at member
        obtain ⟨rfl, -, -⟩ := member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at pointer
        rcases pointer with eq | eq
        · exact Or.inr (Or.inl (by simp [eq]))
        · simp only [HeapAddress.pointer.injEq] at eq
          obtain ⟨rfl, -⟩ := eq
          refine Or.inr (Or.inr ⟨?_, by omega, ?_⟩)
          · simp at restLen
            omega
          · rw [heapLookup_cons_blockRep2 (n := len + 3 - len) (h := by omega), show len + 3 - len - 3 = 0 by omega]
            exact listToBlockReps_heapLookup_zero (β := β) conf x (len + 3) (h' :: t') (by simp)
      · have step := ih (len + 3) ys l d ptr u
        dsimp only at step
        rcases step ⟨by simp, member, pointer⟩ with eq | inner | ⟨lt, gt, found⟩
        · exact Or.inl eq
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ inner))
        · refine Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)
          rw [heapLookup_cons_blockRep2 (n := ptr - len) (h := by omega), show ptr - len - 3 = ptr - (len + 3) by omega]
          exact found

/-- HOL `list_to_BlockReps_Pointer`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_BlockReps_Pointer"
  (words_as_type_indexed_bitvec)]
theorem listToBlockReps_pointer {width : Nat} [NeZero width] {β : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (x : HeapAddress (WordLocW width)) :
    ∀ (xs : List (HeapAddress (WordLocW width))) (len : Nat) (ys : List (HeapAddress (WordLocW width)))
      (l : Nat) (d : HeapTag × List β) (ptr : Nat) (u : WordLocW width),
      xs ≠ [] ∧ HeapElement.dataElement ys l d ∈ (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))) ∧
          HeapAddress.pointer ptr u ∈ ys →
        HeapAddress.pointer ptr u = x ∨ HeapAddress.pointer ptr u ∈ xs ∨
          (ptr < len + heapLength (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))) ∧
            ptr > len ∧
            isSomeDataElement (heapLookup (ptr - len) (listToBlockReps conf x len xs : List (HeapElement _ (HeapTag × List β))))) :=
  listToBlockReps_pointer_lem conf x

/-- HOL `list_to_v_get_refs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_to_v_get_refs"]
theorem listToValue_getRefs :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (t : Flapjack.Compiler.Backend.DataSem.Value)
      (r ts : Nat), r ∈ getRefs (listToValue ts t xs) → ∃ x, (x ∈ xs ∨ x = t) ∧ r ∈ getRefs x := by
  intro xs
  induction xs with
  | nil => intro t r ts h; exact ⟨t, Or.inr rfl, h⟩
  | cons y ys ih =>
    intro t r ts h
    simp only [listToValue, getRefs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at h
    rcases h with h | h
    · exact ⟨y, Or.inl (by simp), h⟩
    · obtain ⟨x, member, hx⟩ := ih t r (ts + 1) h
      exact ⟨x, member.imp (List.mem_cons_of_mem _) id, hx⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
