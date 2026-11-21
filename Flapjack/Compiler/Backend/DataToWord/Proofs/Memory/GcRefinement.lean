module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Relocation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.EvaluatedThunk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Preliminaries
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialSplit
public import Flapjack.FiniteMap.Composition

@[expose] public section

/-!
# Refinement is maintained past collector calls

Counterparts of the declarations from `v_inv_related_lemma` to
`data_up_to_APPEND` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`: relocation
of the value and reference invariants by a collector, the evaluated-thunk
inlining relations `gc_inline_rel`/`gc_heap_inline_rel`, and their effect on
the stack/reference invariant. HOL `f_o_f` is the tagged
`HolFiniteMapExact.compose`, `FAPPLY` is `holFapply`, and `x ∈ FDOM g` is
`g.lookup x ≠ none`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `v_inv_related_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_related_lemma"
  (fmap_as_finite_support_relation := [f, tf, g]) (words_as_type_indexed_bitvec)]
theorem valueInv_related_lemma {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (g : HolFiniteMapExact Nat Nat) (heap2 : ValueHeap width) :
    ∀ (ck : Nat) (w : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap1 : ValueHeap width),
      valueInv conf w refs (x, f, tf, heap1) ∧ gcRelated g heap1 heap2 ∧
        (∀ (ptr : Nat) (u : WordLocW width), x = .pointer ptr u → g.lookup ptr ≠ none) →
      ClockValueInv ck conf w refs
          (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) ∧
        ∀ n ∈ getRefs w, ¬ evaluatedThunkPtr refs n → g.lookup (holFapply f n) ≠ none := by
  rintro ck w refs x f tf heap1 ⟨valid, related, domain⟩
  refine ⟨clockValueInv_gcRelated ck conf w refs x f tf g heap1 heap2 related domain valid, ?_⟩
  intro n member notEvaluated
  apply valueInv_getRefs_gcDomain conf w refs x f tf g heap1 heap2 related domain valid n member
  intro child found
  exact notEvaluated ⟨child, found⟩

/-- HOL `v_inv_related`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_related"
  (fmap_as_finite_support_relation := [f, tf, g]) (words_as_type_indexed_bitvec)]
theorem valueInv_related {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (g : HolFiniteMapExact Nat Nat) (heap1 heap2 : ValueHeap width) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) :
    ∀ (w : Flapjack.Compiler.Backend.DataSem.Value) (x : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat)
      (tf : HolFiniteMapExact Nat Nat),
      gcRelated g heap1 heap2 ∧
        (∀ (ptr : Nat) (u : WordLocW width), x = .pointer ptr u → g.lookup ptr ≠ none) ∧
        valueInv conf w refs (x, f, tf, heap1) →
      valueInv conf w refs
          (addrApply (holFapply g) x, HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2) ∧
        ∀ n ∈ getRefs w, ¬ evaluatedThunkPtr refs n → g.lookup (holFapply f n) ≠ none := by
  rintro w x f tf ⟨related, domain, valid⟩
  refine ⟨fun ck => (valueInv_related_lemma conf g heap2 ck w refs x f tf heap1 ⟨valid, related, domain⟩).1,
    (valueInv_related_lemma conf g heap2 0 w refs x f tf heap1 ⟨valid, related, domain⟩).2⟩

/-- HOL `EVERY2_ADDR_MAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_ADDR_MAP"]
theorem every2_addrMap {α β : Type} (P : HeapAddress α → β → Prop) (g : Nat → Nat) :
    ∀ (zs : List (HeapAddress α)) (l : List β),
      List.Forall₂ P (addrMap g zs) l ↔ List.Forall₂ (fun x y => P (addrApply g x) y) zs l := by
  intro zs
  induction zs with
  | nil => intro l; simp [addrMap]
  | cons z zs ih =>
    intro l
    cases l with
    | nil => cases z <;> simp [addrMap]
    | cons y ys => cases z <;> simp [addrMap, addrApply, ih]

/-- HOL `bc_ref_inv_related`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_ref_inv_related"
  (fmap_as_finite_support_relation := [f, tf, g]) (words_as_type_indexed_bitvec)]
theorem bcRefInv_related {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (g : HolFiniteMapExact Nat Nat)
    (heap1 heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be : Bool) :
    gcRelated g heap1 heap2 ∧ bcRefInv conf n refs (f, tf, heap1, be) ∧ g.lookup (holFapply f n) ≠ none →
      bcRefInv conf n refs (HolFiniteMapExact.compose g f, HolFiniteMapExact.compose g tf, heap2, be) := by
  rintro ⟨related, valid, domain⟩
  exact bcRefInv_gcRelated conf n refs f tf g heap1 heap2 be related valid domain

/-- HOL `gc_inline_rel`: a root is either unchanged or a pointer to a heap block
that the `inline` relation replaces by its content. The heap and root address
carriers are independent, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_inline_rel"]
inductive GcInlineRel {α β γ : Type} (inline : HeapElement α β → HeapAddress γ → Prop)
    (h1 : List (HeapElement α β)) : HeapAddress γ → HeapAddress γ → Prop where
  | unchanged (x : HeapAddress γ) : GcInlineRel inline h1 x x
  | inline (block : HeapElement α β) (p : Nat) (u : γ) (x : HeapAddress γ) :
      heapLookup p h1 = some block ∧ inline block x → GcInlineRel inline h1 (.pointer p u) x

/-- HOL `gc_heap_inline_rel`: a heap element is either unchanged or a data
element whose pointers are related by `gc_inline_rel`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_heap_inline_rel"]
inductive GcHeapInlineRel {α β γ δ : Type} (inline : HeapElement α β → HeapAddress γ → Prop)
    (h1 : List (HeapElement α β)) : HeapElement γ δ → HeapElement γ δ → Prop where
  | unchanged (x : HeapElement γ δ) : GcHeapInlineRel inline h1 x x
  | inline (d : δ) (n : Nat) (xs ys : List (HeapAddress γ)) :
      List.Forall₂ (GcInlineRel inline h1) xs ys →
        GcHeapInlineRel inline h1 (.dataElement xs n d) (.dataElement ys n d)

/-- HOL `gc_inline_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_inline_def"]
def gcInline {α β : Type} (inline : HeapElement α β → HeapAddress α → Prop) :
    List (HeapAddress α) × List (HeapElement α β) → List (HeapAddress α) × List (HeapElement α β) → Prop
  | (r1, h1), (r2, h2) =>
    List.Forall₂ (GcInlineRel inline h1) r1 r2 ∧ List.Forall₂ (GcHeapInlineRel inline h1) h1 h2

/-- HOL `gc_related_roots_heap_def`; root and heap address carriers are
independent. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_related_roots_heap_def"
  (fmap_as_finite_support_parameters := [f])]
def gcRelatedRootsHeap {α β γ : Type} (f : HolFiniteMapExact Nat Nat) :
    List (HeapAddress α) × List (HeapElement β γ) → List (HeapAddress α) × List (HeapElement β γ) → Prop
  | (r1, h1), (r2, h2) =>
    gcRelated f h1 h2 ∧ r2 = addrMap (holFapply f) r1 ∧
      ∀ (ptr : Nat) (u : α), .pointer ptr u ∈ r1 → f.lookup ptr ≠ none

/-- The finite-map parameter of `gcRelatedRootsHeap` has the canonical
lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_gcRelatedRootsHeap_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- HOL `gc_inline_related_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_inline_related_def"
  (fmap_as_finite_support_parameters := [f])]
def gcInlineRelated {α β : Type} (inline : HeapElement α β → HeapAddress α → Prop)
    (f : HolFiniteMapExact Nat Nat) :
    List (HeapAddress α) × List (HeapElement α β) → List (HeapAddress α) × List (HeapElement α β) → Prop
  | (r1, h1), (r2, h2) =>
    ∃ ri hi, gcInline inline (r1, h1) (ri, hi) ∧ gcRelatedRootsHeap f (ri, hi) (r2, h2)

/-- The finite-map parameter of `gcInlineRelated` has the canonical
lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_gcInlineRelated_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).lookup key = f.lookup key ∧
    (GcMapBroad.ofBroad (GcMapBroad.toBroad f)).finiteSupport = f.finiteSupport ∧
    GcMapBroad.ofBroad (GcMapBroad.toBroad f) = f :=
  holFmapAsFiniteSupportParamWitness_gcRelated_f f key

/-- Related heap elements have the same length and data-element status. -/
theorem gcHeapInlineRel_shape {α β γ δ : Type} {inline : HeapElement α β → HeapAddress γ → Prop}
    {h1 : List (HeapElement α β)} {x y : HeapElement γ δ} (rel : GcHeapInlineRel inline h1 x y) :
    elLength x = elLength y ∧ (isSomeDataElement (some x) ↔ isSomeDataElement (some y)) := by
  cases rel with
  | unchanged => exact ⟨rfl, Iff.rfl⟩
  | inline d n xs ys _ =>
    refine ⟨rfl, ?_⟩
    constructor <;> intro _ <;> exact ⟨_, _, _, rfl⟩

/-- HOL `gc_heap_inline_rel_heap_lookup`. The base heap of the inlining
relation has its own payload carrier. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_heap_inline_rel_heap_lookup"]
theorem gcHeapInlineRel_heapLookup {α β γ : Type} (heap : List (HeapElement α (HeapTag × List γ))) :
    ∀ (heap1 heap2 : List (HeapElement α β)),
      List.Forall₂ (GcHeapInlineRel (DestEvaluatedThunkRel (α := α) (β := γ)) heap) heap1 heap2 →
      ∀ a : Nat, isSomeDataElement (heapLookup a heap1) ↔ isSomeDataElement (heapLookup a heap2) := by
  intro heap1 heap2 rel
  induction rel with
  | nil => intro a; exact Iff.rfl
  | @cons x y xs ys hxy _ ih =>
    intro a
    obtain ⟨len, data⟩ := gcHeapInlineRel_shape hxy
    by_cases zero : a = 0
    · subst a
      simpa [heapLookup] using data
    · by_cases inside : a < elLength x
      · have inside' : a < elLength y := len ▸ inside
        simp [heapLookup, zero, inside, inside', isSomeDataElement]
      · simp only [heapLookup, zero, inside, if_false, ← len]
        exact ih (a - elLength x)

/-- HOL `ThunkBlock_not_EQ`. Each conjunct has its own word and payload
carriers, as inferred by HOL; the thunk mode and address are shared. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ThunkBlock_not_EQ"
  (words_as_type_indexed_bitvec)]
theorem thunkBlock_not_eq {wa : Nat} {wb : Nat} {wc : Nat} [NeZero wa] [NeZero wb] [NeZero wc] {δ ε : Type}
    (ev : AstHOL.ThunkMode) (x : HeapAddress (WordLocW wb)) (i : Int) (w : BitVec 64) (n : Nat)
    (xs : List (HeapAddress (WordLocW wb))) (zs : List (HeapAddress (WordLocW wb)))
    (be flag : Bool) (bs : List (BitVec 8)) (ys : List (BitVec wb)) :
    (thunkBlock ev x : HeapElement (WordLocW wb) (HeapTag × List (WordLocW wc))) ≠ bignumRep i ∧
      (thunkBlock ev x : HeapElement (WordLocW wb) (HeapTag × List (WordLocW wa))) ≠ word64Rep w ∧
      (thunkBlock ev x : HeapElement (WordLocW wb) (HeapTag × List δ)) ≠ blockRep n xs ∧
      (thunkBlock ev x : HeapElement (WordLocW wb) (HeapTag × List ε)) ≠ refBlock zs ∧
      (thunkBlock ev x : HeapElement (WordLocW wb) (HeapTag × List (WordLocW wb))) ≠
        bytesRep be flag bs ys := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [bignumRep, thunkBlock] at h
  · intro h
    simp only [word64Rep] at h
    split at h <;> simp [thunkBlock] at h
  · intro h
    simp [thunkBlock, blockRep] at h
  · intro h
    simp [thunkBlock, refBlock] at h
  · intro h
    simp [thunkBlock, bytesRep] at h

/-- HOL `LIST_REL_gc_heap_inline_DataElement`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LIST_REL_gc_heap_inline_DataElement"]
theorem listRel_gcHeapInline_dataElement {α β γ : Type} (base : List (HeapElement α (HeapTag × List γ)))
    (xs : List (HeapAddress α)) (n : Nat) (d : β) :
    ∀ (heap1 heap2 : List (HeapElement α β)),
      List.Forall₂ (GcHeapInlineRel (DestEvaluatedThunkRel (α := α) (β := γ)) base) heap1 heap2 →
      ∀ ptr : Nat, heapLookup ptr heap1 = some (.dataElement xs n d) →
        ∃ ys, heapLookup ptr heap2 = some (.dataElement ys n d) ∧
          List.Forall₂ (GcInlineRel (DestEvaluatedThunkRel (α := α) (β := γ)) base) xs ys := by
  intro heap1 heap2 rel
  induction rel with
  | nil => intro ptr h; simp [heapLookup] at h
  | @cons x y hs ks hxy _ ih =>
    intro ptr found
    have len := (gcHeapInlineRel_shape hxy).1
    by_cases zero : ptr = 0
    · subst ptr
      simp only [heapLookup, if_true, Option.some.injEq] at found ⊢
      subst found
      cases hxy with
      | unchanged =>
        refine ⟨xs, rfl, ?_⟩
        clear ih len
        induction xs with
        | nil => exact .nil
        | cons z zs ihz => exact .cons (.unchanged z) ihz
      | inline _ _ _ ys rel => exact ⟨ys, rfl, rel⟩
    · by_cases inside : ptr < elLength x
      · simp [heapLookup, zero, inside] at found
      · simp only [heapLookup, zero, inside, if_false, ← len] at found ⊢
        exact ih _ found


/-- The generated `gc_inline_rel_cases` characterisation. -/
theorem gcInlineRel_cases {α β γ : Type} (inline : HeapElement α β → HeapAddress γ → Prop)
    (h1 : List (HeapElement α β)) (a0 a1 : HeapAddress γ) :
    GcInlineRel inline h1 a0 a1 ↔
      a1 = a0 ∨ ∃ block p u, a0 = .pointer p u ∧ heapLookup p h1 = some block ∧ inline block a1 := by
  constructor
  · intro rel
    cases rel with
    | unchanged => exact Or.inl rfl
    | inline block p u x h => exact Or.inr ⟨block, p, u, rfl, h⟩
  · rintro (h | ⟨block, p, u, rfl, h⟩)
    · subst h
      exact .unchanged _
    · exact .inline block p u a1 h

/-- An inlined root names a pointer to an evaluated thunk block; any other
heap element leaves the root unchanged. -/
theorem gcInlineRel_eq_of_not_thunk {α γ : Type} {heap : List (HeapElement α (HeapTag × List γ))}
    {a0 a1 : HeapAddress α}
    (rel : GcInlineRel (DestEvaluatedThunkRel (α := α) (β := γ)) heap a0 a1)
    (notThunk : ∀ p u e y, a0 = .pointer p u → heapLookup p heap = some e → e ≠ thunkBlock .evaluated y) :
    a1 = a0 := by
  rcases (gcInlineRel_cases _ _ _ _).mp rel with eq | ⟨block, p, u, rfl, found, dest⟩
  · exact eq
  · exact False.elim (notThunk p u block a1 rfl found ((destEvaluatedThunkRel_cases block a1).mp dest))

/-- Every list position related by `gc_inline_rel` to an empty list is empty. -/
theorem forall2_nil_left {α β : Type} {R : α → β → Prop} {ys : List β}
    (h : List.Forall₂ R [] ys) : ys = [] := by
  cases h
  rfl

/-- A data element without addresses is unchanged by heap inlining. -/
theorem gcHeapInline_lookup_noAddresses {α β γ : Type} (base : List (HeapElement α (HeapTag × List γ)))
    (heap1 heap2 : List (HeapElement α β))
    (rel : List.Forall₂ (GcHeapInlineRel (DestEvaluatedThunkRel (α := α) (β := γ)) base) heap1 heap2)
    (ptr n : Nat) (d : β) (found : heapLookup ptr heap1 = some (.dataElement [] n d)) :
    heapLookup ptr heap2 = some (.dataElement [] n d) := by
  obtain ⟨ys, found2, rels⟩ := listRel_gcHeapInline_dataElement base [] n d heap1 heap2 rel ptr found
  rw [forall2_nil_left rels] at found2
  exact found2

/-- Pairwise relations compose through a shared middle list. -/
theorem forall2_compose_mem {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    {as : List α} {bs : List β} {cs : List γ} (first : List.Forall₂ R as bs) (second : List.Forall₂ S bs cs)
    (step : ∀ a, a ∈ as → ∀ b c, R a b → S b c → T a c) : List.Forall₂ T as cs := by
  induction first generalizing cs with
  | nil => cases second; exact .nil
  | @cons a b as bs hab _ ih =>
    cases second with
    | cons hbc rest =>
      exact .cons (step a (by simp) b _ hab hbc)
        (ih rest (fun a' member b' c' r s => step a' (by simp [member]) b' c' r s))

/-- The references of a stored thunk value are reachable from the thunk's
reference. -/
theorem reachableRefs_thunk (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (n : Nat) (mode : AstHOL.ThunkMode)
    (value : Value) (bit : Bool) (found : sptLookup n refs = some (.thunk mode value)) (r : Nat)
    (reach : reachableRefs [value] refs r) : reachableRefs [.refPtr bit n] refs r := by
  obtain ⟨root, start, rootMember, startMember, path⟩ := reach
  simp only [List.mem_singleton] at rootMember
  subst root
  refine ⟨.refPtr bit n, n, by simp, by simp [getRefs], Relation.ReflTransGen.head ?_ path⟩
  simp only [refEdge, found]
  simpa [getRefs] using startMember

/-- The references of a block element are reachable from the block. -/
theorem reachableRefs_block (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (stamp tag : Nat) (values : List Value)
    (child : Value) (member : child ∈ values) (r : Nat)
    (reach : reachableRefs [child] refs r) : reachableRefs [.block stamp tag values] refs r := by
  obtain ⟨root, start, rootMember, startMember, path⟩ := reach
  simp only [List.mem_singleton] at rootMember
  subst root
  exact ⟨.block stamp tag values, start, by simp, by simp only [getRefs, List.mem_flatMap]; exact ⟨child, member, startMember⟩, path⟩

/-- A reference is reachable from a pointer to it. -/
theorem reachableRefs_self (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (bit : Bool) (n : Nat) :
    reachableRefs [.refPtr bit n] refs n :=
  ⟨.refPtr bit n, n, by simp, by simp [getRefs], .refl⟩

/-- A valid non-thunk reference cell is not an evaluated thunk block. -/
theorem bcRefInv_cell_notThunk {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (be : Bool) (valid : bcRefInv conf n refs (f, tf, heap, be))
    (noThunk : ∀ mode value, sptLookup n refs ≠ some (.thunk mode value)) :
    ∀ e y, heapLookup (holFapply f n) heap = some e → e ≠ thunkBlock .evaluated y := by
  intro e y found
  cases first : f.lookup n with
  | none => simp [bcRefInv, first] at valid
  | some ptr =>
    rw [holFapply_of_lookup first] at found
    cases cell : sptLookup n refs with
    | none => simp [bcRefInv, first, cell] at valid
    | some ref =>
      cases ref with
      | valueArray values =>
        obtain ⟨addresses, stored, _⟩ := by simpa [bcRefInv, first, cell] using valid
        rw [stored] at found
        cases found
        simp [refBlock, thunkBlock]
      | byteArray flag bytes =>
        have stored := by simpa [bcRefInv, first, cell] using valid
        rw [stored] at found
        cases found
        simp [bytesRep, thunkBlock]
      | thunk mode value => exact False.elim (noThunk mode value cell)
      | mutBlock tag fin left value right =>
        obtain ⟨_, _, addresses, stored, _⟩ := by simpa [bcRefInv, first, cell] using valid
        rw [stored] at found
        cases found
        simp [blockRep, thunkBlock]

/-- Bignum representations have no heap addresses. -/
theorem bignumRep_noAddresses {width : Nat} [NeZero width] {α : Type} (i : Int) :
    ∃ n d, (bignumRep i : HeapElement α (HeapTag × List (WordLocW width))) = .dataElement [] n d :=
  ⟨_, _, rfl⟩

/-- Word64 representations have no heap addresses. -/
theorem word64Rep_noAddresses {width : Nat} [NeZero width] {α : Type} (w : BitVec 64) :
    ∃ n d, (word64Rep w : HeapElement α (HeapTag × List (WordLocW width))) = .dataElement [] n d := by
  unfold word64Rep
  split <;> exact ⟨_, _, rfl⟩

/-- HOL `gc_heap_inline_rel_v_inv_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_heap_inline_rel_v_inv_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem gcHeapInlineRel_valueInv_lemma {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) :
    ∀ (ck : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x1 x2 : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat) (heap1 heap2 : ValueHeap width),
      valueInv conf v refs (x1, f, tf, heap1) →
        List.Forall₂ (GcHeapInlineRel (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) heap1)
            heap1 heap2 ∧
          (∀ n, f.lookup n ≠ none ∧ reachableRefs [v] refs n → bcRefInv conf n refs (f, tf, heap1, be)) ∧
          GcInlineRel (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) heap1 x1 x2 →
        ClockValueInv ck conf v refs (x2, f, tf, heap2) := by
  intro ck
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
  intro v refs x1 x2 f tf heap1 heap2 valid ⟨heapRel, refOk, rootRel⟩
  have dataRoot : ∀ w, x1 = .data w → x2 = x1 := by
    intro w eq
    apply gcInlineRel_eq_of_not_thunk rootRel
    intro p u _ _ h
    rw [eq] at h
    cases h
  cases v with
  | number i =>
    have src := (valueInv_number conf i refs x1 f tf heap1).mp valid
    by_cases small : smallInt width i
    · simp only [small, if_true] at src
      rw [dataRoot _ src, src]
      exact .numberSmall ck conf i refs f tf heap2 small
    · simp only [small, if_false] at src
      obtain ⟨ptr, rfl, found⟩ := src
      obtain ⟨len, d, rep⟩ := bignumRep_noAddresses (α := WordLocW width) (width := width) i
      rw [rep] at found
      have same : x2 = .pointer ptr (.word 0) := by
        apply gcInlineRel_eq_of_not_thunk rootRel
        intro p u e y eq h
        cases eq
        rw [found] at h
        cases h
        simp [thunkBlock]
      subst same
      have found2 := gcHeapInline_lookup_noAddresses heap1 heap1 heap2 heapRel ptr len d found
      rw [← rep] at found2
      exact .numberBig ck conf i ptr refs f tf heap2 small found2
  | word64 w =>
    obtain ⟨ptr, rfl, found⟩ := (valueInv_word64 conf w refs x1 f tf heap1).mp valid
    obtain ⟨len, d, rep⟩ := word64Rep_noAddresses (α := WordLocW width) (width := width) w
    rw [rep] at found
    have same : x2 = .pointer ptr (.word 0) := by
      apply gcInlineRel_eq_of_not_thunk rootRel
      intro p u e y eq h
      cases eq
      rw [found] at h
      cases h
      simp [thunkBlock]
    subst same
    have found2 := gcHeapInline_lookup_noAddresses heap1 heap1 heap2 heapRel ptr len d found
    rw [← rep] at found2
    exact .word64 ck conf w ptr refs f tf heap2 found2
  | codePtr n =>
    have src := (valueInv_codePtr conf n refs x1 f tf heap1).mp valid
    rw [dataRoot _ src, src]
    exact .codePtr ck conf n refs f tf heap2
  | refPtr bit n =>
    have childRefs : ∀ mode value, sptLookup n refs = some (.thunk mode value) →
        ∀ r, f.lookup r ≠ none ∧ reachableRefs [value] refs r → bcRefInv conf r refs (f, tf, heap1, be) := by
      intro mode value found r ⟨domain, reach⟩
      exact refOk r ⟨domain, reachableRefs_thunk refs n mode value bit found r reach⟩
    rcases (valueInv_refPtr conf bit n refs x1 f tf heap1).mp valid with
      ⟨domain, noThunk, noMut, rfl⟩ |
      ⟨mode, value, addr, found, safe, domain, cell, childValid, rfl, rfl⟩ |
      ⟨value, found, notThunk, rfl, childValid⟩
    · have defined : f.lookup n ≠ none := by
        obtain ⟨ptr, h⟩ := domain
        simp [h]
      have refValid := refOk n ⟨defined, reachableRefs_self refs bit n⟩
      have same := gcInlineRel_eq_of_not_thunk rootRel (by
        intro p u e y eq h
        cases eq
        exact bcRefInv_cell_notThunk conf n refs f tf heap1 be refValid noThunk e y h)
      subst same
      exact .refPtr bit ck conf n refs f tf heap2 domain noThunk noMut
    · rcases (gcInlineRel_cases _ _ _ _).mp rootRel with same | ⟨block, p, u, eq, stored, dest⟩
      · subst same
        obtain ⟨ys, cell2, rels⟩ := listRel_gcHeapInline_dataElement heap1 [addr] 1 (.thunkTag mode, [])
          heap1 heap2 heapRel (holFapply f n) (by rw [cell]; rfl)
        cases rels with
        | cons rel tail =>
          cases tail
          refine .refPtrThunk ck conf mode n value _ refs f tf heap2 found safe domain cell2 ?_
          intro positive
          exact ih (ck - 1) (by omega) value refs addr _ f tf heap1 heap2 childValid
            ⟨heapRel, childRefs mode value found, rel⟩
      · cases eq
        rw [cell] at stored
        cases stored
        obtain ⟨hm, ha⟩ := (thunkBlock_inj mode addr .evaluated x2).mp
          ((destEvaluatedThunkRel_cases _ _).mp dest)
        subst hm
        subst ha
        refine .refPtrThunkInlined ck conf n value addr refs f tf heap2 found (safe rfl) ?_
        intro positive
        exact ih (ck - 1) (by omega) value refs addr addr f tf heap1 heap2 childValid
          ⟨heapRel, childRefs .evaluated value found, .unchanged addr⟩
    · refine .refPtrThunkInlined ck conf n value x2 refs f tf heap2 found notThunk ?_
      intro positive
      exact ih (ck - 1) (by omega) value refs x1 x2 f tf heap1 heap2 childValid
        ⟨heapRel, childRefs .evaluated value found, rootRel⟩
  | block stamp tag values =>
    by_cases empty : values = []
    · subst values
      obtain ⟨src, bound, zero⟩ := (valueInv_emptyBlock conf stamp tag refs x1 f tf heap1).mp valid
      rw [dataRoot _ src, src]
      exact .blockNil ck conf stamp tag [] refs f tf heap2 rfl bound zero
    · obtain ⟨ptr, xs, pairs, stampFound, rfl, cell⟩ :=
        (valueInv_nonemptyBlock conf stamp tag values refs x1 f tf heap1 empty).mp valid
      have same := gcInlineRel_eq_of_not_thunk rootRel (by
        intro p u e y eq h
        cases eq
        rw [cell] at h
        cases h
        simp [blockRep, thunkBlock])
      subst same
      obtain ⟨ys, cell2, rels⟩ := listRel_gcHeapInline_dataElement heap1 xs xs.length (.blockTag tag, [])
        heap1 heap2 heapRel ptr (by rw [cell]; rfl)
      have len : xs.length = ys.length := rels.length_eq
      have result : ClockValueInv ck conf (.block stamp tag values) refs
          (.pointer ptr (.word (ptrBits conf tag ys.length)), f, tf, heap2) := by
        refine .blockCons ck conf stamp tag ptr values ys refs f tf heap2 empty ?_ stampFound ?_
        · intro positive
          apply (clockValueListInv_iff (ck - 1) conf refs f tf heap2 values ys).mpr
          apply forall2_compose_mem pairs rels
          intro child member addr addr2 childValid rel
          exact ih (ck - 1) (by omega) child refs addr addr2 f tf heap1 heap2 childValid
            ⟨heapRel, fun r ⟨domain, reach⟩ =>
              refOk r ⟨domain, reachableRefs_block refs stamp tag values child member r reach⟩, rel⟩
        · rw [blockRep, ← len]
          exact cell2
      rw [len]
      exact result

/-- HOL `gc_heap_inline_rel_v_inv`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gc_heap_inline_rel_v_inv"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem gcHeapInlineRel_valueInv {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool)
    (heap1 heap2 : ValueHeap width) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x1 x2 : HeapAddress (WordLocW width)) :
    List.Forall₂ (GcHeapInlineRel (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) heap1)
        heap1 heap2 ∧
      (∀ n, f.lookup n ≠ none ∧ reachableRefs [v] refs n → bcRefInv conf n refs (f, tf, heap1, be)) ∧
      valueInv conf v refs (x1, f, tf, heap1) ∧
      GcInlineRel (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) heap1 x1 x2 →
    valueInv conf v refs (x2, f, tf, heap2) := by
  rintro ⟨heapRel, refOk, valid, rootRel⟩ ck
  exact gcHeapInlineRel_valueInv_lemma conf be ck v refs x1 x2 f tf heap1 heap2 valid ⟨heapRel, refOk, rootRel⟩

/-- Domain membership in the canonical carrier. -/
theorem mapDomain_iff_lookup_ne_none (map : HolFiniteMapExact Nat Nat) (key : Nat) :
    mapDomain map key ↔ map.lookup key ≠ none := by
  constructor
  · rintro ⟨value, h⟩
    simp [h]
  · intro h
    cases found : map.lookup key with
    | none => exact False.elim (h found)
    | some value => exact ⟨value, found⟩

/-- References reachable from a value stored in a reachable cell are
reachable from the stack. -/
theorem reachableRefs_through_cell (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (stack : List Flapjack.Compiler.Backend.DataSem.Value) (n : Nat)
    (value : Value) (reach : reachableRefs stack refs n)
    (edge : ∀ s, s ∈ getRefs value → refEdge refs n s) (m : Nat)
    (reachValue : reachableRefs [value] refs m) : reachableRefs stack refs m := by
  obtain ⟨root, start, rootMember, startMember, path⟩ := reach
  obtain ⟨root', start', rootMember', startMember', path'⟩ := reachValue
  simp only [List.mem_singleton] at rootMember'
  subst root'
  exact ⟨root, start, rootMember, startMember,
    path.trans (Relation.ReflTransGen.head (edge start' startMember') path')⟩

/-- Evaluated-thunk inlining preserves one reachable reference cell. -/
theorem bcRefInv_gcInline {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap1 heap2 : ValueHeap width) (be : Bool)
    (heapRels : List.Forall₂
      (GcHeapInlineRel (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) heap1) heap1 heap2)
    (refInv : ∀ m, reachableRefs stack refs m ∧ mapDomain f m → bcRefInv conf m refs (f, tf, heap1, be))
    (reach : reachableRefs stack refs n) (old : bcRefInv conf n refs (f, tf, heap1, be)) :
    bcRefInv conf n refs (f, tf, heap2, be) := by
  have refOk : ∀ value, (∀ s, s ∈ getRefs value → refEdge refs n s) →
      ∀ m, f.lookup m ≠ none ∧ reachableRefs [value] refs m → bcRefInv conf m refs (f, tf, heap1, be) := by
    intro value edge m ⟨domain, reachValue⟩
    exact refInv m ⟨reachableRefs_through_cell refs stack n value reach edge m reachValue,
      (mapDomain_iff_lookup_ne_none f m).mpr domain⟩
  cases first : f.lookup n with
  | none => simp [bcRefInv, first] at old
  | some ptr =>
    cases cell : sptLookup n refs with
    | none => simp [bcRefInv, first, cell] at old
    | some ref =>
      cases ref with
      | valueArray values =>
        obtain ⟨addresses, stored, pairs⟩ := by simpa [bcRefInv, first, cell] using old
        obtain ⟨ys, stored2, rels⟩ := listRel_gcHeapInline_dataElement heap1 addresses addresses.length
          (.refTag, []) heap1 heap2 heapRels ptr (by rw [stored]; rfl)
        have len : addresses.length = ys.length := rels.length_eq
        simp only [bcRefInv, first, cell]
        refine ⟨ys, by rw [refBlock, ← len]; exact stored2, ?_⟩
        have moved := forall2_compose_mem (every2_swap _ _ _ pairs) rels (T := fun value y =>
            valueInv conf value refs (y, f, tf, heap2)) (by
          intro value member a y valid rel
          refine gcHeapInlineRel_valueInv conf be heap1 heap2 f tf value refs a y
            ⟨heapRels, refOk value ?_, valid, rel⟩
          intro s sMember
          simp only [refEdge, cell, getRefs, List.mem_flatMap]
          exact ⟨value, member, sMember⟩)
        exact every2_swap _ _ _ moved
      | byteArray flag bytes =>
        have stored := by simpa [bcRefInv, first, cell] using old
        simp only [bcRefInv, first, cell]
        have := gcHeapInline_lookup_noAddresses heap1 heap1 heap2 heapRels ptr _ _
          (by rw [stored]; rfl)
        exact this
      | thunk mode value =>
        obtain ⟨address, stored, safe, valid⟩ := by simpa [bcRefInv, first, cell] using old
        obtain ⟨ys, stored2, rels⟩ := listRel_gcHeapInline_dataElement heap1 [address] 1
          (.thunkTag mode, []) heap1 heap2 heapRels ptr (by rw [stored]; rfl)
        cases rels with
        | cons rel tail =>
          cases tail
          simp only [bcRefInv, first, cell]
          refine ⟨_, stored2, safe, ?_⟩
          refine gcHeapInlineRel_valueInv conf be heap1 heap2 f tf value refs address _
            ⟨heapRels, refOk value ?_, valid, rel⟩
          intro s sMember
          simp only [refEdge, cell, getRefs, List.mem_flatMap]
          exact ⟨value, by simp, sMember⟩
      | mutBlock tag fin left value right =>
        simp only [bcRefInv, first, cell] at old
        obtain ⟨kind, fresh, addresses, stored, pairs⟩ := old
        obtain ⟨ys, stored2, rels⟩ := listRel_gcHeapInline_dataElement heap1 addresses addresses.length
          (.blockTag tag, []) heap1 heap2 heapRels ptr (by rw [stored]; rfl)
        have len : addresses.length = ys.length := rels.length_eq
        simp only [bcRefInv, first, cell]
        refine ⟨kind, fresh, ys, by rw [blockRep, ← len]; exact stored2, ?_⟩
        have moved := forall2_compose_mem (every2_swap _ _ _ pairs) rels (T := fun item y =>
            valueInv conf item refs (y, f, tf, heap2)) (by
          intro item member a y valid rel
          refine gcHeapInlineRel_valueInv conf be heap1 heap2 f tf item refs a y
            ⟨heapRels, refOk item ?_, valid, rel⟩
          intro s sMember
          simp only [refEdge, cell, getRefs, List.mem_flatMap]
          exact ⟨item, member, sMember⟩)
        exact every2_swap _ _ _ moved

/-- HOL `bc_stack_ref_inv_gc_inline`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_gc_inline"
  (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_gcInline {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots1 roots2 : List (HeapAddress (WordLocW width))) (heap1 heap2 : ValueHeap width) (be : Bool) :
    gcInline (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) (roots1, heap1) (roots2, heap2) ∧
      bcStackRefInv conf ts stack refs (roots1, heap1, be) →
    bcStackRefInv conf ts stack refs (roots2, heap2, be) := by
  rintro ⟨⟨rootRels, heapRels⟩, valid⟩
  obtain ⟨f, tf, fInj, fRefs, tfInj, tfTimes, tfBound, endian, unique, values, refInv⟩ := valid
  have lookupIff := gcHeapInlineRel_heapLookup heap1 heap1 heap2 heapRels
  have inj : ∀ m, mapInjInto m (fun ptr => isSomeDataElement (heapLookup ptr heap1)) →
      mapInjInto m (fun ptr => isSomeDataElement (heapLookup ptr heap2)) := by
    rintro m ⟨into, injective⟩
    exact ⟨fun k d => (lookupIff _).mp (into k d), injective⟩
  refine ⟨f, tf, inj f fInj, fRefs, inj tf tfInj, tfTimes, tfBound, endian, unique, ?_, ?_⟩
  · apply forall2_compose_mem values rootRels
    intro value member a1 a2 hv hr
    refine gcHeapInlineRel_valueInv conf be heap1 heap2 f tf value refs a1 a2 ⟨heapRels, ?_, hv, hr⟩
    rintro n ⟨domain, ⟨root, start, rootMember, startMember, path⟩⟩
    simp only [List.mem_singleton] at rootMember
    subst root
    exact refInv n ⟨⟨value, start, member, startMember, path⟩, (mapDomain_iff_lookup_ne_none f n).mpr domain⟩
  · rintro n ⟨reach, domain⟩
    exact bcRefInv_gcInline conf n stack refs f tf heap1 heap2 be heapRels refInv reach (refInv n ⟨reach, domain⟩)

/-- HOL `bc_stack_ref_inv_gc_related_roots_heap`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_gc_related_roots_heap"
  (fmap_as_finite_support_relation := [g]) (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_gcRelatedRootsHeap {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (g : HolFiniteMapExact Nat Nat)
    (roots1 roots2 : List (HeapAddress (WordLocW width))) (heap1 heap2 : ValueHeap width) (be : Bool) :
    gcRelatedRootsHeap g (roots1, heap1) (roots2, heap2) ∧
      bcStackRefInv conf ts stack refs (roots1, heap1, be) →
    bcStackRefInv conf ts stack refs (roots2, heap2, be) := by
  rintro ⟨⟨related, rfl, rootDomain⟩, valid⟩
  exact bcStackRefInv_gcRelated conf ts stack refs roots1 heap1 heap2 be g related rootDomain valid

/-- HOL `bc_stack_ref_inv_related`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "bc_stack_ref_inv_related"
  (fmap_as_finite_support_relation := [g]) (words_as_type_indexed_bitvec)]
theorem bcStackRefInv_related {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ts : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (g : HolFiniteMapExact Nat Nat)
    (roots1 roots2 : List (HeapAddress (WordLocW width))) (heap1 heap2 : ValueHeap width) (be : Bool) :
    gcInlineRelated (DestEvaluatedThunkRel (α := WordLocW width) (β := WordLocW width)) g
        (roots1, heap1) (roots2, heap2) ∧
      bcStackRefInv conf ts stack refs (roots1, heap1, be) →
    bcStackRefInv conf ts stack refs (roots2, heap2, be) := by
  rintro ⟨⟨ri, hi, inlined, related⟩, valid⟩
  exact bcStackRefInv_gcRelatedRootsHeap conf ts stack refs g ri roots2 hi heap2 be
    ⟨related, bcStackRefInv_gcInline conf ts stack refs roots1 ri heap1 hi be ⟨inlined, valid⟩⟩

/-- HOL `data_up_to_APPEND`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "data_up_to_APPEND"]
theorem dataUpTo_append {α β : Type} (xs ys : List (HeapElement α β)) :
    dataUpTo (heapLength xs) (xs ++ ys) ↔ ∀ x ∈ xs, isDataElement x := by
  constructor
  · rintro ⟨first, second, split, data⟩
    rw [DataToWord.Proofs.Gc.heapSplit_append] at split
    cases split
    exact data
  · intro data
    exact ⟨xs, ys, DataToWord.Proofs.Gc.heapSplit_append xs ys, data⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
