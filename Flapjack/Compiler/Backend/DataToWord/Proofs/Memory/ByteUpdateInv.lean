module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValueHeap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateHeap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePackingLength
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Thunk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.AllValues
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
public import Flapjack.HolArb

@[expose] public section

/-!
# Invariants under in-place byte-array payload updates

Counterparts of `LIST_REL_IMP_LIST_REL`, `v_inv_IMP_lemma`, `v_inv_IMP`,
`gen_state_ok_update_byte`, `heap_length_Bytes` and
`unused_space_inv_byte_update`, `heap_el_def`, `blocks_unique_deref1`,
`blocks_unique_deref2`, `small_int_IMP_MIN_MAX`, `all_ts_permute`,
`pointer_bits_def`, `is_all_ones_def`, `decode_maxout_def` and `decode_addr_def` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
HOL `Bytes` is `bytesRep`, `REPLICATE` is `List.replicate`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `LIST_REL_IMP_LIST_REL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LIST_REL_IMP_LIST_REL"]
theorem listRel_imp_listRel {α β : Type} (P Q : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), (∀ x y, x ∈ xs → P x y → Q x y) →
      List.Forall₂ P xs ys → List.Forall₂ Q xs ys := by
  intro xs ys h rel
  induction rel with
  | nil => exact .nil
  | @cons a b as bs hab _ ih =>
    exact .cons (h a b (by simp) hab) (ih (fun x y m p => h x y (List.mem_cons_of_mem _ m) p))

/-- HOL `v_inv_IMP_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_IMP_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_imp_lemma {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be fl : Bool)
    (xs ys : List (BitVec 8)) (ws : List (BitVec width)) :
    ∀ (ck : Nat) (w : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat),
      valueInv conf w refs (x, f, tf, ha ++ [bytesRep be fl xs ws] ++ hb) →
      ClockValueInv ck conf w refs (x, f, tf, ha ++ [bytesRep be fl ys ws] ++ hb) := by
  intro ck w refs x f tf valid
  exact clockValueInv_byteHeap ck conf refs f tf ha hb be fl xs ys ws w x (valid ck)

/-- HOL `v_inv_IMP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_IMP"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_imp {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be fl : Bool)
    (xs ys : List (BitVec 8)) (ws : List (BitVec width)) :
    ∀ (y : Flapjack.Compiler.Backend.DataSem.Value) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (ha : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf y refs (x, f, tf, ha ++ [bytesRep be fl xs ws] ++ hb) →
      valueInv conf y refs (x, f, tf, ha ++ [bytesRep be fl ys ws] ++ hb) := by
  intro y x f tf ha valid ck
  exact valueInv_imp_lemma conf ha hb be fl xs ys ws ck y refs x f tf valid

/-- HOL `gen_state_ok_update_byte`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "gen_state_ok_update_byte"
  (words_as_type_indexed_bitvec)]
theorem genStateOk_updateByte {width : Nat} [NeZero width] (a k : Nat)
    (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be fl : Bool)
    (xs ys : List (BitVec 8)) (ws : List (BitVec width)) (gens : GcCombined.GenState) :
    genStateOk a k (ha ++ [bytesRep be fl xs ws] ++ hb) gens →
      genStateOk a k (ha ++ [bytesRep be fl ys ws] ++ hb) gens :=
  genStateOk_shape (byteHeap_shape be fl xs ys ws ha hb) a k gens

/-- HOL `heap_length_Bytes`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_length_Bytes"
  (words_as_type_indexed_bitvec)]
theorem heapLength_bytes {width : Nat} [NeZero width] (be fl : Bool) (bs : List (BitVec 8))
    (ws : List (BitVec width)) :
    heapLength [bytesRep be fl bs ws] = ws.length + 1 := by
  simp [heapLength, bytesRep, elLength, writeBytes_wordCount]

/-- HOL `unused_space_inv_byte_update`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "unused_space_inv_byte_update"
  (words_as_type_indexed_bitvec)]
theorem unusedSpaceInv_byteUpdate_source {width : Nat} [NeZero width] (a sp sp1 : Nat)
    (ha hb : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (be fl : Bool)
    (xs ys : List (BitVec 8)) (ws : Nat) :
    unusedSpaceInv a (sp + sp1) (ha ++ [bytesRep be fl xs (List.replicate ws (0 : BitVec width))] ++ hb) →
      unusedSpaceInv a (sp + sp1) (ha ++ [bytesRep be fl ys (List.replicate ws (0 : BitVec width))] ++ hb) :=
  unusedSpaceInv_shape (byteHeap_shape be fl xs ys _ ha hb) a (sp + sp1)

/-- HOL `heap_el_def`: the `n`-th address of a pointed-to data element. The
unspecified `ARB` results and HOL `EL` use `holArb`/`holEl` at `HeapAddress α`,
inhabited through the global `heapAddressNonempty` instance from `Nonempty α`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_el_def"
  (total_function_inhabitants := [α])]
noncomputable def heapEl {α β γ : Type} [Nonempty α] :
    HeapAddress β → Nat → List (HeapElement α γ) → HeapAddress α × Bool
  | .pointer a _, n, heap =>
    match heapLookup a heap with
    | some (.dataElement xs _ _) => if n < xs.length then (holEl n xs, true) else (holArb _, false)
    | _ => (holArb _, false)
  | .data _, _, _ => (holArb _, false)

/-- HOL `blocks_unique_deref1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_deref1"]
theorem blocksUnique_deref1 (ptr ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (a' : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    sptLookup ptr refs = some (.thunk .notEvaluated a') ∧
        blocksUnique ts (allValues refs (.refPtr false ptr :: stack)) →
      blocksUnique ts (allValues refs (a' :: .refPtr false ptr :: stack)) := by
  rintro ⟨found, unique⟩ stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_addThunk refs ptr _ a' _ found _ h1, n1, allValues_addThunk refs ptr _ a' _ found _ h2, n2⟩

/-- HOL `blocks_unique_deref2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_deref2"]
theorem blocksUnique_deref2 (n ptr ts : Nat) (b : Bool) (l : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) :
    n < l.length ∧ sptLookup ptr refs = some (.valueArray l) ∧
        blocksUnique ts (allValues refs (.refPtr b ptr :: stack)) →
      blocksUnique ts (allValues refs (holEl n l :: .refPtr b ptr :: stack)) := by
  rintro ⟨lt, found, unique⟩
  have sub : ∀ v, allValues refs (holEl n l :: .refPtr b ptr :: stack) v →
      allValues refs (.refPtr b ptr :: stack) v := by
    intro v h
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases mem_valueListValues_split v _ _ h with h | h
      · exact Or.inl ⟨ptr, l, found, mem_valueListValues_el l n v ⟨lt, h⟩⟩
      · exact Or.inr (Or.inr (Or.inr h))
  intro stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨sub _ h1, n1, sub _ h2, n2⟩

/-- HOL `small_int_IMP_MIN_MAX`. HOL's integer-valued `INT_MIN (:'a)` and
`INT_MAX (:'a)` are written out as `-2 ^ (width - 1)` and
`2 ^ (width - 1) - 1`, as in the reviewed `small_int_INT_MIN_MAX`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "small_int_IMP_MIN_MAX"
  (word_dimension_as_width := width)]
theorem smallInt_imp_minMax (width : Nat) [NeZero width] (i : Int) :
    goodDimindex width ∧ smallInt width i →
    -(2 : Int) ^ (width - 1) ≤ 4 * i ∧ 4 * i ≤ (2 : Int) ^ (width - 1) - 1 := by
  rintro ⟨good, small⟩
  have bounds := smallnum_signedBounds good i small
  omega

/-- HOL `all_ts_permute`; HOL `PERM` is `List.Perm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_ts_permute"]
theorem allTimestamps_permute :
    ∀ (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (stack stack' : List Flapjack.Compiler.Backend.DataSem.Value),
      stack.Perm stack' → allTimestamps refs stack = allTimestamps refs stack' := by
  intro refs stack stack' perm
  funext t
  apply propext
  simp only [allTimestamps, perm.mem_iff]

/-- HOL `pointer_bits_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "pointer_bits_def"
  (words_as_type_indexed_bitvec)]
def pointerBits {width : Nat} [NeZero width] {β γ : Type} (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (absHeap : List (HeapElement β (HeapTag × List γ))) (n : Nat) : BitVec width :=
  match heapLookup n absHeap with
  | some (.dataElement xs _ (.blockTag tag, [])) =>
    maxoutBits xs.length conf.lenBits (conf.tagBits + 2) ||| maxoutBits tag conf.tagBits 2 ||| 1
  | _ => allOnes (conf.lenBits + conf.tagBits + 1) 0

/-- HOL `is_all_ones_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "is_all_ones_def"
  (words_as_type_indexed_bitvec)]
def isAllOnes {width : Nat} [NeZero width] (m n : Nat) (w : BitVec width) : Prop :=
  (allOnes m n &&& w) = allOnes m n

instance {width : Nat} [NeZero width] (m n : Nat) (w : BitVec width) : Decidable (isAllOnes m n w) := by
  unfold isAllOnes
  infer_instance

/-- HOL `decode_maxout_def`. HOL `(h -- l) w` is the reviewed `gcWordBits`
rendering of `word_bits` and `>>` (`word_asr`) is `BitVec.sshiftRight`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "decode_maxout_def"
  (words_as_type_indexed_bitvec)]
def decodeMaxout {width : Nat} [NeZero width] (l n : Nat) (w : BitVec width) : Option (BitVec width) :=
  if isAllOnes (n + l) n w then none else some ((StackAlloc.gcWordBits (n + l) n w).sshiftRight n)

/-- HOL `decode_addr_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "decode_addr_def"
  (words_as_type_indexed_bitvec)]
def decodeAddr {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (w : BitVec width) : Option (BitVec width) × Option (BitVec width) :=
  (decodeMaxout conf.lenBits (conf.tagBits + 2) w, decodeMaxout conf.tagBits 2 w)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
