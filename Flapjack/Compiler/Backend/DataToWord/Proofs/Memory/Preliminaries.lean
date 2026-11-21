module

public import Flapjack.Compiler.Backend.GcShared
public import Flapjack.Compiler.Backend.GcShared.AddressMap
public import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup
public import Flapjack.PanToCrepMaxList
public import Flapjack.Misc.ListEl
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# Preliminary list, word and heap lemmas of `data_to_word_memoryProof`

Counterparts of the general lemmas at the head of
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`
(`word_eq` through `EL_ADDR_MAP`). HOL `LIST_REL`/`EVERY2` is
`List.Forall₂`, `EVERY P l` is `∀ x ∈ l, P x`, `MAX_LIST` is `Flapjack.maxList`,
`ZIP` is `List.zip` (both truncate to the shorter list), `EL` is the reviewed
`holEl`, `i2w` is `BitVec.ofInt` and `w2i` is `BitVec.toInt`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend

/-- HOL `word_eq`: two words are equal exactly when every `word_bit` agrees.
HOL `word_bit n w` is `n ≤ dimindex (:α) - 1 ∧ w ' n`, rendered as
`n ≤ width - 1 ∧ w.getLsbD n = true`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq"
  (words_as_type_indexed_bitvec)]
theorem wordEq_wordBit {width : Nat} [NeZero width] :
    ∀ (w v : BitVec width), w = v ↔
      ∀ n : Nat, (n ≤ width - 1 ∧ w.getLsbD n = true) ↔ (n ≤ width - 1 ∧ v.getLsbD n = true) := by
  intro w v
  constructor
  · rintro rfl n
    exact Iff.rfl
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hle : i ≤ width - 1 := by omega
    have := h i
    cases hw : w.getLsbD i <;> cases hv : v.getLsbD i <;> simp_all

/-- HOL `ZIP_REPLICATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ZIP_REPLICATE"]
theorem zip_replicate {α β : Type} (x : α) (y : β) :
    ∀ n : Nat, List.zip (List.replicate n x) (List.replicate n y) = List.replicate n (x, y) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- HOL `MEM_EL_APPEND_MID`: an in-range element of `l ++ [c] ++ r` is in `l`,
is `c`, or is in `r`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_EL_APPEND_MID"
  (total_function_inhabitants := [α])]
theorem mem_el_append_mid {α : Type} [Nonempty α] :
    ∀ (n : Nat) (l : List α) (c : α) (r : List α),
      n < l.length + (r.length + 1) →
      holEl n (l ++ [c] ++ r) ∈ l ∨ holEl n (l ++ [c] ++ r) = c ∨ holEl n (l ++ [c] ++ r) ∈ r := by
  intro n l c r h
  have hlen : n < (l ++ [c] ++ r).length := by simp; omega
  have hmem : holEl n (l ++ [c] ++ r) ∈ l ++ [c] ++ r := by
    rw [holEl_eq_getElem n _ hlen]
    exact List.getElem_mem hlen
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with (h1 | h2) | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- HOL `MAX_LIST_sum_bound`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MAX_LIST_sum_bound"]
theorem maxList_sum_bound (ls : List Nat) : ls.sum ≤ maxList ls * ls.length := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, maxList, List.length_cons, Nat.mul_succ]
    have h1 : xs.sum ≤ max x (maxList xs) * xs.length :=
      Nat.le_trans ih (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
    have h2 : x ≤ max x (maxList xs) := Nat.le_max_left _ _
    omega

/-- HOL `MAX_LIST_bounded_elements`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MAX_LIST_bounded_elements"]
theorem maxList_bounded_elements :
    ∀ (l1 l2 : List Nat), List.Forall₂ (· ≤ ·) l1 l2 → maxList l1 ≤ maxList l2 := by
  intro l1 l2 h
  induction h with
  | nil => exact Nat.le_refl _
  | cons hab _ ih =>
    simp only [maxList]
    omega

/-- HOL `MAX_LIST_MAP`; HOL `NULL l` is `l.isEmpty`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MAX_LIST_MAP"]
theorem maxList_map :
    ∀ (f : Nat → Nat) (l : List Nat), (∀ x y : Nat, x < y → f x < f y) →
      maxList (l.map f) = if l.isEmpty then 0 else f (maxList l) := by
  intro f l mono
  have fmax : ∀ a b, f (max a b) = max (f a) (f b) := by
    intro a b
    rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · have := mono a b hab
      rw [Nat.max_eq_right (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt this)]
    · simp
    · have := mono b a hab
      rw [Nat.max_eq_left (Nat.le_of_lt hab), Nat.max_eq_left (Nat.le_of_lt this)]
  have nonempty : ∀ (xs : List Nat) (x : Nat), maxList ((x :: xs).map f) = f (maxList (x :: xs)) := by
    intro xs
    induction xs with
    | nil => intro x; simp [maxList]
    | cons y ys ih =>
      intro x
      change max (f x) (maxList ((y :: ys).map f)) = f (max x (maxList (y :: ys)))
      rw [ih y, fmax]
  cases l with
  | nil => simp [maxList]
  | cons x xs => simp only [nonempty xs x, List.isEmpty_cons, Bool.false_eq_true, if_false]

/-- HOL `w2i_i2w_IMP`. The integer-valued `INT_MIN (:α)` and `INT_MAX (:α)` are
written out as `-2 ^ (width - 1)` and `2 ^ (width - 1) - 1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "w2i_i2w_IMP"
  (words_as_type_indexed_bitvec)]
theorem toInt_ofInt_imp {width : Nat} [NeZero width] (i : Int) :
    (BitVec.ofInt width i : BitVec width).toInt = i →
      -(2 : Int) ^ (width - 1) ≤ i ∧ i ≤ (2 : Int) ^ (width - 1) - 1 := by
  intro h
  have lo := BitVec.le_toInt (BitVec.ofInt width i)
  have hi := BitVec.toInt_lt (x := BitVec.ofInt width i)
  rw [h] at lo hi
  constructor
  · exact lo
  · omega

/-- HOL `word_i2w_sub`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_i2w_sub"
  (words_as_type_indexed_bitvec)]
theorem ofInt_sub {width : Nat} [NeZero width] :
    ∀ (a b : Int),
      (BitVec.ofInt width a : BitVec width) - BitVec.ofInt width b = BitVec.ofInt width (a - b) := by
  intro a b
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_sub, BitVec.toInt_ofInt]
  rw [Int.bmod_sub_bmod, Int.sub_bmod_bmod]

/-- HOL `MOD_EQ_0_0`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MOD_EQ_0_0"]
theorem mod_eq_zero_zero : ∀ n b : Nat, 0 < b → n % b = 0 → n < b → n = 0 := by
  intro n b _ hmod hlt
  rw [Nat.mod_eq_of_lt hlt] at hmod
  exact hmod

/-- HOL `EVERY2_IMP_EVERY`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_IMP_EVERY"]
theorem every2_imp_every {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ P xs ys → ∀ p ∈ List.zip ys xs, P p.2 p.1 := by
  intro xs ys h
  induction h with
  | nil => simp
  | @cons a b as bs hab _ ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hab
    · exact ih p hp

/-- HOL `EVERY2_IMP_EVERY2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_IMP_EVERY2"]
theorem every2_imp_every2 {α β : Type} :
    ∀ (xs : List α) (ys : List β) (P1 P2 : α → β → Prop),
      (∀ x y, x ∈ xs ∧ y ∈ ys ∧ P1 x y → P2 x y) →
      List.Forall₂ P1 xs ys → List.Forall₂ P2 xs ys := by
  intro xs ys P1 P2 himp h
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b as bs hab _ ih =>
    refine List.Forall₂.cons (himp a b ⟨by simp, by simp, hab⟩) (ih ?_)
    intro x y ⟨hx, hy, hp⟩
    exact himp x y ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy, hp⟩

/-- HOL `MEM_EVERY2_IMP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_EVERY2_IMP"]
theorem mem_every2_imp {α β : Type} :
    ∀ (l : List α) (x : α) (zs : List β) (P : β → α → Prop),
      x ∈ l ∧ List.Forall₂ P zs l → ∃ z, z ∈ zs ∧ P z x := by
  intro l x zs P ⟨hx, h⟩
  induction h with
  | nil => simp at hx
  | @cons a b as bs hab _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨z, hz, hp⟩ := ih hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hp⟩

/-- HOL `EVERY2_APPEND_CONS`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_APPEND_CONS"]
theorem every2_append_cons {α β : Type} :
    ∀ (xs : List α) (y : α) (ys : List α) (zs : List β) (P : α → β → Prop),
      List.Forall₂ P (xs ++ y :: ys) zs →
      ∃ t1 t t2, zs = t1 ++ t :: t2 ∧ t1.length = xs.length ∧
        List.Forall₂ P xs t1 ∧ P y t ∧ List.Forall₂ P ys t2 := by
  intro xs
  induction xs with
  | nil =>
    intro y ys zs P h
    cases h with
    | cons hab hrest => exact ⟨[], _, _, rfl, rfl, List.Forall₂.nil, hab, hrest⟩
  | cons x xs ih =>
    intro y ys zs P h
    cases h with
    | @cons _ b _ bs hab hrest =>
      obtain ⟨t1, t, t2, rfl, hlen, h1, hy, h2⟩ := ih y ys bs P hrest
      exact ⟨b :: t1, t, t2, rfl, by simp [hlen], List.Forall₂.cons hab h1, hy, h2⟩

/-- HOL `EVERY2_SWAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_SWAP"]
theorem every2_swap {α β : Type} (P : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ P xs ys → List.Forall₂ (fun y x => P x y) ys xs := by
  intro xs ys h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

/-- HOL `EVERY2_APPEND_IMP_APPEND`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_APPEND_IMP_APPEND"]
theorem every2_append_imp_append {α β : Type} :
    ∀ (xs1 xs2 : List α) (ys : List β) (P : α → β → Prop),
      List.Forall₂ P (xs1 ++ xs2) ys →
      ∃ ys1 ys2, ys = ys1 ++ ys2 ∧ List.Forall₂ P xs1 ys1 ∧ List.Forall₂ P xs2 ys2 := by
  intro xs1
  induction xs1 with
  | nil => intro xs2 ys P h; exact ⟨[], ys, rfl, List.Forall₂.nil, h⟩
  | cons x xs ih =>
    intro xs2 ys P h
    cases h with
    | @cons _ b _ bs hab hrest =>
      obtain ⟨ys1, ys2, rfl, h1, h2⟩ := ih xs2 bs P hrest
      exact ⟨b :: ys1, ys2, rfl, List.Forall₂.cons hab h1, h2⟩

/-- HOL `EVERY2_MAP_FST_SND`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EVERY2_MAP_FST_SND"]
theorem every2_map_fst_snd {α β : Type} (P : α → β → Prop) :
    ∀ xs : List (α × β), List.Forall₂ P (xs.map Prod.fst) (xs.map Prod.snd) ↔ ∀ p ∈ xs, P p.1 p.2 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.forall₂_cons, ih]

/-- HOL `heap_lookup_APPEND1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_APPEND1"]
theorem heapLookup_append1 {α β : Type} :
    ∀ (h1 : List (HeapElement α β)) (z : Nat) (h2 : List (HeapElement α β)),
      heapLength h1 ≤ z → heapLookup z (h1 ++ h2) = heapLookup (z - heapLength h1) h2 := by
  intro h1 z h2 hle
  rw [GenGc.heapLookup_append]
  simp [Nat.not_lt.mpr hle]

/-- HOL `heap_lookup_APPEND2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_APPEND2"]
theorem heapLookup_append2 {α β : Type} :
    ∀ (h1 : List (HeapElement α β)) (z : Nat) (h2 : List (HeapElement α β)),
      z < heapLength h1 → heapLookup z (h1 ++ h2) = heapLookup z h1 := by
  intro h1 z h2 hlt
  rw [GenGc.heapLookup_append]
  simp [hlt]

/-- HOL `heap_lookup_APPEND`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_APPEND"]
theorem heapLookup_append {α β : Type} (a : Nat) (h1 h2 : List (HeapElement α β)) :
    heapLookup a (h1 ++ h2) =
      if a < heapLength h1 then heapLookup a h1 else heapLookup (a - heapLength h1) h2 :=
  GenGc.heapLookup_append a h1 h2

/-- HOL `LENGTH_ADDR_MAP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "LENGTH_ADDR_MAP"]
theorem length_addrMap {α : Type} :
    ∀ (xs : List (HeapAddress α)) (f : Nat → Nat), (addrMap f xs).length = xs.length := by
  intro xs f
  exact (addrMap_length xs f).symm

/-- HOL `EL_ADDR_MAP`. `holEl` at `HeapAddress α` takes its inhabitant from
the global `heapAddressNonempty` instance derived from `[Nonempty α]`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "EL_ADDR_MAP"
  (total_function_inhabitants := [α])]
theorem el_addrMap {α : Type} [Nonempty α] :
    ∀ (xs : List (HeapAddress α)) (n : Nat) (f : Nat → Nat),
      n < xs.length → holEl n (addrMap f xs) = addrApply f (holEl n xs) := by
  intro xs
  induction xs with
  | nil => intro n f h; simp at h
  | cons x xs ih =>
    intro n f h
    cases n with
    | zero => cases x <;> rfl
    | succ n =>
      have h' : n < xs.length := by simpa using h
      cases x <;> simpa [addrMap, holEl_cons_succ] using ih n f h'

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
