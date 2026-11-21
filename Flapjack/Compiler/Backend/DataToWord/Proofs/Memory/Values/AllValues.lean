module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Stack
public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Misc.ListEl

@[expose] public section

/-!
# Nested-value membership lemmas for `v_all_vs` and `all_vs`

Counterparts of `v_all_vs_MEM`, `v_in_all_vs`, `v_all_vs_trans`,
`MEM_in_all_vs`, the `MEM_v_all_vs_*` lemmas, `all_vs_Block` and
`blocks_unique_cons_thm` in `cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`v_all_vs` is `valueListValues`, `all_vs` is the predicate `allValues`
(`x ∈ s` is `s x`, `x INSERT s` is `fun y => y = x ∨ s y`), `MEM` is list
membership, `EL` is the reviewed `holEl` and `LUPDATE v i xs` is `xs.set i v`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `v_all_vs_MEM`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_MEM"]
theorem valueListValues_mem_block :
    ∀ (l : List Flapjack.Compiler.Backend.DataSem.Value) (ts tag : Nat)
      (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      .block ts tag xs ∈ valueListValues l →
        ∃ x y, valueListValues l = x ++ .block ts tag xs :: valueListValues xs ++ y := by
  intro l
  induction l using valueListValues.induct with
  | case1 stamp tag' children rest ihChildren ihRest =>
    intro ts tag xs member
    simp only [valueListValues, List.mem_cons, List.mem_append] at member ⊢
    rcases member with (eq | nested) | tail
    · cases eq
      exact ⟨[], valueListValues rest, by simp⟩
    · obtain ⟨x, y, eq⟩ := ihChildren ts tag xs nested
      exact ⟨.block stamp tag' children :: x, y ++ valueListValues rest, by rw [eq]; simp⟩
    · obtain ⟨x, y, eq⟩ := ihRest ts tag xs tail
      exact ⟨.block stamp tag' children :: valueListValues children ++ x, y, by rw [eq]; simp⟩
  | case2 head rest notBlock ih =>
    intro ts tag xs member
    have traversal : valueListValues (head :: rest) = head :: valueListValues rest := by
      cases head with
      | block stamp tag children => exact False.elim (notBlock stamp tag children rfl)
      | number _ => simp [valueListValues]
      | word64 _ => simp [valueListValues]
      | codePtr _ => simp [valueListValues]
      | refPtr _ _ => simp [valueListValues]
    rw [traversal] at member ⊢
    rcases List.mem_cons.mp member with eq | tail
    · exact False.elim (notBlock ts tag xs eq.symm)
    · obtain ⟨x, y, eq⟩ := ih ts tag xs tail
      exact ⟨head :: x, y, by rw [eq]; simp⟩
  | case3 => intro ts tag xs member; simp [valueListValues] at member

/-- HOL `v_all_vs_trans`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_all_vs_trans"]
theorem valueListValues_trans :
    ∀ (x : List Flapjack.Compiler.Backend.DataSem.Value) (y z : Flapjack.Compiler.Backend.DataSem.Value),
      y ∈ valueListValues x ∧ z ∈ valueListValues [y] → z ∈ valueListValues x := by
  rintro x y z ⟨hy, hz⟩
  cases y with
  | block ts tag xs =>
    obtain ⟨pre, post, eq⟩ := valueListValues_mem_block x ts tag xs hy
    simp only [valueListValues, List.append_nil, List.mem_cons] at hz
    rw [eq]
    rcases hz with rfl | hz
    · simp
    · simp [hz]
  | number _ => simp [valueListValues] at hz; subst hz; exact hy
  | word64 _ => simp [valueListValues] at hz; subst hz; exact hy
  | codePtr _ => simp [valueListValues] at hz; subst hz; exact hy
  | refPtr _ _ => simp [valueListValues] at hz; subst hz; exact hy

/-- HOL `MEM_in_all_vs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_in_all_vs"]
theorem allValues_mem :
    ∀ (x y : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
      (stack : List Flapjack.Compiler.Backend.DataSem.Value),
      allValues refs stack x ∧ y ∈ valueListValues [x] → allValues refs stack y := by
  rintro x y refs stack ⟨hx, hy⟩
  rcases hx with ⟨i, vs, f, m⟩ | ⟨i, mode, c, f, m⟩ | ⟨i, t, fin, l, c, r, f, m⟩ | m
  · exact Or.inl ⟨i, vs, f, valueListValues_trans _ x y ⟨m, hy⟩⟩
  · exact Or.inr (Or.inl ⟨i, mode, c, f, valueListValues_trans _ x y ⟨m, hy⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, t, fin, l, c, r, f, valueListValues_trans _ x y ⟨m, hy⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (valueListValues_trans _ x y ⟨m, hy⟩)))

/-- HOL `v_in_all_vs`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_in_all_vs"]
theorem allValues_valueListValues :
    ∀ (x y : Flapjack.Compiler.Backend.DataSem.Value)
      (stack : List Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)),
      allValues refs stack x ∧ y ∈ valueListValues [x] → allValues refs stack y := by
  intro x y stack refs h
  exact allValues_mem x y refs stack h

/-- `v_all_vs` of a cons, split into the head's and the tail's traversals. -/
theorem valueListValues_cons (v : Flapjack.Compiler.Backend.DataSem.Value)
    (xs : List Flapjack.Compiler.Backend.DataSem.Value) :
    valueListValues (v :: xs) = valueListValues [v] ++ valueListValues xs := by
  simpa using valueListValues_append [v] xs

/-- HOL `MEM_v_all_vs_split`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_split"]
theorem mem_valueListValues_split :
    ∀ (x v : Flapjack.Compiler.Backend.DataSem.Value) (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      x ∈ valueListValues (v :: xs) → x ∈ valueListValues [v] ∨ x ∈ valueListValues xs := by
  intro x v xs h
  rw [valueListValues_cons, List.mem_append] at h
  exact h

/-- HOL `MEM_v_all_vs_split2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_split2"]
theorem mem_valueListValues_split2 (x v y : Flapjack.Compiler.Backend.DataSem.Value)
    (xs : List Flapjack.Compiler.Backend.DataSem.Value) :
    x ∈ valueListValues (v :: y :: xs) → x ∈ valueListValues (v :: xs) ∨ x ∈ valueListValues [y] := by
  intro h
  rw [valueListValues_cons, valueListValues_cons y, List.mem_append, List.mem_append] at h
  rw [valueListValues_cons, List.mem_append]
  rcases h with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h
  · exact Or.inl (Or.inr h)

/-- HOL `MEM_v_all_vs_extend_tl`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_extend_tl"]
theorem mem_valueListValues_extend_tl :
    ∀ (x v : Flapjack.Compiler.Backend.DataSem.Value) (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      x ∈ valueListValues [v] → x ∈ valueListValues (v :: xs) := by
  intro x v xs h
  rw [valueListValues_cons, List.mem_append]
  exact Or.inl h

/-- HOL `MEM_v_all_vs_extend_hd`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_extend_hd"]
theorem mem_valueListValues_extend_hd :
    ∀ (x v : Flapjack.Compiler.Backend.DataSem.Value) (xs : List Flapjack.Compiler.Backend.DataSem.Value),
      x ∈ valueListValues xs → x ∈ valueListValues (v :: xs) := by
  intro x v xs h
  rw [valueListValues_cons, List.mem_append]
  exact Or.inr h

/-- HOL `MEM_v_all_vs_extend_append`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_extend_append"]
theorem mem_valueListValues_extend_append (x : Flapjack.Compiler.Backend.DataSem.Value)
    (xs ys : List Flapjack.Compiler.Backend.DataSem.Value) :
    x ∈ valueListValues xs → x ∈ valueListValues (xs ++ ys) := by
  intro h
  rw [valueListValues_append, List.mem_append]
  exact Or.inl h

/-- HOL `MEM_v_all_vs_EL`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_EL"]
theorem mem_valueListValues_el :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (i : Nat) (x : Flapjack.Compiler.Backend.DataSem.Value),
      i < xs.length ∧ x ∈ valueListValues [holEl i xs] → x ∈ valueListValues xs := by
  intro xs
  induction xs with
  | nil => rintro i x ⟨h, _⟩; simp at h
  | cons y ys ih =>
    rintro i x ⟨lt, h⟩
    cases i with
    | zero => exact mem_valueListValues_extend_tl x y ys h
    | succ i =>
      rw [holEl_cons_succ] at h
      exact mem_valueListValues_extend_hd x y ys (ih i x ⟨by simpa using lt, h⟩)

/-- HOL `MEM_v_all_vs_LUPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "MEM_v_all_vs_LUPDATE"]
theorem mem_valueListValues_set :
    ∀ (xs : List Flapjack.Compiler.Backend.DataSem.Value) (i : Nat) (v x : Flapjack.Compiler.Backend.DataSem.Value),
      x ∈ valueListValues (xs.set i v) → x ∈ valueListValues [v] ∨ x ∈ valueListValues xs := by
  intro xs
  induction xs with
  | nil => intro i v x h; simp [valueListValues] at h
  | cons y ys ih =>
    intro i v x h
    cases i with
    | zero =>
      rcases mem_valueListValues_split x v ys (by simpa using h) with h | h
      · exact Or.inl h
      · exact Or.inr (mem_valueListValues_extend_hd x y ys h)
    | succ i =>
      rcases mem_valueListValues_split x y (ys.set i v) (by simpa using h) with h | h
      · exact Or.inr (mem_valueListValues_extend_tl x y ys h)
      · rcases ih i v x h with h | h
        · exact Or.inl h
        · exact Or.inr (mem_valueListValues_extend_hd x y ys h)

/-- HOL `all_vs_Block`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "all_vs_Block"]
theorem allValues_block (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (t tag : Nat)
    (xs ys : List Flapjack.Compiler.Backend.DataSem.Value) :
    allValues refs (.block t tag xs :: ys) = fun z => z = .block t tag xs ∨ allValues refs (xs ++ ys) z := by
  funext z
  apply propext
  have split : valueListValues (.block t tag xs :: ys) = .block t tag xs :: valueListValues (xs ++ ys) := by
    simp [valueListValues, valueListValues_append]
  simp only [allValues, split, List.mem_cons]
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro (h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- HOL `blocks_unique_cons_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_cons_thm"]
theorem blocksUnique_cons (ts tag : Nat) (xs : List Flapjack.Compiler.Backend.DataSem.Value)
    (s : Flapjack.Compiler.Backend.DataSem.Value → Prop) :
    blocksUnique ts s → blocksUnique (ts + 1) (fun z => z = .block ts tag xs ∨ s z) := by
  intro unique stamp tag1 xs1 tag2 xs2 ⟨h1, ne1, h2, ne2⟩
  have fromS : ∀ tg ys, s (.block stamp tg ys) → ys ≠ [] → stamp < ts :=
    fun tg ys hs ne => (unique stamp tg ys tg ys ⟨hs, ne, hs, ne⟩).2.2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · cases h1; cases h2; exact ⟨rfl, rfl, Nat.lt_succ_self _⟩
  · cases h1; exact absurd (fromS _ _ h2 ne2) (Nat.lt_irrefl _)
  · cases h2; exact absurd (fromS _ _ h1 ne1) (Nat.lt_irrefl _)
  · obtain ⟨a, b, c⟩ := unique stamp tag1 xs1 tag2 xs2 ⟨h1, ne1, h2, ne2⟩
    exact ⟨a, b, by omega⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
