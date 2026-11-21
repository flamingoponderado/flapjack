module

public import Flapjack.Misc.ListEl
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Opening list, option and set lemmas of `data_to_word_gcProofScript.sml`
(lines 38-253). HOL `LAST`, `EL` are `holLast`, `holEl` (with their reviewed
`Nonempty` inhabitant instances), `FRONT` is `List.dropLast`, `ALOOKUP` is
`holALookup`, `LIST_REL`/`EVERY2` is `List.Forall₂`, `IS_SOME` is
`Option.isSome`, `MAP FST` is `List.map Prod.fst`, and HOL sets `α -> bool`
are `Set α`. HOL `ZIP` of two equal-length lists is `List.zip`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

open Flapjack

/-- Exact HOL `LESS_EQ_IMP_APPEND_ALT` (`data_to_word_gcProofScript.sml:38-47`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LESS_EQ_IMP_APPEND_ALT"]
theorem LESS_EQ_IMP_APPEND_ALT {α : Type} :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length →
      ∃ ys zs : List α, xs = ys ++ zs ∧ zs.length = n := by
  intro n xs h
  refine ⟨xs.take (xs.length - n), xs.drop (xs.length - n), (List.take_append_drop _ _).symm, ?_⟩
  simp only [List.length_drop]
  omega

/-- Exact HOL `ALOOKUP_SKIP_LEMMA` (`data_to_word_gcProofScript.sml:149-154`);
the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ALOOKUP_SKIP_LEMMA"]
theorem ALOOKUP_SKIP_LEMMA {α β : Type} {n : α} {xs : List (α × β)} {d e : β}
    {ys : List (α × β)} :
    ¬ n ∈ xs.map Prod.fst ∧ d = e → holALookup (xs ++ [(n, d)] ++ ys) n = some e := by
  rintro ⟨hn, rfl⟩
  classical
  induction xs with
  | nil => simp [holALookup]
  | cons p xs ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [List.cons_append, holALookup, if_neg hn.1]
    exact ih hn.2

/-- Exact HOL `LAST_EQ` (`data_to_word_gcProofScript.sml:156-161`); the HOL
free variables `x` and `xs` are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LAST_EQ"
  (total_function_inhabitants := [α])]
theorem LAST_EQ {α : Type} [Nonempty α] {x : α} {xs : List α} :
    holLast (x :: xs) = (if xs = [] then x else holLast xs) ∧
      (x :: xs).dropLast = if xs = [] then [] else x :: xs.dropLast := by
  refine ⟨holLast_cons x xs, ?_⟩
  cases xs <;> simp

/-- Exact HOL `NOT_NIL_IMP_LAST` (`data_to_word_gcProofScript.sml:195-199`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "NOT_NIL_IMP_LAST"
  (total_function_inhabitants := [α])]
theorem NOT_NIL_IMP_LAST {α : Type} [Nonempty α] :
    ∀ (xs : List α) (x : α), xs ≠ [] → holLast (x :: xs) = holLast xs := by
  intro xs x h
  rw [holLast_cons, if_neg h]

/-- Exact HOL `IS_SOME_IF` (`data_to_word_gcProofScript.sml:201-205`); the HOL
condition `b : bool` is a Lean `Bool`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "IS_SOME_IF"]
theorem IS_SOME_IF {α : Type} {b : Bool} {x y : Option α} :
    (if b then x else y).isSome = if b then x.isSome else y.isSome := by
  cases b <;> rfl

/-- Exact HOL `IS_SOME_ALOOKUP_EQ` (`data_to_word_gcProofScript.sml:207-212`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "IS_SOME_ALOOKUP_EQ"]
theorem IS_SOME_ALOOKUP_EQ {α β : Type} :
    ∀ (l : List (α × β)) (x : α), (holALookup l x).isSome = true ↔ x ∈ l.map Prod.fst := by
  intro l x
  classical
  induction l with
  | nil => simp [holALookup]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hx : x = k
    · subst hx; simp [holALookup]
    · simp [holALookup, hx, ih]

/-- Exact HOL `MEM_IMP_IS_SOME_ALOOKUP` (`data_to_word_gcProofScript.sml:214-218`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "MEM_IMP_IS_SOME_ALOOKUP"]
theorem MEM_IMP_IS_SOME_ALOOKUP {α β : Type} :
    ∀ (l : List (α × β)) (x : α) (y : β), (x, y) ∈ l → (holALookup l x).isSome = true := by
  intro l x y h
  rw [IS_SOME_ALOOKUP_EQ]
  exact List.mem_map.mpr ⟨(x, y), h, rfl⟩

/-- Exact HOL `SUBSET_INSERT_EQ_SUBSET` (`data_to_word_gcProofScript.sml:220-224`);
the HOL free variables are universally quantified. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "SUBSET_INSERT_EQ_SUBSET"]
theorem SUBSET_INSERT_EQ_SUBSET {α : Type} {x : α} {s t : Set α} :
    x ∉ s → (s ⊆ insert x t ↔ s ⊆ t) := by
  intro hx
  constructor
  · intro h y hy
    rcases h hy with rfl | h'
    · exact absurd hy hx
    · exact h'
  · intro h
    exact h.trans (Set.subset_insert x t)

/-- Exact HOL `EVERY2_IMP_EL` (`data_to_word_gcProofScript.sml:226-231`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "EVERY2_IMP_EL"
  (total_function_inhabitants := [α, β])]
theorem EVERY2_IMP_EL {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (xs : List α) (ys : List β) (P : α → β → Prop) (n : Nat),
      List.Forall₂ P xs ys ∧ n < ys.length → P (holEl n xs) (holEl n ys) := by
  intro xs ys P n ⟨h, hn⟩
  have hlen := h.length_eq
  rw [holEl_eq_getElem n xs (by omega), holEl_eq_getElem n ys hn]
  exact List.forall₂_iff_get.mp h |>.2 n (by omega) hn

/-- Exact HOL `FST_PAIR_EQ` (`data_to_word_gcProofScript.sml:233-237`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "FST_PAIR_EQ"]
theorem FST_PAIR_EQ {α β : Type} :
    ∀ (x : α × β) (v : β), (x.1, v) = x ↔ v = x.2 := by
  rintro ⟨a, b⟩ v
  simp

/-- Exact HOL `EVERY2_APPEND_IMP` (`data_to_word_gcProofScript.sml:239-247`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "EVERY2_APPEND_IMP"]
theorem EVERY2_APPEND_IMP {α β : Type} :
    ∀ (xs1 xs2 : List α) (zs : List β) (P : α → β → Prop),
      List.Forall₂ P (xs1 ++ xs2) zs →
        ∃ zs1 zs2 : List β, zs = zs1 ++ zs2 ∧ List.Forall₂ P xs1 zs1 ∧
          List.Forall₂ P xs2 zs2 := by
  intro xs1 xs2 zs P h
  induction xs1 generalizing zs with
  | nil => exact ⟨[], zs, rfl, List.Forall₂.nil, h⟩
  | cons x xs1 ih =>
    cases h with
    | cons hxy hrest =>
      obtain ⟨zs1, zs2, rfl, h1, h2⟩ := ih _ hrest
      exact ⟨_ :: zs1, zs2, rfl, List.Forall₂.cons hxy h1, h2⟩

/-- Exact HOL `ZIP_ID` (`data_to_word_gcProofScript.sml:249-252`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "ZIP_ID"]
theorem ZIP_ID {α β : Type} :
    ∀ xs : List (α × β), List.zip (xs.map Prod.fst) (xs.map Prod.snd) = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons p xs ih => simp [ih]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
