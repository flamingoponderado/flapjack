module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Elementary `misc` facts

Lean counterparts of the short generic facts at the head of
`cakeml/misc/miscScript.sml`: eta-expanded tuple projections, the one-step
`num` bound, replication membership, take length, byte-range words, the
implication combinator, set inclusion and the arithmetic composition.
-/

namespace Flapjack

/-- Original `FST_pair`: the first projection as an eta-expanded lambda. -/
@[hol "cakeml/misc/miscScript.sml" "FST_pair"]
theorem fst_pair_eta {α β : Type} : (fun p : α × β => p.1) = Prod.fst := rfl

/-- Original `SND_pair`: the second projection as an eta-expanded lambda. -/
@[hol "cakeml/misc/miscScript.sml" "SND_pair"]
theorem snd_pair_eta {α β : Type} : (fun p : α × β => p.2) = Prod.snd := rfl

/-- Original `FST_triple`: the first projection of a nested triple. -/
@[hol "cakeml/misc/miscScript.sml" "FST_triple"]
theorem fst_triple_eta {α β γ : Type} : (fun p : α × β × γ => p.1) = Prod.fst := rfl

/-- Original `SND_triple`: uncurrying the pair part of a nested triple. -/
@[hol "cakeml/misc/miscScript.sml" "SND_triple"]
theorem snd_triple_eta {δ β γ α : Type} (f : β → γ → α) :
    (fun p : δ × β × γ => f p.2.1 p.2.2) = Function.uncurry f ∘ Prod.snd := by
  funext p
  rfl

/-- Original `LESS_1`: the only number below one is zero. -/
@[hol "cakeml/misc/miscScript.sml" "LESS_1"]
theorem less_one (x : Nat) : x < 1 ↔ x = 0 := Nat.lt_one_iff

/-- Original `MEM_REPLICATE_EQ`: membership in a replication. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_REPLICATE_EQ"]
theorem mem_replicate_eq {α : Type} (n : Nat) (x y : α) :
    x ∈ List.replicate n y ↔ x = y ∧ n ≠ 0 := by
  rw [List.mem_replicate]
  exact ⟨fun ⟨hn, hxy⟩ => ⟨hxy, hn⟩, fun ⟨hxy, hn⟩ => ⟨hn, hxy⟩⟩

/-- Original `LENGTH_TAKE_EQ_MIN`: a take is bounded by the minimum. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_TAKE_EQ_MIN"]
theorem length_take_min {α : Type} (n : Nat) (xs : List α) :
    (xs.take n).length = min n xs.length := List.length_take

/-- Original `w2n_lt_256`: byte words are below 256. -/
@[hol "cakeml/misc/miscScript.sml" "w2n_lt_256"]
theorem toNat_lt_256 (w : BitVec 8) : w.toNat < 256 := w.isLt

/-- Original `IMP_IMP`: currying a conjoined implication. -/
@[hol "cakeml/misc/miscScript.sml" "IMP_IMP"]
theorem imp_imp (P Q R : Prop) : P ∧ (Q → R) → (P → Q) → R :=
  fun h hpq => h.2 (hpq h.1)

/-- Original `SUBSET_IMP`: membership transfers along a subset. -/
@[hol "cakeml/misc/miscScript.sml" "SUBSET_IMP"]
theorem subset_imp {α : Type} {s t : Set α} {x : α} (h : s ⊆ t) (hx : x ∈ s) : x ∈ t :=
  h hx

/-- Original `DROP_NIL`: a drop is empty exactly up to the length. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_NIL"]
theorem drop_eq_nil_iff {α : Type} (n : Nat) (xs : List α) :
    xs.drop n = [] ↔ xs.length ≤ n := List.drop_eq_nil_iff

/-- Original `times_add_o`: `k * n + x` as a composition. -/
@[hol "cakeml/misc/miscScript.sml" "times_add_o"]
theorem times_add_comp (k x : Nat) :
    (fun n : Nat => k * n + x) = (fun n : Nat => n + x) ∘ (fun n : Nat => n * k) := by
  funext n
  simp only [Function.comp_apply, Nat.mul_comm]

/-- Original `FST_5tup`: the first projection of a nested five-tuple. -/
@[hol "cakeml/misc/miscScript.sml" "FST_5tup"]
theorem fst_5tup_eta {α β γ δ ε : Type} :
    (fun p : α × β × γ × δ × ε => p.1) = Prod.fst := rfl

/-- Original `SND_FST_pair`: the second component of the first pair. -/
@[hol "cakeml/misc/miscScript.sml" "SND_FST_pair"]
theorem snd_fst_pair_eta {α β γ : Type} :
    (fun p : (α × β) × γ => p.1.2) = Prod.snd ∘ Prod.fst := rfl

/-- Original `plus_compose`: adding a constant composes by addition. -/
@[hol "cakeml/misc/miscScript.sml" "plus_compose"]
theorem plus_comp (n m : Nat) :
    (fun k : Nat => k + n) ∘ (fun k : Nat => k + m) = (fun k : Nat => k + (n + m)) := by
  funext k
  simp only [Function.comp_apply]
  omega

/-- Original `option_case_NONE_F`: a case over `NONE` as an existential. -/
@[hol "cakeml/misc/miscScript.sml" "option_case_NONE_F"]
theorem option_case_none_false {α : Type} (X : Option α) (P : α → Prop) :
    (match X with | none => False | some x => P x) ↔ ∃ x, X = some x ∧ P x := by
  cases X with
  | none => simp
  | some x => simp

/-- Original `MAP_FST_I_PAIR_MAP`: mapping the second component keeps the
first projection. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_FST_I_PAIR_MAP"]
theorem map_fst_pair_map {α β γ : Type} (f : β → γ) (xs : List (α × β)) :
    (xs.map (Prod.map id f)).map Prod.fst = xs.map Prod.fst := by
  simp

/-- Original `FLAT_MAP_SING`: flattening singleton lists is mapping. -/
@[hol "cakeml/misc/miscScript.sml" "FLAT_MAP_SING"]
theorem flat_map_sing {α β : Type} (f : α → β) (ls : List α) :
    (ls.map (fun x => [f x])).flatten = ls.map f := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.singleton_append]
    rw [ih]

/-- Original `FLAT_MAP_NIL`: flattening empty lists is empty. -/
@[hol "cakeml/misc/miscScript.sml" "FLAT_MAP_NIL"]
theorem flat_map_nil {α β : Type} (ls : List α) :
    (ls.map (fun _ => ([] : List β))).flatten = [] := by
  induction ls with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_cons, List.flatten_cons, List.nil_append, ih]

/-- Original `remove_pair_lem`: applying a pair-destructuring lambda. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "remove_pair_lem"]
theorem remove_pair_lem {α β γ δ ε ζ η : Type} :
    (∀ (f : α → β → γ) (v : α × β), (fun p : α × β => f p.1 p.2) v = f v.1 v.2) ∧
      (∀ (f : δ → ε → ζ → η) (v : δ × ε × ζ),
        (fun p : δ × ε × ζ => f p.1 p.2.1 p.2.2) v = f v.1 v.2.1 v.2.2) := by
  constructor
  · intro f v
    rfl
  · intro f v
    rfl

/-- Original `UNCURRY_rator`: uncurrying absorbs a trailing argument. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "UNCURRY_rator"]
theorem uncurry_rator {α β γ δ : Type} (f : α → β → γ → δ) (x : α × β) (y : γ) :
    Function.uncurry f x y = Function.uncurry (fun a b => f a b y) x := by
  cases x with
  | mk a b =>
    rfl

/-- Original `PAIR_MAP_EQ_EQ` (`backendProofScript.sml:353`): a mapped pair
equals `y` exactly when `y` is the image of the pair's two components. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "PAIR_MAP_EQ_EQ"]
theorem pairMap_eq_eq {α β γ δ : Type} (f : γ → α) (g : δ → β) (x : γ × δ)
    (y : α × β) :
    Prod.map f g x = y ↔ ∃ x0 x1, x = (x0, x1) ∧ (f x0, g x1) = y := by
  cases x with
  | mk x0 x1 =>
    constructor
    · intro h
      exact ⟨x0, x1, rfl, h⟩
    · rintro ⟨x0', x1', hpair, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
      exact h

/-- Original `ZIP_MAP_FST_SND_EQ`: zipping the two projections rebuilds the list. -/
@[hol "cakeml/misc/miscScript.sml" "ZIP_MAP_FST_SND_EQ"]
theorem zip_map_fst_snd_eq {α β : Type} (ls : List (α × β)) :
    (ls.map Prod.fst).zip (ls.map Prod.snd) = ls := by
  induction ls with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.map_cons, List.zip_cons_cons, ih]

/-- Original `MAP_EQ_ID`: a map is the identity exactly on the list elements. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_EQ_ID"]
theorem map_eq_id {α : Type} (f : α → α) (ls : List α) :
    ls.map f = ls ↔ ∀ x ∈ ls, f x = x := by
  induction ls with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.cons.injEq, List.mem_cons]
    constructor
    · rintro ⟨hx, hrest⟩ y (rfl | hy)
      · exact hx
      · exact ih.mp hrest y hy
    · intro h
      exact ⟨h x (Or.inl rfl), ih.mpr (fun y hy => h y (Or.inr hy))⟩

/-- Original `SUM_REPLICATE`: replicating a value multiplies it by the count. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_REPLICATE"]
theorem sum_replicate (n m : Nat) : (List.replicate n m).sum = n * m := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
    omega

/-- Original `SUM_MAP_LENGTH_REPLICATE`: replicated lists sum their lengths. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_MAP_LENGTH_REPLICATE"]
theorem sum_map_length_replicate {α : Type} (n : Nat) (ls : List α) :
    ((List.replicate n ls).map List.length).sum = n * ls.length := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.map_cons, List.sum_cons, ih, Nat.succ_mul]
    omega

/-- Original `EL_CONS_IF`: indexing a cons splits off the head. -/
@[hol "cakeml/misc/miscScript.sml" "EL_CONS_IF" (total_function_inhabitants := [α])]
theorem holEl_cons {α : Type} [Nonempty α] (n : Nat) (x : α) (xs : List α) :
    holEl n (x :: xs) = if n = 0 then x else holEl (n - 1) xs := by
  cases n with
  | zero => simp [holEl, holHd]
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false, holEl, List.tail_cons]
    rw [Nat.succ_sub_one]

/-- Original `EVERY_LAST`: every element satisfies a predicate that the last
element does too. -/
@[hol "cakeml/misc/miscScript.sml" "EVERY_LAST" (total_function_inhabitants := [α])]
theorem every_holLast {α : Type} [Nonempty α] (P : α → Bool) (l : List α) :
    l ≠ [] ∧ l.all P = true → P (holLast l) = true := by
  intro h
  induction l with
  | nil => exact absurd rfl h.1
  | cons x rest ih =>
    cases rest with
    | nil => simpa [holLast] using h.2
    | cons y z =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [holLast]
      have tailAll : (y :: z).all P = true := by
        simp only [List.all_cons, Bool.and_eq_true]
        exact h.2.2
      exact ih ⟨by simp, tailAll⟩

end Flapjack
