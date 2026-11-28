module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Flapjack.FiniteMap.AlistExact.Lookup
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Forall2

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

/-- Original `revdroprev`: dropping from the reversed list and reversing back
gives the corresponding take. The source bound is retained although the proof
does not need it. -/
@[hol "cakeml/misc/miscScript.sml" "revdroprev"]
theorem revdroprev {α : Type} (l : List α) (n : Nat) (_h : n ≤ l.length) :
    (l.reverse.drop n).reverse = l.take (l.length - n) := by
  rw [List.drop_reverse, List.reverse_reverse]

/-- Original `o_PAIR_MAP`: the projections commute with a pair map. -/
@[hol "cakeml/misc/miscScript.sml" "o_PAIR_MAP"]
theorem pairMap_proj {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    (Prod.fst ∘ Prod.map f g = f ∘ Prod.fst) ∧
      (Prod.snd ∘ Prod.map f g = g ∘ Prod.snd) := by
  constructor
  · funext p
    rfl
  · funext p
    rfl

/-- Original `EVERY_FST_SND`: a predicate on pairs splits over the two
projections. -/
@[hol "cakeml/misc/miscScript.sml" "EVERY_FST_SND"]
theorem all_fst_snd {α β : Type} (P : α → Bool) (Q : β → Bool) (ls : List (α × β)) :
    (ls.all fun p => P p.1 && Q p.2) = ((ls.map Prod.fst).all P && (ls.map Prod.snd).all Q) := by
  induction ls with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    simp only [List.all_cons, List.map_cons, ih, Bool.and_assoc, Bool.and_left_comm]

/-- Original `EVERY_ZIP`: a predicate on the first components of a pair list is
the same as a predicate on the projected list. -/
@[hol "cakeml/misc/miscScript.sml" "EVERY_ZIP"]
theorem all_fst {α β : Type} (l : List (α × β)) (f : α → Bool) :
    (l.all fun p => f p.1) = ((l.map Prod.fst).all f) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.all_cons, List.map_cons, ih]

/-- Original `EXISTS_ZIP`: a predicate on the first components of a pair list is
the same as a predicate on the projected list. -/
@[hol "cakeml/misc/miscScript.sml" "EXISTS_ZIP"]
theorem any_fst {α β : Type} (l : List (α × β)) (f : α → Bool) :
    (l.any fun p => f p.1) = ((l.map Prod.fst).any f) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.any_cons, List.map_cons, ih]

/-- Original `TWOxDIV2`: doubling then halving is the identity. -/
@[hol "cakeml/misc/miscScript.sml" "TWOxDIV2"]
theorem two_mul_div_two (x : Nat) : 2 * x / 2 = x := Nat.mul_div_cancel_left x (by decide)

/-- Original `DROP_EMPTY`: an empty drop means the index reached the length. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_EMPTY"]
theorem drop_empty {α : Type} (ls : List α) (n : Nat) (h : ls.drop n = []) :
    ls.length ≤ n := by
  rwa [← List.drop_eq_nil_iff]

/-- Original `DROP_IMP_LESS_LENGTH`: a non-empty drop has a valid index. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_IMP_LESS_LENGTH"]
theorem drop_cons_imp_lt_length {α : Type} (xs : List α) (n : Nat) (y : α) (ys : List α)
    (h : xs.drop n = y :: ys) : n < xs.length := by
  have lenEq : (xs.drop n).length = xs.length - n := List.length_drop
  rw [h] at lenEq
  simp at lenEq
  omega

/-- Original `MULT_DIV_MULT_LEMMA`: cancelling a common positive factor under
division. The second positivity premise is retained from the source. -/
@[hol "cakeml/misc/miscScript.sml" "MULT_DIV_MULT_LEMMA"]
theorem mul_div_mul_lemma (m l k : Nat) (hm : 0 < m) (_hl : 0 < l) :
    (m * k) / (l * m) = k / l := by
  rw [Nat.mul_comm l m]
  exact Nat.mul_div_mul_left k l hm

/-- Original `ADD_MOD_EQ_LEMMA`: adding a value below the modulus to a multiple
of the modulus leaves that value. -/
@[hol "cakeml/misc/miscScript.sml" "ADD_MOD_EQ_LEMMA"]
theorem add_mod_eq_lemma (k n d : Nat) (hk : k % d = 0) (hn : n < d) :
    (k + n) % d = n := by
  have hdvd : d ∣ k := Nat.dvd_of_mod_eq_zero hk
  have hkmul : k / d * d = k := Nat.div_mul_cancel hdvd
  rw [← hkmul, Nat.add_comm, Nat.mul_comm (k / d) d, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hn]

/-- Original `SUM_MOD`: a sum is congruent to the sum of its residues. The
source positivity premise is retained although the proof does not need it. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_MOD"]
theorem sum_mod (ls : List Nat) (k : Nat) (_hk : k > 0) :
    ls.sum % k = (ls.map fun n => n % k).sum % k := by
  induction ls with
  | nil => simp
  | cons x rest ih =>
    simp only [List.sum_cons, List.map_cons, ih, Nat.add_mod, Nat.mod_mod]

/-- Original `DROP_EQ_CONS_IMP_DROP_SUC`: a drop that starts with a cons drops
one more element to reach its tail. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_EQ_CONS_IMP_DROP_SUC"]
theorem drop_cons_imp_drop_succ {α : Type} (xs : List α) (n : Nat) (y : α) (ys : List α)
    (h : xs.drop n = y :: ys) : xs.drop (n + 1) = ys := by
  rw [← List.tail_drop, h]
  rfl

/-- Original `LUPDATE_APPEND`: updating an appended list splits at the left
length. LUPDATE is Lean `List.set`. -/
@[hol "cakeml/misc/miscScript.sml" "LUPDATE_APPEND"]
theorem lupdate_append {α : Type} (xs : List α) (n : Nat) (ys : List α) (x : α) :
    (xs ++ ys).set n x =
      if n < xs.length then xs.set n x ++ ys else xs ++ ys.set (n - xs.length) x :=
  List.set_append

/-- Original `DROP_LUPDATE`: dropping an updated list updates the dropped list
at the shifted index. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_LUPDATE"]
theorem drop_lupdate {α : Type} (n : Nat) (x : α) (m : Nat) (l : List α) (h : n ≤ m) :
    (l.set m x).drop n = (l.drop n).set (m - n) x := by
  rw [List.drop_set]
  rw [if_neg (by omega)]

section

open Classical

/-- Original `ALOOKUP_SNOC`: appending one entry leaves earlier lookups intact
and otherwise falls back to that entry. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_SNOC"]
theorem holALookup_snoc {α β : Type} (ls : List (α × β)) (p : α × β) (k : α) :
    holALookup (ls ++ [p]) k =
      match holALookup ls k with
      | none => if k = p.1 then some p.2 else none
      | some v => some v := by
  induction ls with
  | nil => simp [holALookup]
  | cons e rest ih =>
    rcases e with ⟨key, value⟩
    simp only [List.cons_append, holALookup]
    split
    · rfl
    · exact ih

/-- Original `ALOOKUP_ZIP_FAIL`: a lookup in a zipped pair list fails exactly
when the key is absent from the left list, given equal lengths. -/
@[hol "cakeml/misc/miscScript.sml" "ALOOKUP_ZIP_FAIL"]
theorem holALookup_zip_fail {α β : Type} (A : List α) (B : List β) (x : α)
    (h : A.length = B.length) :
    holALookup (A.zip B) x = none ↔ x ∉ A := by
  induction A generalizing B with
  | nil => simp [holALookup]
  | cons a rest ih =>
    cases B with
    | nil => simp at h
    | cons b restB =>
      simp only [List.zip_cons_cons, holALookup, List.length_cons] at h ⊢
      by_cases same : x = a
      · rw [if_pos same]
        simp [same]
      · rw [if_neg same]
        rw [ih restB (by omega)]
        simp [same]

end

/-- Original `map_fst`: remapping the second components leaves the first
components unchanged. -/
@[hol "cakeml/misc/miscScript.sml" "map_fst"]
theorem map_fst_second {α β γ : Type} (l : List (α × β)) (f : β → γ) :
    (l.map fun p => (p.1, f p.2)).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.map_cons, ih]

/-- Original `map_some_eq`: mapping to `SOME` is injective. -/
@[hol "cakeml/misc/miscScript.sml" "map_some_eq"]
theorem map_some_eq {α : Type} (l1 l2 : List α) : (l1.map some = l2.map some) ↔ l1 = l2 := by
  constructor
  · intro h
    induction l1 generalizing l2 with
    | nil =>
      cases l2 with
      | nil => rfl
      | cons y ys => simp at h
    | cons x xs ih =>
      cases l2 with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, Option.some.injEq, List.cons.injEq] at h
        rw [h.1, ih ys h.2]
  · intro h
    rw [h]

/-- Original `MAP_EQ_MAP_IMP`: a map that is injective on the relevant members
reflects list equality. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_EQ_MAP_IMP"]
theorem map_eq_map_imp {α β : Type} (xs ys : List α) (f : α → β)
    (inj : ∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) (h : xs.map f = ys.map f) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy : x = y := inj x y ⟨by simp, by simp, h.1⟩
      rw [hxy, ih ys (fun a b hab => inj a b ⟨by simp [hab.1], by simp [hab.2.1], hab.2.2⟩) h.2]

/-- Original `OPTION_MAP_INJ`: an injective map is injective on options. -/
@[hol "cakeml/misc/miscScript.sml" "OPTION_MAP_INJ"]
theorem option_map_inj {α β : Type} (f : α → β) (inj : ∀ x y, f x = f y → x = y)
    (o1 o2 : Option α) (h : o1.map f = o2.map f) : o1 = o2 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some y => simp at h
  | some x =>
    cases o2 with
    | none => simp at h
    | some y =>
      simp only [Option.map_some, Option.some.injEq] at h
      rw [inj x y h]

/-- Original `the_OPTION_MAP`: mapping an option commutes with its default
lookup when the default is a fixed point. -/
@[hol "cakeml/misc/miscScript.sml" "the_OPTION_MAP"]
theorem the_option_map {α : Type} (f : α → α) (d : α) (opt : Option α) (hd : f d = d) :
    (opt.map f).getD d = f (opt.getD d) := by
  cases opt with
  | none => simp [hd]
  | some x => rfl

/-- Original `MEM_REPLICATE_IMP`: a replicated value is the repeated element. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_REPLICATE_IMP"]
theorem mem_replicate_imp {α : Type} (x : α) :
    ∀ (n : Nat) (y : α), x ∈ List.replicate n y → x = y := by
  intro n
  induction n with
  | zero =>
    intro y hx
    simp at hx
  | succ n ih =>
    intro y hx
    simp only [List.replicate_succ, List.mem_cons] at hx
    rcases hx with h | h
    · exact h
    · exact ih y h

/-- Original `MAP_K_REPLICATE`: mapping a constant is a replicate. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_K_REPLICATE"]
theorem map_const_replicate {α β : Type} (x : α) :
    ∀ (ls : List β), ls.map (fun _ => x) = List.replicate ls.length x := by
  intro ls
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [ih, List.replicate_succ]

/-- Original `SUM_MAP_K`: a constant map sums to its length times the value. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_MAP_K"]
theorem sum_map_const {α : Type} :
    ∀ (f : α → Nat) (ls : List α) (c : Nat),
      (∀ x, f x = c) → (ls.map f).sum = ls.length * c := by
  intro f ls
  induction ls with
  | nil =>
    intro c _
    simp
  | cons h t ih =>
    intro c hc
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [hc h, ih c hc, Nat.succ_mul]
    omega

/-- Original `OPTION_MAP_I`: mapping the identity changes nothing. -/
@[simp, hol "cakeml/misc/miscScript.sml" "OPTION_MAP_I"]
theorem option_map_id {α : Type} (x : Option α) : x.map id = x := by
  cases x with
  | none => rfl
  | some v => rfl

/-- Original `TL_DROP_SUC`: the tail of a proper drop is the next drop. -/
@[hol "cakeml/misc/miscScript.sml" "TL_DROP_SUC"]
theorem tail_drop_succ {α : Type} (x : Nat) :
    ∀ (ls : List α), x < ls.length → (ls.drop x).tail = ls.drop (x + 1) := by
  intro ls
  induction ls generalizing x with
  | nil =>
    intro h
    simp at h
  | cons h t ih =>
    intro hx
    cases x with
    | zero => rfl
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k (by simpa using hx)

/-- Original `ALL_DISTINCT_FLAT_EVERY`: a distinct flattening has distinct
members. -/
@[hol "cakeml/misc/miscScript.sml" "ALL_DISTINCT_FLAT_EVERY"]
theorem allDistinct_flatten_every {α : Type} :
    ∀ (ls : List (List α)), ls.flatten.Nodup → ∀ l ∈ ls, l.Nodup := by
  intro ls
  induction ls with
  | nil =>
    intro _ l hl
    simp at hl
  | cons a as ih =>
    intro h l hl
    rw [List.flatten_cons, List.nodup_append] at h
    rcases List.mem_cons.mp hl with rfl | hmem
    · exact h.1
    · exact ih h.2.1 l hmem

/-- Original `OPT_MMAP_SOME`: mapping `some` recovers the list. -/
@[simp, hol "cakeml/misc/miscScript.sml" "OPT_MMAP_SOME"]
theorem mapM_some {α : Type} (ls : List α) : ls.mapM some = some ls := by
  induction ls with
  | nil => rfl
  | cons a t ih =>
    simp [List.mapM_cons, ih]

/-- Original `insert_atI_def`: overwrite `l1` into `l2` starting at `n`. -/
@[hol "cakeml/misc/miscScript.sml" "insert_atI_def"]
def insertAtI {α : Type} (l1 : List α) (n : Nat) (l2 : List α) : List α :=
  l2.take n ++ l1 ++ l2.drop (n + l1.length)

/-- Original `LENGTH_insert_atI`: an in-bounds overwrite keeps the length. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_insert_atI"]
theorem length_insertAtI {α : Type} (p : Nat) (l1 l2 : List α)
    (h : p + l1.length ≤ l2.length) : (insertAtI l1 p l2).length = l2.length := by
  unfold insertAtI
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

/-- Original `insert_atI_NIL`: overwriting nothing changes nothing. -/
@[hol "cakeml/misc/miscScript.sml" "insert_atI_NIL"]
theorem insertAtI_nil {α : Type} (n : Nat) (l : List α) : insertAtI [] n l = l := by
  unfold insertAtI
  simp

/-- Original `insert_atI_end`: overwriting from the end appends. -/
@[hol "cakeml/misc/miscScript.sml" "insert_atI_end"]
theorem insertAtI_end {α : Type} (l1 l2 : List α) :
    insertAtI l1 l2.length l2 = l2 ++ l1 := by
  unfold insertAtI
  simp

/-- Original `OPT_MMAP_MAP_o`: mapping a function into an optional map is the
composition. -/
@[hol "cakeml/misc/miscScript.sml" "OPT_MMAP_MAP_o"]
theorem mapM_map_comp {α β γ : Type} (f : γ → Option β) (g : α → γ) (ls : List α) :
    (ls.map g).mapM f = ls.mapM (f ∘ g) := by
  induction ls with
  | nil => rfl
  | cons a t ih =>
    simp [List.mapM_cons, ih]

/-- Original `list_inter_def`: the elements of `ys` that occur in `xs`. -/
@[hol "cakeml/misc/miscScript.sml" "list_inter_def"]
def listInter {α : Type} [DecidableEq α] (xs ys : List α) : List α :=
  ys.filter (fun y => decide (y ∈ xs))

/-- Original `any_el_def`: the element at `n`, with a default past the end. -/
@[hol "cakeml/misc/miscScript.sml" "any_el_def"]
def anyEl {α : Type} (n : Nat) (xs : List α) (d : α) : α :=
  match xs with
  | [] => d
  | x :: xs => if n = 0 then x else anyEl (n - 1) xs d

/-- Original `option_fold_def`: fold an optional value with a default. -/
@[hol "cakeml/misc/miscScript.sml" "option_fold_def"]
def optionFold {α β : Type} (f : β → α → α) (x : α) : Option β → α
  | none => x
  | some y => f y x

/-- Original `steps_rel_def`: a trace is accepted when every step relates the
current state to the next one. -/
@[hol "cakeml/misc/miscScript.sml" "steps_rel_def"]
def stepsRel {α β : Type} (R : α → β → α → Bool) (x : α) : List (β × α) → Bool
  | [] => true
  | (j, y) :: tr => R x j y && stepsRel R y tr

/-- Original `DROP_IMP_EL`: a non-empty drop starts with the indexed element. -/
@[hol "cakeml/misc/miscScript.sml" "DROP_IMP_EL" (total_function_inhabitants := [α])]
theorem drop_imp_el {α : Type} [Nonempty α] (xs : List α) (n : Nat) (h : α) (t : List α)
    (hd : xs.drop n = h :: t) : holEl n xs = h := by
  have hn : n < xs.length := by
    have := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at this
    omega
  rw [holEl_eq_getElem n xs hn]
  have hcons := List.drop_eq_getElem_cons hn
  rw [hcons] at hd
  simp only [List.cons.injEq] at hd
  exact hd.1

/-- Original `HD_LUPDATE`: overwriting keeps the head unless position `0` is
overwritten. -/
@[hol "cakeml/misc/miscScript.sml" "HD_LUPDATE" (total_function_inhabitants := [α])]
theorem holHd_lupdate {α : Type} [Nonempty α] (l : List α) (p : Nat) (x : α)
    (h : 0 < l.length) : holHd (l.set p x) = if p = 0 then x else holHd l := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases p with
    | zero => simp [holHd]
    | succ k =>
      simp only [List.set_cons_succ, holHd, Nat.succ_ne_zero, if_false]

/-- Original `steps_def`: thread `f` through the inputs, keeping each step. -/
@[hol "cakeml/misc/miscScript.sml" "steps_def"]
def steps {α β : Type} (f : α → β → α) (x : α) : List β → List (β × α)
  | [] => []
  | j :: js => (j, f x j) :: steps f (f x j) js

/-- Original `LAST_MAP_SND_steps_FOLDL`: the last recorded state is the fold. -/
@[hol "cakeml/misc/miscScript.sml" "LAST_MAP_SND_steps_FOLDL"
  (total_function_inhabitants := [α])]
theorem holLast_map_snd_steps {α β : Type} [Nonempty α] :
    ∀ (f : α → β → α) (x : α) (ls : List β),
      holLast (x :: (steps f x ls).map Prod.snd) = ls.foldl f x := by
  intro f x ls
  induction ls generalizing x with
  | nil => simp [steps, holLast]
  | cons j js ih =>
    simp only [steps, List.map_cons, List.foldl_cons]
    rw [holLast_cons]
    simp only [List.cons_ne_nil, if_false]
    exact ih (f x j)

/-- Original `IN_option_rwt2`: membership in an option-selected set. -/
@[hol "cakeml/misc/miscScript.sml" "IN_option_rwt2"]
theorem mem_option_case {α β : Type} (x : α) (opt : Option β) (s : β → Set α) :
    x ∈ (match opt with | none => ∅ | some y => s y) ↔ ∃ y, opt = some y ∧ x ∈ s y := by
  cases opt with
  | none => simp
  | some y => simp

/-- Original `between_def`: the half-open interval predicate. -/
@[hol "cakeml/misc/miscScript.sml" "between_def"]
def between (x y z : Nat) : Bool := decide (x ≤ z) && decide (z < y)

/-- Original `IN_between`: membership in the interval predicate. -/
@[hol "cakeml/misc/miscScript.sml" "IN_between"]
theorem mem_between (x y z : Nat) : between y z x = true ↔ y ≤ x ∧ x < z := by
  unfold between
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Original `map_some_eq_append`: appending maps to `SOME` is injective. -/
@[hol "cakeml/misc/miscScript.sml" "map_some_eq_append"]
theorem map_some_append_eq {α : Type} (l1 l2 l3 : List α) :
    l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  rw [← List.map_append]
  exact map_some_eq (l1 ++ l2) l3

/-- Original `every_shim`: a predicate on the second components of a pair list
is a predicate on the projected list. -/
@[hol "cakeml/misc/miscScript.sml" "every_shim"]
theorem all_snd {α β : Type} (l : List (α × β)) (P : β → Bool) :
    (l.all fun p => P p.2) = ((l.map Prod.snd).all P) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.all_cons, List.map_cons, ih]

/-- Original `every_shim2`: a conjunction predicate on pairs splits over the two
projections. -/
@[hol "cakeml/misc/miscScript.sml" "every_shim2"]
theorem all_pair_split {α β : Type} (l : List (α × β)) (P : α → Bool) (Q : β → Bool) :
    (l.all fun p => P p.1 && Q p.2) =
      ((l.all fun p => P p.1) && (l.all fun p => Q p.2)) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    simp only [List.all_cons, ih, Bool.and_assoc, Bool.and_left_comm]

/-- Original `plus_0_I`: adding zero pointwise is the identity. HOL marks this
`[simp]`; Lean keeps it as a function equality, so the attribute is not
reproduced (the pointwise form is definitional). -/
@[hol "cakeml/misc/miscScript.sml" "plus_0_I"]
theorem add_zero_fun : (fun (y : Nat) => 0 + y) = fun (y : Nat) => y := by
  funext y
  exact Nat.zero_add y

/-- Original `EVERY2_RC_same`: the reflexive closure relates every list to
itself pointwise. HOL's `RC R` is `λx y. x = y ∨ R x y` and `EVERY2` is
`LIST_REL`. -/
@[simp, hol "cakeml/misc/miscScript.sml" "EVERY2_RC_same"]
theorem forall₂_rc_same {α : Type} (R : α → α → Prop) (l : List α) :
    List.Forall₂ (fun x y => x = y ∨ R x y) l l := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih => exact List.Forall₂.cons (Or.inl rfl) ih

/-- Original `LIST_REL_MEM`: a pointwise relation is unchanged by requiring
both components to be members of the two lists, because `LIST_REL` (Lean's
`List.Forall₂`) already relates the elements in place. -/
@[hol "cakeml/misc/miscScript.sml" "LIST_REL_MEM"]
theorem forall₂_mem_iff {α β : Type} (xs : List α) (ys : List β) (P : α → β → Prop) :
    List.Forall₂ P xs ys ↔
      List.Forall₂ (fun x y => x ∈ xs → y ∈ ys → P x y) xs ys := by
  constructor
  · intro h
    exact List.Forall₂.imp (fun _ _ hab _ _ => hab) h
  · intro h
    refine List.forall₂_iff_get.mpr ⟨h.length_eq, ?_⟩
    intro i h1 h2
    exact (List.forall₂_iff_get.mp h).2 i h1 h2 (List.get_mem _ _) (List.get_mem _ _)

/-- Original `FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM`: a successful option fold
returns an element of the folded list. -/
@[hol "cakeml/misc/miscScript.sml" "FOLDL_OPTION_CHOICE_EQ_SOME_IMP_MEM"]
theorem foldl_option_choice_mem {α : Type} (y : α) :
    ∀ (x : Option α) (ls : List (Option α)),
      List.foldl (fun acc e => acc <|> e) x ls = some y → some y ∈ x :: ls := by
  intro x ls
  induction ls generalizing x with
  | nil =>
    intro h
    simp only [List.foldl_nil] at h
    simp [h]
  | cons e rest ih =>
    intro h
    simp only [List.foldl_cons] at h
    cases x with
    | none =>
      have h' : List.foldl (fun acc e => acc <|> e) e rest = some y := by
        simpa using h
      exact List.mem_cons.mpr (Or.inr (ih e h'))
    | some a =>
      have h' : some y ∈ some a :: rest := ih (some a) h
      rcases List.mem_cons.mp h' with h1 | h2
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2)))

/-- Original `LENGTH_EQ_FILTER_FILTER`: when every element satisfies exactly
one of the two predicates, the two filters partition the list. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_EQ_FILTER_FILTER"]
theorem length_eq_filter_filter {α : Type} (P Q : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, (P x = true ∨ Q x = true) ∧ ¬(P x = true ∧ Q x = true)) :
    xs.length = (xs.filter P).length + (xs.filter Q).length := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ t, (P x = true ∨ Q x = true) ∧ ¬(P x = true ∧ Q x = true) :=
      fun x hx => h x (by simp [hx])
    have ih' := ih ht
    cases hP : P a with
    | false =>
      have hQ : Q a = true := by
        rcases ha.1 with hp | hq
        · exact absurd hP (by
            rw [hp]
            simp)
        · exact hq
      have hP' : ¬ P a = true := by
        rw [hP]
        simp
      rw [List.length_cons, List.filter_cons_of_neg hP', List.filter_cons_of_pos hQ, ih']
      simp only [List.length_cons]
      omega
    | true =>
      have hQ : Q a = false := by
        exact Bool.eq_false_iff.mpr (fun hq => ha.2 ⟨hP, hq⟩)
      have hQ' : ¬ Q a = true := by
        rw [hQ]
        simp
      rw [List.length_cons, List.filter_cons_of_pos hP, List.filter_cons_of_neg hQ', ih']
      simp only [List.length_cons]
      omega

/-- Original `MEM_ZIP2`: a pair in a zip sits at a common in-range index. -/
@[hol "cakeml/misc/miscScript.sml" "MEM_ZIP2"
  (total_function_inhabitants := [α, β])]
theorem mem_zip2 {α β : Type} [Nonempty α] [Nonempty β] (l1 : List α) :
    ∀ (l2 : List β) (x : α × β), x ∈ l1.zip l2 →
      ∃ n, n < l1.length ∧ n < l2.length ∧ x = (holEl n l1, holEl n l2) := by
  induction l1 with
  | nil =>
    intro l2 x h
    simp at h
  | cons a t ih =>
    intro l2 x h
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with hx | hx
      · refine ⟨0, by simp, by simp, ?_⟩
        rw [hx]
        simp [holEl, holHd]
      · obtain ⟨n, hn1, hn2, hx⟩ := ih u x hx
        refine ⟨n + 1, by simp [hn1], by simp [hn2], ?_⟩
        rw [hx]
        simp [holEl_cons_succ]

/-- Original `revtakerev`: reversing a reversed take is a drop. -/
@[hol "cakeml/misc/miscScript.sml" "revtakerev"]
theorem reverse_take_reverse {α : Type} (n : Nat) (l : List α) (_h : n ≤ l.length) :
    (l.reverse.take n).reverse = l.drop (l.length - n) := by
  rw [List.reverse_take, List.reverse_reverse, List.length_reverse]

/-- Original `any_el_ALT`: the defaulted lookup agrees with the total `EL`. -/
@[hol "cakeml/misc/miscScript.sml" "any_el_ALT"
  (total_function_inhabitants := [α])]
theorem anyEl_eq {α : Type} [Nonempty α] (l : List α) :
    ∀ (n : Nat) (d : α), anyEl n l d = if n < l.length then holEl n l else d := by
  induction l with
  | nil =>
    intro n d
    simp [anyEl]
  | cons x xs ih =>
    intro n d
    cases n with
    | zero => simp [anyEl, holEl, holHd]
    | succ n =>
      simp only [anyEl, List.length_cons, Nat.succ_ne_zero, if_false, Nat.succ_lt_succ_iff,
        holEl_cons_succ]
      exact ih n d

/-- Original `SUM_MAP_BOUND`: a uniformly bounded map sums below length times
bound. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_MAP_BOUND"]
theorem sum_map_bound {α : Type} (f : α → Nat) (ls : List α) (c : Nat)
    (h : ∀ x, f x ≤ c) : (ls.map f).sum ≤ ls.length * c := by
  induction ls with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha : f a ≤ c := h a
    have ht : (t.map f).sum ≤ t.length * c := ih
    rw [Nat.succ_mul]
    omega

/-- Original `LUPDATE_commutes`: distinct updates commute. -/
@[hol "cakeml/misc/miscScript.sml" "LUPDATE_commutes"]
theorem lupdate_commutes {α : Type} (m n : Nat) (e1 e2 : α) (l : List α) (h : m ≠ n) :
    (l.set n e2).set m e1 = (l.set m e1).set n e2 := by
  induction l generalizing m n with
  | nil => rfl
  | cons x xs ih =>
    cases m with
    | zero =>
      cases n with
      | zero => exact absurd rfl h
      | succ n => simp [List.set]
    | succ m =>
      cases n with
      | zero => simp [List.set]
      | succ n =>
        simp only [List.set]
        rw [ih m n (by omega)]

/-- Original `LESS_EQ_LENGTH`: a prefix of the requested length exists. -/
@[hol "cakeml/misc/miscScript.sml" "LESS_EQ_LENGTH"]
theorem exists_prefix_of_le {α : Type} (xs : List α) :
    ∀ k, k ≤ xs.length → ∃ ys1 ys2 : List α, xs = ys1 ++ ys2 ∧ ys1.length = k := by
  induction xs with
  | nil =>
    intro k h
    have hk : k = 0 := by simpa using h
    subst hk
    exact ⟨[], [], rfl, rfl⟩
  | cons x rest ih =>
    intro k h
    cases k with
    | zero => exact ⟨[], x :: rest, rfl, rfl⟩
    | succ k =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at h
      obtain ⟨ys1, ys2, hsplit, hlen⟩ := ih k h
      exact ⟨x :: ys1, ys2, by simp [hsplit], by simp [hlen]⟩

/-- Original `LESS_LENGTH`: a strictly shorter prefix splits before an element. -/
@[hol "cakeml/misc/miscScript.sml" "LESS_LENGTH"]
theorem exists_prefix_of_lt {α : Type} (xs : List α) :
    ∀ k, k < xs.length → ∃ (ys1 : List α) (y : α) (ys2 : List α),
      xs = ys1 ++ y :: ys2 ∧ ys1.length = k := by
  induction xs with
  | nil =>
    intro k h
    simp at h
  | cons x rest ih =>
    intro k h
    cases k with
    | zero => exact ⟨[], x, rest, rfl, rfl⟩
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
      obtain ⟨ys1, y, ys2, hsplit, hlen⟩ := ih k h
      exact ⟨x :: ys1, y, ys2, by simp [hsplit], by simp [hlen]⟩

/-- Dropping the last element of a list with at least two elements keeps the
head. -/
private theorem dropLast_cons_cons {α : Type} (a b : α) (rest : List α) :
    (a :: b :: rest).dropLast = a :: (b :: rest).dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take]
  simp only [List.length_cons]
  rw [show rest.length + 1 + 1 - 1 = rest.length + 1 by omega,
    show rest.length + 1 - 1 = rest.length by omega]
  rw [List.take_succ_cons]

/-- Original `MAP_REVERSE_STEP`: reversing a map splits off the last element. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_REVERSE_STEP"
  (total_function_inhabitants := [α])]
theorem map_reverse_step {α β : Type} [Nonempty α] (x : List α) (f : α → β)
    (h : x ≠ []) :
    x.reverse.map f = f (holLast x) :: (x.dropLast.reverse).map f := by
  induction x with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => simp [holLast]
    | cons b rest =>
      have hlast : holLast (a :: b :: rest) = holLast (b :: rest) := by simp [holLast]
      rw [hlast, dropLast_cons_cons]
      rw [show (a :: b :: rest).reverse = (b :: rest).reverse ++ [a] by
        rw [List.reverse_cons]]
      rw [show (a :: (b :: rest).dropLast).reverse = (b :: rest).dropLast.reverse ++ [a] by
        rw [List.reverse_cons]]
      rw [List.map_append, List.map_append]
      rw [ih (by simp)]
      rfl

/-- Original `ALL_DISTINCT_APPEND_APPEND_IMP`: distinctness of a triple append
restricts to the pairwise appends. -/
@[hol "cakeml/misc/miscScript.sml" "ALL_DISTINCT_APPEND_APPEND_IMP"]
theorem nodup_append_append {α : Type} (xs ys zs : List α)
    (h : (xs ++ ys ++ zs).Nodup) :
    (xs ++ ys).Nodup ∧ (xs ++ zs).Nodup ∧ (ys ++ zs).Nodup := by
  rw [List.nodup_append] at h
  obtain ⟨hxy, hz, hd⟩ := h
  rw [List.nodup_append] at hxy
  obtain ⟨hx, hy, hdxy⟩ := hxy
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hx, hy, hdxy⟩
  · rw [List.nodup_append]
    exact ⟨hx, hz, fun a ha b hb => hd a (List.mem_append_left ys ha) b hb⟩
  · rw [List.nodup_append]
    exact ⟨hy, hz, fun a ha b hb => hd a (List.mem_append_right xs ha) b hb⟩

/-- Original `FOLDR_CONS_triple`: folding a triple cons over a list of triples
is a map followed by the initial accumulator. -/
@[hol "cakeml/misc/miscScript.sml" "FOLDR_CONS_triple"]
theorem foldr_cons_triple {α β γ δ : Type} (f : α → β → γ → δ)
    (ls : List (α × β × γ)) (a : List δ) :
    ls.foldr (fun p w => match p with | (x, y, z) => f x y z :: w) a =
      (ls.map fun p => match p with | (x, y, z) => f x y z) ++ a := by
  induction ls with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, y, z⟩
    simp only [List.foldr_cons, List.map_cons, ih, List.cons_append]

/-- Original `MAP_ZIP_SND_triple`: mapping the pair components of a zip equals
mapping the curried function over the second list. -/
@[hol "cakeml/misc/miscScript.sml" "MAP_ZIP_SND_triple"]
theorem map_zip_snd_triple {α β γ δ : Type} (f : β → γ → δ)
    (l1 : List α) (l2 : List (β × γ)) (h : l1.length = l2.length) :
    (l1.zip l2).map (fun p => match p with | (_x, y, z) => f y z) =
      l2.map (fun p => f p.1 p.2) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons p rest => simp at h
  | cons a t ih =>
    cases l2 with
    | nil => simp at h
    | cons p rest =>
      rcases p with ⟨b, c⟩
      simp only [List.zip_cons_cons, List.map_cons, List.length_cons] at h ⊢
      rw [ih rest (by omega)]

/-- Original `TAKE_DROP_SUBLIST`: a prefix of a dropped suffix reassembles the
list. -/
@[hol "cakeml/misc/miscScript.sml" "TAKE_DROP_SUBLIST"]
theorem take_drop_sublist {α : Type} (ls ll : List α) (n nlll : Nat)
    (hpre : ll <+: ls.drop n) (_hn : n < ls.length) (hnlll : nlll = n + ll.length) :
    ls.take n ++ ll ++ ls.drop nlll = ls := by
  obtain ⟨t, ht⟩ := hpre
  subst hnlll
  have hdrop : ls.drop (n + ll.length) = t := by
    rw [← List.drop_drop, ← ht, List.drop_left]
  rw [hdrop]
  conv_rhs =>
    rw [← List.take_append_drop n ls, ← ht]
  rw [List.append_assoc]

/-- Flapjack infrastructure: twice the sum of the first `n` numbers. -/
theorem sum_range_double (n : Nat) : 2 * (List.range n).sum = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.mul_add, ih]
    have h : n * (n - 1) + 2 * n = (n + 1) * n := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_mul, Nat.one_mul]
      have hn : n ≤ n * n := Nat.le_mul_self n
      omega
    rw [h]
    have h' : n + 1 - 1 = n := by omega
    rw [h']

/-- Original `SUM_COUNT_LIST`: the first `n` numbers sum to `n * (n-1) / 2`. -/
@[hol "cakeml/misc/miscScript.sml" "SUM_COUNT_LIST"]
theorem sum_range {n : Nat} : (List.range n).sum = n * (n - 1) / 2 := by
  have h := sum_range_double n
  omega

end Flapjack
