module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Flapjack.FiniteMap.AlistExact.Lookup
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

end Flapjack
