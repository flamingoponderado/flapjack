module

public import Flapjack.HolRef
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

end Flapjack
