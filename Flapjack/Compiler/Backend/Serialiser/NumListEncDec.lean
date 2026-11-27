module

public import Flapjack.Misc.AppList

@[expose] public section

/-!
# Encoder/decoder well-formedness for natural-number list prefixes

Counterparts of the `dec_ok` / `enc_dec_ok` / `enc_dec_ok'` predicates and the
first helper theorems of
`cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml`. HOL's `##` pair
map is Lean's `Prod.map` and HOL `∘` is composition.
-/

namespace Flapjack.Compiler.Backend.Serialiser

open Flapjack

/-- Original `dec_ok_def`: a decoder never returns more input than it consumed. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "dec_ok_def"]
def decOk {α : Type} (dec : List Nat → α × List Nat) : Prop :=
  ∀ i, (dec i).2.length ≤ i.length

/-- Original `enc_dec_ok_def`: the decoder inverts the encoder on any suffix. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok_def"]
def encDecOk {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat) : Prop :=
  decOk dec ∧ ∀ x xs, dec (appListAppend (enc x) ++ xs) = (x, xs)

/-- Original `dec_ok_simp`: mapping the decoded value does not change the bound. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "dec_ok_simp"]
theorem decOk_comp_map {α β : Type} (f : β → α) (d : List Nat → β × List Nat) :
    decOk (fun i => Prod.map f id (d i)) ↔ decOk d := by
  simp [decOk, Prod.map]

/-- Original `enc_dec_ok_o`: composing the encoder with a left inverse keeps the
    round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok_o"]
theorem encDecOk_comp {α β : Type} (e : α → AppList Nat) (d : List Nat → α × List Nat)
    (f : α → β) (g : β → α) (premise : encDecOk e d ∧ ∀ x, f (g x) = x) :
    encDecOk (fun x => e (g x)) (fun i => Prod.map f id (d i)) := by
  obtain ⟨⟨dec, roundtrip⟩, inverse⟩ := premise
  refine ⟨?_, ?_⟩
  · simpa [decOk, Prod.map] using dec
  · intro x xs
    simp only [Prod.map, id]
    rw [roundtrip (g x) xs, inverse]

/-- Original `enc_dec_ok'_def`: the conditional form of the round trip. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_def"]
def encDecOkPrime {α : Type} (p : α → Bool) (enc : α → AppList Nat)
    (dec : List Nat → α × List Nat) : Prop :=
  decOk dec ∧ ∀ x xs, p x = true → dec (appListAppend (enc x) ++ xs) = (x, xs)

/-- Original `IMP_enc_dec_ok`: an unconditional round trip is the total case. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "IMP_enc_dec_ok"]
theorem encDecOk_imp_prime {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat)
    (ok : encDecOk enc dec) : encDecOkPrime (fun _ => true) enc dec := by
  obtain ⟨bound, roundtrip⟩ := ok
  refine ⟨bound, ?_⟩
  intro x xs _
  exact roundtrip x xs

/-- Original `enc_dec_ok'_IMP`: the total conditional round trip is unconditional. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "enc_dec_ok'_IMP"]
theorem encDecOkPrime_imp {α : Type} (enc : α → AppList Nat) (dec : List Nat → α × List Nat)
    (ok : encDecOkPrime (fun _ => true) enc dec) : encDecOk enc dec := by
  obtain ⟨bound, roundtrip⟩ := ok
  exact ⟨bound, fun x xs => roundtrip x xs rfl⟩

/-- Original `const_dec_def`: a decoder that returns a fixed value. -/
@[hol "cakeml/compiler/backend/serialiser/num_list_enc_decScript.sml" "const_dec_def"]
def constDec {α : Type} (a : α) (xs : List Nat) : α × List Nat := (a, xs)

end Flapjack.Compiler.Backend.Serialiser
