module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
import Mathlib.Data.List.Sort

@[expose] public section

/-! Distinctness and bounds of closure locations assigned by numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

private def OrderedBetween (start stop : Nat) (xs : List Nat) : Prop :=
  xs.Pairwise (· < ·) ∧ ∀ x ∈ xs, start ≤ x ∧ x < stop

private theorem between_append {a b c : Nat} {xs ys : List Nat}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hxs : OrderedBetween a b xs) (hys : OrderedBetween b c ys) :
    OrderedBetween a c (xs ++ ys) := by
  refine ⟨List.pairwise_append.mpr ⟨hxs.1, hys.1, ?_⟩, ?_⟩
  · intro x hx y hy
    have hxBounds := hxs.2 x hx
    have hyBounds := hys.2 y hy
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have bounds := hxs.2 x hx; omega
    · have bounds := hys.2 x hx; omega

private theorem between_range (n len : Nat) :
    OrderedBetween n (n + 2 * len) ((List.range len).map (fun i => n + 2 * i)) := by
  constructor
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp (fun {a b} h => ?_) List.pairwise_lt_range
    omega
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi := List.mem_range.mp hi
    omega

mutual
private theorem orderedExpr (e : Exp) (n : Nat) :
    OrderedBetween n (renumber n e).1 (codeLocationsExp (renumber n e).2) := by
  cases e with
  | var tr v => simp [renumber, codeLocationsExp, OrderedBetween]
  | raise tr e =>
    have ih := orderedExpr e n
    cases h : renumber n e with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | tick tr e =>
    have ih := orderedExpr e n
    cases h : renumber n e with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | ifThenElse tr a b c =>
    cases ha : renumber n a with
    | mk na oa =>
      have h1 := orderedExpr a n
      have le1 := renumber_start_le a n
      simp only [ha] at h1 le1
      cases hb : renumber na b with
      | mk nb ob =>
        have h2 := orderedExpr b na
        have le2 := renumber_start_le b na
        simp only [hb] at h2 le2
        cases hc : renumber nb c with
        | mk nc oc =>
          have h3 := orderedExpr c nb
          have le3 := renumber_start_le c nb
          simp only [hc] at h3 le3
          have both := between_append le1 le2 h1 h2
          have all := between_append (Nat.le_trans le1 le2) le3 both h3
          simpa [renumber, ha, hb, hc, codeLocationsExp, List.append_assoc] using all
  | «let» tr args body =>
    cases ha : renumberList n args with
    | mk na oa =>
      have h1 := orderedList args n
      have le1 := renumberList_start_le args n
      simp only [ha] at h1 le1
      cases hb : renumber na body with
      | mk nb ob =>
        have h2 := orderedExpr body na
        have le2 := renumber_start_le body na
        simp only [hb] at h2 le2
        simpa [renumber, ha, hb, codeLocationsExp] using between_append le1 le2 h1 h2
  | handle tr a b =>
    cases ha : renumber n a with
    | mk na oa =>
      have h1 := orderedExpr a n
      have le1 := renumber_start_le a n
      simp only [ha] at h1 le1
      cases hb : renumber na b with
      | mk nb ob =>
        have h2 := orderedExpr b na
        have le2 := renumber_start_le b na
        simp only [hb] at h2 le2
        simpa [renumber, ha, hb, codeLocationsExp] using between_append le1 le2 h1 h2
  | call tr ticks loc args =>
    have ih := orderedList args n
    cases h : renumberList n args with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | op tr op args =>
    have ih := orderedList args n
    cases h : renumberList n args with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | app tr loc f args =>
    cases hf : renumber n f with
    | mk nf ofun =>
      have h1 := orderedExpr f n
      have le1 := renumber_start_le f n
      simp only [hf] at h1 le1
      cases ha : renumberList nf args with
      | mk na oa =>
        have h2 := orderedList args nf
        have le2 := renumberList_start_le args nf
        simp only [ha] at h2 le2
        simpa [renumber, hf, ha, codeLocationsExp] using between_append le1 le2 h1 h2
  | fn name loc vs arity body =>
    cases h : renumber n body with
    | mk m out =>
      have h1 := orderedExpr body n
      have le1 := renumber_start_le body n
      simp only [h] at h1 le1
      have singleton : OrderedBetween m (m + 2) [m] := by
        simp [OrderedBetween]
      have all := between_append le1 (by omega) h1 singleton
      simpa [renumber, h, codeLocationsExp] using all
  | letrec names loc vs fs body =>
    cases hf : renumberFuns n fs with
    | mk m outFuns =>
      have h1 := orderedFuns fs n
      have le1 := renumberFuns_start_le fs n
      simp only [hf] at h1 le1
      cases hb : renumber (m + 2 * outFuns.length) body with
      | mk next outBody =>
        have h2 := orderedExpr body (m + 2 * outFuns.length)
        have le2 := renumber_start_le body (m + 2 * outFuns.length)
        simp only [hb] at h2 le2
        have both := between_append le1 (by omega) h1 (between_range m outFuns.length)
        have all := between_append (by omega) le2 both h2
        simpa [renumber, hf, hb, codeLocationsExp, List.append_assoc] using all
termination_by sizeOf e

private theorem orderedList (es : List Exp) (n : Nat) :
    OrderedBetween n (renumberList n es).1 (codeLocations (renumberList n es).2) := by
  cases es with
  | nil => simp [renumberList, codeLocations, OrderedBetween]
  | cons e es =>
    cases he : renumber n e with
    | mk ne oe =>
      have h1 := orderedExpr e n
      have le1 := renumber_start_le e n
      simp only [he] at h1 le1
      cases hs : renumberList ne es with
      | mk ns os =>
        have h2 := orderedList es ne
        have le2 := renumberList_start_le es ne
        simp only [hs] at h2 le2
        simpa [renumberList, he, hs, codeLocations] using between_append le1 le2 h1 h2
termination_by sizeOf es

private theorem orderedFuns (fs : List (Nat × Exp)) (n : Nat) :
    OrderedBetween n (renumberFuns n fs).1 (codeLocationsFuns (renumberFuns n fs).2) := by
  cases fs with
  | nil => simp [renumberFuns, codeLocationsFuns, OrderedBetween]
  | cons f fs =>
    obtain ⟨arity, body⟩ := f
    cases hb : renumber n body with
    | mk nb ob =>
      have h1 := orderedExpr body n
      have le1 := renumber_start_le body n
      simp only [hb] at h1 le1
      cases hs : renumberFuns nb fs with
      | mk ns os =>
        have h2 := orderedFuns fs nb
        have le2 := renumberFuns_start_le fs nb
        simp only [hs] at h2 le2
        simpa [renumberFuns, hb, hs, codeLocationsFuns] using between_append le1 le2 h1 h2
termination_by sizeOf fs
decreasing_by all_goals subst_vars; simp_wf; omega
end

/-- The numbered expression list has distinct, bounded code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_list_distinct"]
theorem renumberList_codeLocations_distinct (n : Nat) (es : List Exp) :
    (codeLocations (renumberList n es).2).Nodup ∧
      (∀ x ∈ codeLocations (renumberList n es).2, n ≤ x) ∧
      (∀ x ∈ codeLocations (renumberList n es).2, x < (renumberList n es).1) := by
  have all := orderedList es n
  exact ⟨all.1.nodup, fun x hx => (all.2 x hx).1, fun x hx => (all.2 x hx).2⟩

/-- A numbered expression has distinct, bounded code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_distinct"]
theorem renumber_codeLocations_distinct (n : Nat) (e : Exp) :
    (codeLocations [(renumber n e).2]).Nodup ∧
      (∀ x ∈ codeLocations [(renumber n e).2], n ≤ x) ∧
      (∀ x ∈ codeLocations [(renumber n e).2], x < (renumber n e).1) := by
  have all := orderedExpr e n
  simpa [codeLocations_singleton] using
    And.intro all.1.nodup (And.intro (fun x hx => (all.2 x hx).1) (fun x hx => (all.2 x hx).2))

end Flapjack.Compiler.Backend.ClosNumber
