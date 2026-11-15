module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants

@[expose] public section

/-! Parity of locations assigned by closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open ClosLang ClosProps

mutual
private theorem evenExpr (e : Exp) (n : Nat) (hn : n % 2 = 0) :
    (renumber n e).1 % 2 = 0 ∧ ∀ x ∈ codeLocationsExp (renumber n e).2, x % 2 = 0 := by
  cases e with
  | var tr v => simp [renumber, codeLocationsExp, hn]
  | raise tr e =>
    have ih := evenExpr e n hn
    cases h : renumber n e with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | tick tr e =>
    have ih := evenExpr e n hn
    cases h : renumber n e with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | ifThenElse tr a b c =>
    cases ha : renumber n a with
    | mk na oa =>
      have h1 := evenExpr a n hn
      simp only [ha] at h1
      cases hb : renumber na b with
      | mk nb ob =>
        have h2 := evenExpr b na h1.1
        simp only [hb] at h2
        cases hc : renumber nb c with
        | mk nc oc =>
          have h3 := evenExpr c nb h2.1
          simp only [hc] at h3
          simpa [renumber, ha, hb, hc, codeLocationsExp, List.forall_mem_append, or_imp, forall_and] using
            And.intro h3.1 (And.intro h1.2 (And.intro h2.2 h3.2))
  | «let» tr args body =>
    cases ha : renumberList n args with
    | mk na oa =>
      have h1 := evenList args n hn
      simp only [ha] at h1
      cases hb : renumber na body with
      | mk nb ob =>
        have h2 := evenExpr body na h1.1
        simp only [hb] at h2
        simpa [renumber, ha, hb, codeLocationsExp, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 h2.2)
  | handle tr a b =>
    cases ha : renumber n a with
    | mk na oa =>
      have h1 := evenExpr a n hn
      simp only [ha] at h1
      cases hb : renumber na b with
      | mk nb ob =>
        have h2 := evenExpr b na h1.1
        simp only [hb] at h2
        simpa [renumber, ha, hb, codeLocationsExp, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 h2.2)
  | call tr ticks loc args =>
    have ih := evenList args n hn
    cases h : renumberList n args with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | op tr op args =>
    have ih := evenList args n hn
    cases h : renumberList n args with
    | mk m out => simpa [renumber, h, codeLocationsExp] using ih
  | app tr loc f args =>
    cases hf : renumber n f with
    | mk nf ofun =>
      have h1 := evenExpr f n hn
      simp only [hf] at h1
      cases ha : renumberList nf args with
      | mk na oa =>
        have h2 := evenList args nf h1.1
        simp only [ha] at h2
        simpa [renumber, hf, ha, codeLocationsExp, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 h2.2)
  | fn name loc vs arity body =>
    have ih := evenExpr body n hn
    cases h : renumber n body with
    | mk m out =>
      simp only [h] at ih
      simp only [renumber, h, codeLocationsExp, Option.getD_some, List.forall_mem_append,
        List.forall_mem_singleton]
      exact ⟨by omega, ih.2, ih.1⟩
  | letrec names loc vs fs body =>
    cases hf : renumberFuns n fs with
    | mk m outFuns =>
      have h1 := evenFuns fs n hn
      simp only [hf] at h1
      have startEven : (m + 2 * outFuns.length) % 2 = 0 := by omega
      cases hb : renumber (m + 2 * outFuns.length) body with
      | mk next outBody =>
        have h2 := evenExpr body (m + 2 * outFuns.length) startEven
        simp only [hb] at h2
        have rangeEven : ∀ x ∈ (List.range outFuns.length).map (fun i => m + 2 * i), x % 2 = 0 := by
          intro x hx
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
          omega
        simpa [renumber, hf, hb, codeLocationsExp, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 (And.intro rangeEven h2.2))
termination_by sizeOf e

private theorem evenList (es : List Exp) (n : Nat) (hn : n % 2 = 0) :
    (renumberList n es).1 % 2 = 0 ∧ ∀ x ∈ codeLocations (renumberList n es).2, x % 2 = 0 := by
  cases es with
  | nil => simp [renumberList, codeLocations, hn]
  | cons e es =>
    cases he : renumber n e with
    | mk ne oe =>
      have h1 := evenExpr e n hn
      simp only [he] at h1
      cases hs : renumberList ne es with
      | mk ns os =>
        have h2 := evenList es ne h1.1
        simp only [hs] at h2
        simpa [renumberList, he, hs, codeLocations, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 h2.2)
termination_by sizeOf es

private theorem evenFuns (fs : List (Nat × Exp)) (n : Nat) (hn : n % 2 = 0) :
    (renumberFuns n fs).1 % 2 = 0 ∧ ∀ x ∈ codeLocationsFuns (renumberFuns n fs).2, x % 2 = 0 := by
  cases fs with
  | nil => simp [renumberFuns, codeLocationsFuns, hn]
  | cons f fs =>
    obtain ⟨arity, body⟩ := f
    cases hb : renumber n body with
    | mk nb ob =>
      have h1 := evenExpr body n hn
      simp only [hb] at h1
      cases hs : renumberFuns nb fs with
      | mk ns os =>
        have h2 := evenFuns fs nb h1.1
        simp only [hs] at h2
        simpa [renumberFuns, hb, hs, codeLocationsFuns, List.forall_mem_append, or_imp, forall_and] using
          And.intro h2.1 (And.intro h1.2 h2.2)
termination_by sizeOf fs
decreasing_by all_goals subst_vars; simp_wf <;> omega
end

/-- Numbering from an even location yields an even next location and assigns
only even code locations, for lists and individual expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_EVEN"]
theorem renumberCodeLocs_even :
    (∀ n es, n % 2 = 0 → (renumberList n es).1 % 2 = 0 ∧
      ∀ x ∈ codeLocations (renumberList n es).2, x % 2 = 0) ∧
    (∀ n e, n % 2 = 0 → (renumber n e).1 % 2 = 0 ∧
      ∀ x ∈ codeLocations [(renumber n e).2], x % 2 = 0) := by
  constructor
  · intro n es hn
    exact evenList es n hn
  · intro n e hn
    simpa [codeLocations_singleton] using evenExpr e n hn

/-- An even starting location produces an even next location. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "renumber_code_locs_imp_EVEN"]
theorem renumberCodeLocs_imp_even (n next : Nat) (es out : List Exp) (e result : Exp) :
    (renumberList n es = (next, out) ∧ n % 2 = 0 → next % 2 = 0) ∧
    (renumber n e = (next, result) ∧ n % 2 = 0 → next % 2 = 0) := by
  constructor
  · rintro ⟨run, even⟩
    have h := (renumberCodeLocs_even.1 n es even).1
    simpa [run] using h
  · rintro ⟨run, even⟩
    have h := (renumberCodeLocs_even.2 n e even).1
    simpa [run] using h

end Flapjack.Compiler.Backend.ClosNumber
