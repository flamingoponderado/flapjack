module

public import Flapjack.FiniteMap.CardinalityExact
public import Flapjack.Misc.Option
public import Flapjack.Misc.Sptree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Construction of the direct-call proof state from a code map. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- Finite specialization of HOL SET_TO_LIST: use a shared interpretation of
HOL CHOICE and Lean epsilon; the concrete order is unspecified. -/
private noncomputable def setToListAux (s : Finset Nat) : List Nat := by
  classical
  exact if h : s.Nonempty then
    let chosen := Classical.epsilon (fun n => n ∈ s)
    chosen :: setToListAux (s.erase chosen)
  else []
termination_by s.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (Classical.epsilon_spec h)

private theorem setToListAux_step (s : Finset Nat) (h : s.Nonempty) :
    setToListAux s = Classical.epsilon (fun n => n ∈ s) ::
      setToListAux (s.erase (Classical.epsilon (fun n => n ∈ s))) := by
  rw [setToListAux]
  simp only [dite_eq_left h]

private theorem setToListAux_empty : setToListAux ∅ = [] := by
  rw [setToListAux]
  simp

private theorem mem_setToListAux (s : Finset Nat) (n : Nat) : n ∈ setToListAux s ↔ n ∈ s := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases h : s.Nonempty
    · rw [setToListAux_step s h, List.mem_cons]
      have hc : Classical.epsilon (fun n => n ∈ s) ∈ s := Classical.epsilon_spec h
      rw [ih _ (Finset.erase_ssubset hc)]
      simp only [Finset.mem_erase]
      constructor
      · rintro (equal | ⟨_, member⟩)
        · simpa [equal] using hc
        · exact member
      · intro member
        by_cases equal : n = Classical.epsilon (fun n => n ∈ s)
        · exact Or.inl equal
        · exact Or.inr ⟨equal, member⟩
    · have empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst s
      simp [setToListAux_empty]

/-- Each enumerated key is defined in the input map. This Flapjack-specific
domain fact supports the HOL FAPPLY and Lean lookup comparison; it has no
separate HOL declaration. -/
theorem mkCodeG_keys_defined {B : Type} (code : HolFiniteMapExact Nat B) (key : Nat)
    (member : key ∈ setToListAux code.domain_finite.toFinset) : code.lookup key ≠ none := by
  have h := (mem_setToListAux _ _).mp member
  exact code.domain_finite.mem_toFinset.mp h

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The source code map has the canonical finite-support codec. -/
theorem holFmapAsFiniteSupportParamWitness_mkCodeG_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Build the proof-state tree and auxiliary list from the same choice-ordered
code domain. HOL CHOICE is interpreted by Lean epsilon; its concrete order is
unspecified, and is not a claim of matching the HOL enumeration. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "mk_code_g_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def mkCodeG {B : Type} [Nonempty B] (code : HolFiniteMapExact Nat B) :
    NumSet × List (Nat × B) := by
  let keys := setToListAux code.domain_finite.toFinset
  exact ((keys.map Nat.pred).foldr (fun key tree => sptInsert key () tree) .ln,
    keys.map (fun key => (key, holThe (code.lookup key))))
end Flapjack.Compiler.Backend.ClosCall
