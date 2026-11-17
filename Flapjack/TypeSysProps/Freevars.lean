module

public import Flapjack.TypeSystemHOL.Environments
public import Flapjack.TypeSystemHOL.TypeNames
public import Flapjack.FiniteMap.AlistExact

@[expose] public section

/-! Free-variable bounds for declarative types. -/
namespace Flapjack.TypeSysProps
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

mutual
/-- Increasing the de Bruijn bound preserves a free-variable check. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_add"]
theorem checkFreevarsAdd (tvs : Nat) (names : List MlString) (t : SemanticT) :
    checkFreevars tvs names t = true → ∀ tvs', tvs ≤ tvs' → checkFreevars tvs' names t = true := by
  intro checked tvs' bound
  cases t with
  | var name => simpa [checkFreevars] using checked
  | varDb index =>
    simp only [checkFreevars, decide_eq_true_eq] at checked ⊢
    omega
  | app args id =>
    simp only [checkFreevars] at checked ⊢
    exact checkFreevarsListAdd tvs names args checked tvs' bound
termination_by sizeOf t

/-- List traversal for the source free-variable induction, which HOL proves
within the same theorem rather than as a separate declaration. -/
private theorem checkFreevarsListAdd (tvs : Nat) (names : List MlString) (ts : List SemanticT) :
    checkFreevarsList tvs names ts = true → ∀ tvs', tvs ≤ tvs' →
      checkFreevarsList tvs' names ts = true := by
  intro checked tvs' bound
  cases ts with
  | nil => simp [checkFreevarsList]
  | cons t rest =>
    simp only [checkFreevarsList, Bool.and_eq_true] at checked ⊢
    exact ⟨checkFreevarsAdd tvs names t checked.1 tvs' bound,
      checkFreevarsListAdd tvs names rest checked.2 tvs' bound⟩
termination_by sizeOf ts
end

/-- The specialized lookup map used elsewhere agrees with the reviewed generic
HOL association-list map. This is a local representation bridge. -/
private theorem mapAgreement (entries : List (MlString × SemanticT)) :
    Flapjack.HolFiniteMapExact.alistToFmap entries = typeSubstMap entries := by
  unfold Flapjack.HolFiniteMapExact.alistToFmap typeSubstMap
  have same : (fun (a b : MlString) => Classical.propDecidable (a = b)) =
      inferInstanceAs (DecidableEq MlString) := Subsingleton.elim _ _
  rw [same]

/-- A zipped association list contains each key when both input lists have
equal length. This is local list infrastructure used by the source proof. -/
private theorem lookupZipExists (names : List MlString) (values : List SemanticT)
    (lengths : names.length = values.length) (name : MlString) (member : name ∈ names) :
    ∃ value, (names.zip values).lookup name = some value := by
  have keys : (names.zip values).map Prod.fst = names := List.map_fst_zip (by omega)
  have keyMember : name ∈ (names.zip values).map Prod.fst := by simpa [keys] using member
  obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp keyMember
  cases found : (names.zip values).lookup name with
  | none =>
    have absent := List.lookup_eq_none_iff.mp found entry entryMember
    simp [entryEq] at absent
  | some value => exact ⟨value, rfl⟩

mutual
/-- A well-formed substitution preserves the declared free-variable bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_subst_single"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem checkFreevarsSubstSingle (dbmax : Nat) (tvs : List MlString) (t : SemanticT)
    (tvs' : List MlString) (ts : List SemanticT) :
    tvs.length = ts.length ∧ checkFreevars dbmax tvs t = true ∧
      ts.all (checkFreevars dbmax tvs') = true →
    checkFreevars dbmax tvs' (typeSubst (Flapjack.HolFiniteMapExact.alistToFmap (tvs.zip ts)) t) = true := by
  rintro ⟨lengths, check, valuesCheck⟩
  cases t with
  | var name =>
    have member : name ∈ tvs := by simpa [checkFreevars] using check
    obtain ⟨value, found⟩ := lookupZipExists tvs ts lengths name member
    obtain ⟨before, after, zipped, _⟩ := List.lookup_eq_some_iff.mp found
    have pairMember : (name, value) ∈ tvs.zip ts := by rw [zipped]; simp
    have valueMember : value ∈ ts := (List.of_mem_zip pairMember).2
    have result := (List.all_eq_true.mp valuesCheck) value valueMember
    simpa [typeSubst, mapAgreement, lookupTypeSubstMap, found] using result
  | varDb index => simpa [typeSubst, checkFreevars] using check
  | app args id =>
    simp only [typeSubst, checkFreevars] at check ⊢
    exact substFreevarsList dbmax tvs args tvs' ts ⟨lengths, check, valuesCheck⟩
termination_by sizeOf t

/-- List traversal for the HOL substitution induction, with no separate
source declaration. -/
private theorem substFreevarsList (dbmax : Nat) (tvs : List MlString) (xs : List SemanticT)
    (tvs' : List MlString) (ts : List SemanticT) :
    tvs.length = ts.length ∧ checkFreevarsList dbmax tvs xs = true ∧
      ts.all (checkFreevars dbmax tvs') = true →
    checkFreevarsList dbmax tvs' (typeSubstList (Flapjack.HolFiniteMapExact.alistToFmap (tvs.zip ts)) xs) = true := by
  rintro ⟨lengths, checked, valuesCheck⟩
  cases xs with
  | nil => simp [typeSubstList, checkFreevarsList]
  | cons x xs =>
    simp only [typeSubstList, checkFreevarsList, Bool.and_eq_true] at checked ⊢
    exact ⟨checkFreevarsSubstSingle dbmax tvs x tvs' ts ⟨lengths, checked.1, valuesCheck⟩,
      substFreevarsList dbmax tvs xs tvs' ts ⟨lengths, checked.2, valuesCheck⟩⟩
termination_by sizeOf xs
end


end Flapjack.TypeSysProps
