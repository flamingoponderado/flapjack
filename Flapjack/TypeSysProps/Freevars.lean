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

/-- The specialized type-substitution map agrees with the reviewed generic
HOL association-list map. This Flapjack representation lemma is shared by
the substitution and type-name proofs. -/
theorem alistToFmapEqTypeSubstMap (entries : List (MlString × SemanticT)) :
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
    simpa [typeSubst, alistToFmapEqTypeSubstMap, lookupTypeSubstMap, found] using result
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


mutual
/-- Shared induction for the two HOL de Bruijn substitution bounds. The
arithmetic premise is proved at each call; it is not an assumption of either
ported theorem. -/
private theorem substBound (source target : Nat) (names : List MlString) (t : SemanticT)
    (ts : List SemanticT) (bound : source ≤ target + ts.length)
    (checked : checkFreevars source names t = true)
    (args : ts.all (checkFreevars target names) = true) :
    checkFreevars target names (deBruijnSubst 0 ts t) = true := by
  cases t with
  | var name => simpa [deBruijnSubst, checkFreevars] using checked
  | varDb index =>
    have indexBound : index < source := by simpa [checkFreevars] using checked
    by_cases inside : index < ts.length
    · have replacement := (List.all_eq_true.mp args) ts[index] (List.getElem_mem inside)
      simpa [deBruijnSubst, inside] using replacement
    · simp only [deBruijnSubst, Nat.zero_le, true_and, Nat.add_zero, inside, ↓reduceDIte, ↓reduceIte,
        checkFreevars, decide_eq_true_eq]
      omega
  | app children id =>
    simp only [checkFreevars] at checked ⊢
    simp only [deBruijnSubst, checkFreevars]
    exact substListBound source target names children ts bound checked args
termination_by sizeOf t

/-- List traversal for the shared substitution induction; HOL performs this
recursion within its proofs. -/
private theorem substListBound (source target : Nat) (names : List MlString) (xs ts : List SemanticT)
    (bound : source ≤ target + ts.length) (checked : checkFreevarsList source names xs = true)
    (args : ts.all (checkFreevars target names) = true) :
    checkFreevarsList target names (deBruijnSubstList 0 ts xs) = true := by
  cases xs with
  | nil => simp [deBruijnSubstList, checkFreevarsList]
  | cons x xs =>
    simp only [checkFreevarsList, Bool.and_eq_true] at checked
    simp only [deBruijnSubstList, checkFreevarsList, Bool.and_eq_true]
    exact ⟨substBound source target names x ts bound checked.1 args,
      substListBound source target names xs ts bound checked.2 args⟩
termination_by sizeOf xs
end

/-- Substitution preserves a free-variable bound when both the source type and
replacement types satisfy it. The unused polymorphic binder is retained from HOL. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_check_freevars"]
theorem deBruijnSubstCheckFreevars {α : Type} (tvs : Nat) (names : List MlString) (t : SemanticT)
    (ts : List SemanticT) (_unused : α) :
    checkFreevars tvs names t = true ∧ ts.all (checkFreevars tvs names) = true →
      checkFreevars tvs names (deBruijnSubst 0 ts t) = true := by
  rintro ⟨checked, args⟩
  exact substBound tvs tvs names t ts (by omega) checked args

/-- Substituting a complete de Bruijn context preserves the replacements'
free-variable bound. Both unused polymorphic HOL binders are retained. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_check_freevars2"]
theorem deBruijnSubstCheckFreevars2 {α β : Type} (tvs : Nat) (names : List MlString) (t : SemanticT)
    (ts : List SemanticT) (_unused : α) (_unused2 : β) :
    checkFreevars ts.length names t = true ∧ ts.all (checkFreevars tvs names) = true →
      checkFreevars tvs names (deBruijnSubst 0 ts t) = true := by
  rintro ⟨checked, args⟩
  exact substBound ts.length tvs names t ts (by omega) checked args

mutual
/-- Increasing de Bruijn indices preserves a correspondingly increased
free-variable bound. This is the source-local HOL lemma. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_deBruijn_inc"]
theorem checkFreevarsDeBruijnInc (tvs : Nat) (names : List MlString) (t : SemanticT) :
    checkFreevars tvs names t = true → ∀ amount skip,
      checkFreevars (amount + tvs) names (deBruijnInc skip amount t) = true := by
  intro checked amount skip
  cases t with
  | var name => simpa [deBruijnInc, checkFreevars] using checked
  | varDb index =>
    simp only [checkFreevars, decide_eq_true_eq] at checked
    simp only [deBruijnInc, checkFreevars, decide_eq_true_eq]
    split <;> omega
  | app ts id =>
    simp only [checkFreevars] at checked
    simp only [deBruijnInc, checkFreevars]
    exact checkFreevarsListDeBruijnInc tvs names ts checked amount skip
termination_by sizeOf t

/-- List recursion for the source-local increment lemma, not a separate HOL
declaration. -/
private theorem checkFreevarsListDeBruijnInc (tvs : Nat) (names : List MlString) (ts : List SemanticT) :
    checkFreevarsList tvs names ts = true → ∀ amount skip,
      checkFreevarsList (amount + tvs) names (deBruijnIncList skip amount ts) = true := by
  intro checked amount skip
  cases ts with
  | nil => simp [deBruijnIncList, checkFreevarsList]
  | cons t rest =>
    simp only [checkFreevarsList, Bool.and_eq_true] at checked
    simp only [deBruijnIncList, checkFreevarsList, Bool.and_eq_true]
    exact ⟨checkFreevarsDeBruijnInc tvs names t checked.1 amount skip,
      checkFreevarsListDeBruijnInc tvs names rest checked.2 amount skip⟩
termination_by sizeOf ts
end

/-- Incrementing and then substituting preserves the stated free-variable
bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_subst_inc"]
theorem checkFreevarsSubstInc (tvs : Nat) (names : List MlString) (t : SemanticT) :
    checkFreevars tvs names t = true → ∀ rest (args : List SemanticT) amount,
      tvs = args.length + rest ∧ args.all (checkFreevars (amount + rest) names) = true →
      checkFreevars (amount + rest) names (deBruijnSubst 0 args (deBruijnInc args.length amount t)) = true := by
  intro checked rest args amount ⟨size, all⟩
  have increased := checkFreevarsDeBruijnInc tvs names t checked amount args.length
  apply substBound (amount + tvs) (amount + rest) names _ args
  · omega
  · exact increased
  · exact all

end Flapjack.TypeSysProps
