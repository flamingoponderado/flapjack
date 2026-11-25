module

public import Flapjack.TypeSystemHOL.Environments
public import Flapjack.TypeSystemHOL.TypeNames
public import Flapjack.FiniteMap.AlistExact
public import Flapjack.Misc.ListLookup

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
    obtain ⟨value, found⟩ := Flapjack.Misc.lookupZipExists tvs ts lengths name member
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

/-- List recursion for the zero-increment theorem, not a separate HOL
  declaration. -/
private theorem deBruijnIncList_eq_map (skip amount : Nat) (ts : List SemanticT) :
    deBruijnIncList skip amount ts = ts.map (deBruijnInc skip amount) := by
  induction ts with
  | nil => simp [deBruijnIncList]
  | cons t ts ih => simp only [deBruijnIncList, List.map_cons, ih]

/-- A zero increment leaves every type unchanged, pointwise and over lists. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_inc0"]
theorem deBruijnInc_zero :
    (∀ (t : SemanticT) (sk : Nat), deBruijnInc sk 0 t = t) ∧
      ∀ (ts : List SemanticT) (sk : Nat), ts.map (deBruijnInc sk 0) = ts := by
  have pointwise : ∀ (t : SemanticT) (sk : Nat), deBruijnInc sk 0 t = t := by
    refine deBruijnInc.induct (fun t => ∀ sk, deBruijnInc sk 0 t = t)
      (fun ts => ∀ sk, ts.map (deBruijnInc sk 0) = ts) ?_ ?_ ?_ ?_ ?_
    · intro tv sk
      simp [deBruijnInc]
    · intro n sk
      simp only [deBruijnInc]
      simp
    · intro ts id ih sk
      simp only [deBruijnInc, deBruijnIncList_eq_map, ih sk]
    · intro sk
      simp
    · intro t ts ih1 ih2 sk
      simp only [List.map_cons, ih1 sk, ih2 sk]
  refine ⟨pointwise, ?_⟩
  intro ts sk
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.map_cons, pointwise t sk, ih]

/-- Two successive increments compose into a single increment by the sum. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_inc_deBruijn_inc"]
theorem deBruijnInc_deBruijnInc (sk i2 : Nat) :
    ∀ (t : SemanticT) (i1 : Nat),
      deBruijnInc sk i1 (deBruijnInc sk i2 t) = deBruijnInc sk (i1 + i2) t := by
  have pointwise : ∀ (t : SemanticT) (i1 : Nat),
      deBruijnInc sk i1 (deBruijnInc sk i2 t) = deBruijnInc sk (i1 + i2) t := by
    refine deBruijnInc.induct
      (fun t => ∀ i1, deBruijnInc sk i1 (deBruijnInc sk i2 t) = deBruijnInc sk (i1 + i2) t)
      (fun ts => ∀ i1, deBruijnIncList sk i1 (deBruijnIncList sk i2 ts) =
        deBruijnIncList sk (i1 + i2) ts) ?_ ?_ ?_ ?_ ?_
    · intro tv i1
      simp [deBruijnInc]
    · intro n i1
      simp only [deBruijnInc]
      by_cases inside : n < sk
      · simp [inside]
      · have outside : ¬ n + i2 < sk := by omega
        simp [inside, outside]
        omega
    · intro ts id ih i1
      simp only [deBruijnInc, ih i1]
    · intro i1
      simp [deBruijnIncList]
    · intro t ts ih1 ih2 i1
      simp only [deBruijnIncList, ih1 i1, ih2 i1]
  intro t i1
  exact pointwise t i1

/-- A type whose free variables are in range is left alone by any increment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "nil_deBruijn_inc"]
theorem nil_deBruijnInc (skip tvs : Nat) :
    ∀ (t : SemanticT),
      (checkFreevars skip [] t = true ∨ checkFreevars skip [] (deBruijnInc skip tvs t) = true) →
        deBruijnInc skip tvs t = t := by
  refine deBruijnInc.induct
    (fun t =>
      (checkFreevars skip [] t = true ∨
          checkFreevars skip [] (deBruijnInc skip tvs t) = true) →
        deBruijnInc skip tvs t = t)
    (fun ts => (checkFreevarsList skip [] ts = true ∨
        checkFreevarsList skip [] (deBruijnIncList skip tvs ts) = true) →
      deBruijnIncList skip tvs ts = ts) ?_ ?_ ?_ ?_ ?_
  · intro tv h
    simp [deBruijnInc]
  · intro n h
    simp only [deBruijnInc, checkFreevars] at h ⊢
    by_cases inside : n < skip
    · simp [inside]
    · simp [inside] at h ⊢
      omega
  · intro ts id ih h
    simp only [deBruijnInc, checkFreevars] at h ⊢
    rw [ih h]
  · intro h
    simp [deBruijnIncList]
  · intro t ts ih1 ih2 h
    simp only [deBruijnIncList, checkFreevarsList, Bool.and_eq_true] at h ⊢
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ih1 (Or.inl h1), ih2 (Or.inl h2)]
    · rw [ih1 (Or.inr h1), ih2 (Or.inr h2)]

/-- A type whose free variables are in range is left alone by any substitution. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "nil_deBruijn_subst"]
theorem nil_deBruijnSubst (skip : Nat) (tvs : List SemanticT) :
    ∀ (t : SemanticT), checkFreevars skip [] t = true → deBruijnSubst skip tvs t = t := by
  refine deBruijnSubst.induct skip tvs
    (fun t => checkFreevars skip [] t = true → deBruijnSubst skip tvs t = t)
    (fun ts => checkFreevarsList skip [] ts = true → deBruijnSubstList skip tvs ts = ts)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro tv h
    simp [deBruijnSubst]
  · intro n range h
    have lt : n < skip := by simpa [checkFreevars] using h
    omega
  · intro n range lower h
    have lt : n < skip := by simpa [checkFreevars] using h
    omega
  · intro n range lower h
    simp [deBruijnSubst, lower]
  · intro ts id ih h
    simp only [deBruijnSubst, checkFreevars] at h ⊢
    rw [ih h]
  · intro h
    simp [deBruijnSubstList]
  · intro t ts ih1 ih2 h
    simp only [deBruijnSubstList, checkFreevarsList, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [ih1 h1, ih2 h2]

/-- A list of types under a well-formed substitution preserves the declared
free-variable bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_freevars_subst_list"]
theorem checkFreevarsSubstList (dbmax : Nat) (tvs tvs' : List MlString) (ts ts' : List SemanticT) :
    tvs.length = ts.length ∧ ts'.all (checkFreevars dbmax tvs) = true ∧
      ts.all (checkFreevars dbmax tvs') = true →
      (ts'.map (typeSubst (Flapjack.HolFiniteMapExact.alistToFmap (tvs.zip ts)))).all
        (checkFreevars dbmax tvs') = true := by
  intro h
  induction ts' with
  | nil => simp
  | cons t rest ih =>
    simp only [List.all_cons, List.map_cons, Bool.and_eq_true] at h ⊢
    obtain ⟨hlen, rest1, hvals⟩ := h
    obtain ⟨hhead, hrest⟩ := rest1
    exact ⟨checkFreevarsSubstSingle dbmax tvs t tvs' ts ⟨hlen, hhead, hvals⟩,
      ih ⟨hlen, hrest, hvals⟩⟩

/-- A well-formed de Bruijn substitution preserves the declared free-variable
bound. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_freevars"]
theorem deBruijn_subst_freevars (skip : Nat) (targs : List SemanticT) (t : SemanticT)
    (tvs : Nat) :
    skip = 0 ∧ targs.all (checkFreevars tvs []) = true ∧
      checkFreevars targs.length [] t = true →
      checkFreevars tvs [] (deBruijnSubst skip targs t) = true := by
  rintro ⟨rfl, hall, hbound⟩
  have substList_eq_map : ∀ ts : List SemanticT,
      deBruijnSubstList 0 targs ts = ts.map (deBruijnSubst 0 targs) := by
    intro ts
    induction ts with
    | nil => simp [deBruijnSubstList]
    | cons u us ih => simp only [deBruijnSubstList, List.map_cons, ih]
  have listEqAll : ∀ (dbmax : Nat) (ts : List SemanticT),
      checkFreevarsList dbmax [] ts = ts.all (checkFreevars dbmax []) := by
    intro dbmax ts
    induction ts with
    | nil => simp [checkFreevarsList]
    | cons u us ih => simp only [checkFreevarsList, List.all_cons, ih]
  have pointwise : ∀ (u : SemanticT), checkFreevars targs.length [] u = true →
      checkFreevars tvs [] (deBruijnSubst 0 targs u) = true := by
    refine deBruijnSubst.induct 0 targs
      (fun u => checkFreevars targs.length [] u = true →
        checkFreevars tvs [] (deBruijnSubst 0 targs u) = true)
      (fun us => checkFreevarsList targs.length [] us = true →
        (us.map (deBruijnSubst 0 targs)).all (checkFreevars tvs []) = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro tv checked
      exact absurd checked (by simp [checkFreevars])
    · intro m range checked
      have bound : m < targs.length := by simpa [checkFreevars] using checked
      have inside : 0 ≤ m ∧ m < targs.length + 0 := by omega
      simp only [deBruijnSubst, dif_pos inside]
      exact (List.all_eq_true.mp hall) targs[m] (List.getElem_mem bound)
    · intro m range lower checked
      have bound : m < targs.length := by simpa [checkFreevars] using checked
      exfalso
      omega
    · intro m range lower checked
      exfalso
      omega
    · intro us id ih checked
      have inner : checkFreevarsList targs.length [] us = true := by
        simpa [checkFreevars] using checked
      simp only [deBruijnSubst, checkFreevars]
      rw [substList_eq_map, listEqAll]
      exact ih inner
    · intro checked
      simp
    · intro u us ih1 ih2 checked
      rw [listEqAll] at checked
      simp only [List.all_cons, Bool.and_eq_true] at checked
      have tailChecked : checkFreevarsList targs.length [] us = true := by
        rw [listEqAll]
        exact checked.2
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
      exact ⟨ih1 checked.1, ih2 tailChecked⟩
  exact pointwise t hbound

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

/-- Substituting the identity context (the de Bruijn variables below the bound)
leaves any in-range type unchanged, pointwise and over lists. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "deBruijn_subst_id"]
theorem deBruijnSubst_id :
    (∀ (t : SemanticT) (n : Nat),
        checkFreevars n [] t = true →
          deBruijnSubst 0 ((List.range n).map SemanticT.varDb) t = t) ∧
      ∀ (ts : List SemanticT) (n : Nat),
        ts.all (checkFreevars n []) = true →
          ts.map (deBruijnSubst 0 ((List.range n).map SemanticT.varDb)) = ts := by
  have substList_eq_map : ∀ (replacement ts : List SemanticT),
      deBruijnSubstList 0 replacement ts = ts.map (deBruijnSubst 0 replacement) := by
    intro replacement ts
    induction ts with
    | nil => simp [deBruijnSubstList]
    | cons t ts ih => simp only [deBruijnSubstList, List.map_cons, ih]
  have general : ∀ (replacement : List SemanticT),
      (∀ (i : Nat) (h : i < replacement.length), replacement[i]'h = SemanticT.varDb i) →
      ∀ (t : SemanticT), checkFreevars replacement.length [] t = true →
        deBruijnSubst 0 replacement t = t := by
    intro replacement point
    refine deBruijnSubst.induct 0 replacement
      (fun t => checkFreevars replacement.length [] t = true → deBruijnSubst 0 replacement t = t)
      (fun ts => checkFreevarsList replacement.length [] ts = true →
        ts.map (deBruijnSubst 0 replacement) = ts) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro tv checked
      simp [deBruijnSubst]
    · intro m range checked
      have inside : 0 ≤ m ∧ m < replacement.length + 0 := by omega
      simp only [deBruijnSubst, dif_pos inside]
      exact point m (by omega)
    · intro m range lower checked
      have lt : m < replacement.length := by simpa [checkFreevars] using checked
      exfalso
      omega
    · intro m range lower checked
      exfalso
      omega
    · intro ts id ih checked
      have inner : checkFreevarsList replacement.length [] ts = true := by
        simpa [checkFreevars] using checked
      simp only [deBruijnSubst]
      rw [substList_eq_map, ih inner]
    · intro checked
      simp
    · intro t ts ih1 ih2 checked
      simp only [checkFreevarsList, Bool.and_eq_true] at checked
      simp only [List.map_cons, ih1 checked.1, ih2 checked.2]
  constructor
  · intro t n checked
    have len : ((List.range n).map SemanticT.varDb).length = n := by simp
    exact general ((List.range n).map SemanticT.varDb) (by
      intro i bound
      rw [List.getElem_map, List.getElem_range]) t (by simpa [len] using checked)
  · intro ts n checked
    induction ts with
    | nil => simp
    | cons t ts ih =>
      simp only [List.all_cons, Bool.and_eq_true] at checked
      have len : ((List.range n).map SemanticT.varDb).length = n := by simp
      have head := general ((List.range n).map SemanticT.varDb) (by
        intro i bound
        rw [List.getElem_map, List.getElem_range]) t (by simpa [len] using checked.1)
      simp only [List.map_cons, head, ih checked.2]

end Flapjack.TypeSysProps
