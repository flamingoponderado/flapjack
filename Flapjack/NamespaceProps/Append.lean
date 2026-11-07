import Flapjack.NamespaceHOL

/-! Namespace append infrastructure for compiler simulation proofs. -/
namespace Flapjack.NamespaceHOL

/-- Flapjack infrastructure for the HOL proofs: a short lookup in an appended
namespace chooses the first available binding. -/
theorem nsLookup_append_short {M N V : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (name : N) :
    nsLookup (nsAppend first second) (.short name) =
      (nsLookup first (.short name)).orElse (fun _ => nsLookup second (.short name)) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      simp [nsAppend, nsLookup, List.lookup_append]

/-- Flapjack infrastructure for the HOL proofs: a long lookup uses the first
namespace whenever it contains the initial module, even if the rest fails. -/
theorem nsLookup_append_long {M N V : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (moduleName : M) (rest : Ident M N) :
    nsLookup (nsAppend first second) (.long moduleName rest) =
      match nsLookupMod first [moduleName] with
      | none => nsLookup second (.long moduleName rest)
      | some _ => nsLookup first (.long moduleName rest) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      cases found : firstModules.lookup moduleName <;>
        simp [nsAppend, nsLookup, nsLookupMod, List.lookup_append, found]

/-- Flapjack infrastructure for the HOL proofs: module lookup in an append has
the same first-module shadowing rule. -/
theorem nsLookupMod_append_cons {M N V : Type} [DecidableEq M]
    (first second : Namespace M N V) (moduleName : M) (rest : List M) :
    nsLookupMod (nsAppend first second) (moduleName :: rest) =
      match nsLookupMod first [moduleName] with
      | none => nsLookupMod second (moduleName :: rest)
      | some _ => nsLookupMod first (moduleName :: rest) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      cases found : firstModules.lookup moduleName <;>
        simp [nsAppend, nsLookupMod, List.lookup_append, found]

/-- Flapjack infrastructure for the HOL proofs: corresponding namespaces
retain corresponding value domains after left-biased append. -/
private theorem nsDom_append_preserved {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstDomain : nsDom first = nsDom first') (secondDomain : nsDom second = nsDom second')
    (firstModules : nsDomMod first = nsDomMod first') :
    nsDom (nsAppend first second) = nsDom (nsAppend first' second') := by
  funext id
  apply propext
  have firstAt := congrFun firstDomain id
  have secondAt := congrFun secondDomain id
  change (∃ v, nsLookup first id = some v) = (∃ v, nsLookup first' id = some v) at firstAt
  change (∃ v, nsLookup second id = some v) = (∃ v, nsLookup second' id = some v) at secondAt
  change (∃ v, nsLookup (nsAppend first second) id = some v) ↔
    (∃ v, nsLookup (nsAppend first' second') id = some v)
  cases id with
  | short name =>
    simp only [nsLookup_append_short]
    cases h1 : nsLookup first (.short name) <;> cases h2 : nsLookup first' (.short name) <;>
      cases h3 : nsLookup second (.short name) <;> cases h4 : nsLookup second' (.short name) <;>
      simp_all
  | long moduleName rest =>
    have modulesAt := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modulesAt
    simp only [nsLookup_append_long]
    cases h1 : nsLookupMod first [moduleName] <;> cases h2 : nsLookupMod first' [moduleName] <;>
      simp_all

/-- Flapjack infrastructure for the HOL proofs: module domains also agree
after left-biased append. -/
private theorem nsDomMod_append_preserved {M N V W : Type} [DecidableEq M]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstModules : nsDomMod first = nsDomMod first')
    (secondModules : nsDomMod second = nsDomMod second') :
    nsDomMod (nsAppend first second) = nsDomMod (nsAppend first' second') := by
  funext path
  apply propext
  have firstAt := congrFun firstModules path
  have secondAt := congrFun secondModules path
  change (∃ v, nsLookupMod first path = some v) = (∃ v, nsLookupMod first' path = some v) at firstAt
  change (∃ v, nsLookupMod second path = some v) = (∃ v, nsLookupMod second' path = some v) at secondAt
  change (∃ v, nsLookupMod (nsAppend first second) path = some v) ↔
    (∃ v, nsLookupMod (nsAppend first' second') path = some v)
  cases path with
  | nil => simp [nsLookupMod]
  | cons moduleName rest =>
    have modulesAt := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modulesAt
    simp only [nsLookupMod_append_cons]
    cases h1 : nsLookupMod first [moduleName] <;> cases h2 : nsLookupMod first' [moduleName] <;>
      simp_all

/-- Corresponding value and module domains remain equal under namespace append. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsAppend_equal"]
theorem nsDom_nsAppend_equal {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (n₁ n₂ : Namespace M N V) (n₃ n₄ : Namespace M N W)
    (premises : nsDom n₁ = nsDom n₃ ∧ nsDom n₂ = nsDom n₄ ∧
      nsDomMod n₁ = nsDomMod n₃ ∧ nsDomMod n₂ = nsDomMod n₄) :
    nsDom (nsAppend n₁ n₂) = nsDom (nsAppend n₃ n₄) ∧
    nsDomMod (nsAppend n₁ n₂) = nsDomMod (nsAppend n₃ n₄) := by
  exact ⟨nsDom_append_preserved n₁ n₂ n₃ n₄ premises.1 premises.2.1 premises.2.2.1,
    nsDomMod_append_preserved n₁ n₂ n₃ n₄ premises.2.2.1 premises.2.2.2⟩

/-- Flapjack infrastructure for the HOL proofs: pointwise lookup
correspondence is preserved when leading namespace domains agree. -/
theorem nsLookup_append_transfer {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (first' second' : Namespace M N W)
    (firstDomain : nsDom first = nsDom first') (firstModules : nsDomMod first = nsDomMod first')
    (id : Ident M N) (value : W) (rel : W → V → Prop)
    (firstRelated : ∀ v, nsLookup first' id = some v →
      ∃ w, nsLookup first id = some w ∧ rel v w)
    (secondRelated : ∀ v, nsLookup second' id = some v →
      ∃ w, nsLookup second id = some w ∧ rel v w)
    (sourceLookup : nsLookup (nsAppend first' second') id = some value) :
    ∃ w, nsLookup (nsAppend first second) id = some w ∧ rel value w := by
  cases id with
  | short name =>
    rw [nsLookup_append_short] at sourceLookup ⊢
    cases src : nsLookup first' (.short name) with
    | some v =>
      simp [src] at sourceLookup
      subst v
      obtain ⟨w, lookup, related⟩ := firstRelated value src
      exact ⟨w, by simp [lookup], related⟩
    | none =>
      have firstNone : nsLookup first (.short name) = none := by
        have h := congrFun firstDomain (.short name)
        change (∃ v, nsLookup first (.short name) = some v) =
          (∃ v, nsLookup first' (.short name) = some v) at h
        cases found : nsLookup first (.short name) <;> simp_all
      have sourceSecond : nsLookup second' (.short name) = some value := by simpa [src] using sourceLookup
      obtain ⟨w, lookup, related⟩ := secondRelated value sourceSecond
      exact ⟨w, by simp [firstNone, lookup], related⟩
  | long moduleName rest =>
    rw [nsLookup_append_long] at sourceLookup ⊢
    have modules := congrFun firstModules [moduleName]
    change (∃ v, nsLookupMod first [moduleName] = some v) =
      (∃ v, nsLookupMod first' [moduleName] = some v) at modules
    cases srcModule : nsLookupMod first' [moduleName] with
    | none =>
      have firstNone : nsLookupMod first [moduleName] = none := by
        cases found : nsLookupMod first [moduleName] <;> simp_all
      have sourceSecond : nsLookup second' (.long moduleName rest) = some value := by
        simpa [srcModule] using sourceLookup
      obtain ⟨w, lookup, related⟩ := secondRelated value sourceSecond
      exact ⟨w, by simp [firstNone, lookup], related⟩
    | some sourceModule =>
      have firstSome : ∃ targetModule, nsLookupMod first [moduleName] = some targetModule := by
        cases found : nsLookupMod first [moduleName] <;> simp_all
      obtain ⟨targetModule, targetLookup⟩ := firstSome
      have sourceFirst : nsLookup first' (.long moduleName rest) = some value := by
        simpa [srcModule] using sourceLookup
      obtain ⟨w, lookup, related⟩ := firstRelated value sourceFirst
      exact ⟨w, by simp [targetLookup, lookup], related⟩

end Flapjack.NamespaceHOL
