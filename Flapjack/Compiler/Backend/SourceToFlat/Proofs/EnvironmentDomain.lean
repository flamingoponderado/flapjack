import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateDenv

/-! Namespace-domain facts needed by sequential declaration simulation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- A short lookup in an appended namespace chooses the first available
binding. -/
theorem nsLookup_append_short {M N V : Type} [DecidableEq M] [DecidableEq N]
    (first second : Namespace M N V) (name : N) :
    nsLookup (nsAppend first second) (.short name) =
      (nsLookup first (.short name)).orElse (fun _ => nsLookup second (.short name)) := by
  cases first with
  | bind firstValues firstModules =>
    cases second with
    | bind secondValues secondModules =>
      simp [nsAppend, nsLookup, List.lookup_append]

/-- A long lookup uses the first namespace whenever it contains the initial
module, even if the rest of the lookup fails. -/
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

/-- Module lookup in an append has the same first-module shadowing rule. -/
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

/-- Corresponding namespaces retain corresponding value domains after
left-biased append, including module shadowing. -/
theorem nsDom_append_preserved {M N V W : Type} [DecidableEq M] [DecidableEq N]
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

/-- Module domains also agree after left-biased append. -/
theorem nsDomMod_append_preserved {M N V W : Type} [DecidableEq M]
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

/-- Extending compiler and source environments preserves their value,
constructor, and module domains. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_domain_eq_append"]
theorem envDomainEq_append (first second : Environment) (sourceFirst sourceSecond : SemEnv Value)
    (premises : EnvDomainEq first sourceFirst ∧ EnvDomainEq second sourceSecond) :
    EnvDomainEq (extendEnv first second) (extendDecEnv sourceFirst sourceSecond) := by
  obtain ⟨⟨v1, vm1, c1, cm1⟩, ⟨v2, vm2, c2, cm2⟩⟩ := premises
  exact ⟨nsDom_append_preserved _ _ _ _ v1 v2 vm1,
    nsDomMod_append_preserved _ _ _ _ vm1 vm2,
    nsDom_append_preserved _ _ _ _ c1 c2 cm1,
    nsDomMod_append_preserved _ _ _ _ cm1 cm2⟩

end Flapjack.Compiler.Backend.SourceToFlat
