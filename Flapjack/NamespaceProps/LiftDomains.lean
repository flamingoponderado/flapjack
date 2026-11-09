module

public import Flapjack.NamespaceProps.LiftLookup
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert

@[expose] public section

/-! Original namespace-domain characterizations for module lifting. -/
namespace Flapjack.NamespaceHOL

/-- Lifting adds the same leading module to every value-domain identifier. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsLift"]
theorem nsDom_nsLift {M N V : Type} [DecidableEq M] [DecidableEq N]
    (mn : M) (ns : Namespace M N V) :
    nsDom (nsLift mn ns) = Set.image (Ident.long mn) (nsDom ns) := by
  funext id
  apply propext
  change nsDom (nsLift mn ns) id ↔ ∃ inner, nsDom ns inner ∧ Ident.long mn inner = id
  cases id with
  | short name => simp [nsDom, nsLookup_nsLift]
  | long head rest =>
    by_cases same : head = mn
    · subst head
      simp [nsDom, nsLookup_nsLift]
    · simp [nsDom, nsLookup_nsLift, Ne.symm same]

/-- Lifting adds the empty path and prefixes every module-domain path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsLift"]
theorem nsDomMod_nsLift {M N V : Type} [DecidableEq M]
    (mn : M) (ns : Namespace M N V) :
    nsDomMod (nsLift mn ns) = Set.insert [] (Set.image (List.cons mn) (nsDomMod ns)) := by
  funext path
  apply propext
  change nsDomMod (nsLift mn ns) path ↔ path = [] ∨ ∃ inner, nsDomMod ns inner ∧ mn :: inner = path
  cases path with
  | nil => simp [nsDomMod, nsLookupMod_nsLift]
  | cons head rest =>
    by_cases same : head = mn
    · subst head
      simp [nsDomMod, nsLookupMod_nsLift]
    · simp [nsDomMod, nsLookupMod_nsLift, Ne.symm same]

end Flapjack.NamespaceHOL
