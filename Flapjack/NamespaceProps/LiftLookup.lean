module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup equations for module-lifted namespaces. -/
namespace Flapjack.NamespaceHOL

/-- Lookup through a lifted namespace removes its matching leading module. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsLift"]
theorem nsLookup_nsLift {M N V : Type} [DecidableEq M] [DecidableEq N]
    (mn : M) (env : Namespace M N V) (id : Ident M N) :
    nsLookup (nsLift mn env) id =
      match id with
      | .long mn' id' => if mn = mn' then nsLookup env id' else none
      | .short _ => none := by
  cases id with
  | short name => rfl
  | long name rest =>
    by_cases same : mn = name
    · subst name
      simp [nsLookup, nsLift]
    · have different : name ≠ mn := Ne.symm same
      simp [nsLookup, nsLift, List.lookup, BEq.beq, same, different]

/-- Module lookup through a lift returns the lift itself at the empty path. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsLift"]
theorem nsLookupMod_nsLift {M N V : Type} [DecidableEq M]
    (mn : M) (env : Namespace M N V) (path : List M) :
    nsLookupMod (nsLift mn env) path =
      match path with
      | [] => some (nsLift mn env)
      | mn' :: path' => if mn = mn' then nsLookupMod env path' else none := by
  cases path with
  | nil => rfl
  | cons name rest =>
    by_cases same : mn = name
    · subst name
      simp [nsLookupMod, nsLift]
    · have different : name ≠ mn := Ne.symm same
      simp [nsLookupMod, nsLift, List.lookup, BEq.beq, same, different]

@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsLift"]
theorem nsAll_nsLift {M N V : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → Prop) (mn : M) (env : Namespace M N V) :
    nsAll R (nsLift mn env) ↔ nsAll (fun id => R (.long mn id)) env := by
  constructor
  · intro h id value found
    apply h (.long mn id) value
    simpa [nsLookup_nsLift] using found
  · intro h id value found
    cases id with
    | short name => simp [nsLookup_nsLift] at found
    | long moduleName rest =>
      by_cases same : mn = moduleName
      · subst moduleName
        exact h rest value (by simpa [nsLookup_nsLift] using found)
      · simp [nsLookup_nsLift, same] at found

end Flapjack.NamespaceHOL
