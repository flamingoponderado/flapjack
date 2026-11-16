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

private theorem nsSubLift {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (mn : M)
    (e1 : Namespace M N V) (e2 : Namespace M N W) :
    nsSub R (nsLift mn e1) (nsLift mn e2) ↔
      nsSub (fun id => R (.long mn id)) e1 e2 := by
  constructor
  · rintro ⟨look, modules⟩
    constructor
    · intro id value found
      simpa [nsLookup_nsLift] using look (.long mn id) value (by simpa [nsLookup_nsLift] using found)
    · intro path absent
      simpa [nsLookupMod_nsLift] using modules (mn :: path) (by simpa [nsLookupMod_nsLift] using absent)
  · rintro ⟨look, modules⟩
    constructor
    · intro id value found
      cases id with
      | short name => simp [nsLookup_nsLift] at found
      | long name rest =>
        by_cases same : mn = name
        · subst name
          simpa [nsLookup_nsLift] using look rest value (by simpa [nsLookup_nsLift] using found)
        · simp [nsLookup_nsLift, same] at found
    · intro path absent
      cases path with
      | nil => simp [nsLookupMod_nsLift] at absent
      | cons name rest =>
        by_cases same : mn = name
        · subst name
          simpa [nsLookupMod_nsLift] using modules rest (by simpa [nsLookupMod_nsLift] using absent)
        · simp [nsLookupMod_nsLift, same]

/-- Lifting related namespaces prepends the module name in the relation. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_nsLift"]
theorem nsAll2_nsLift {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (mn : M)
    (e1 : Namespace M N V) (e2 : Namespace M N W) :
    nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔
      nsAll2 (fun id => R (.long mn id)) e1 e2 := by
  simp only [nsAll2, nsSubLift]

end Flapjack.NamespaceHOL
