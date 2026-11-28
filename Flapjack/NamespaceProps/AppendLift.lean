module

public import Flapjack.NamespaceProps.AppendLookup
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Lifted namespaces under appended namespace subsumption. -/
namespace Flapjack.NamespaceHOL

/-- Flapjack infrastructure: a lifted namespace misses every identifier that is
not a long identifier under the lift's module name. -/
private theorem nsLookup_nsLift_none {M N V : Type} [DecidableEq M] [DecidableEq N]
    (mn : M) (env : Namespace M N V) (id : Ident M N)
    (notUnder : ∀ rest, id ≠ .long mn rest) : nsLookup (nsLift mn env) id = none := by
  cases id with
  | short name => rw [nsLookup_nsLift]
  | long mn' rest =>
    rw [nsLookup_nsLift]
    by_cases same : mn = mn'
    · subst same
      exact absurd rfl (notUnder rest)
    · simp [same]

/-- Flapjack infrastructure: a lifted namespace is found at its own module
path. -/
private theorem nsLookupMod_nsLift_self {M N V : Type} [DecidableEq M]
    (mn : M) (env : Namespace M N V) :
    nsLookupMod (nsLift mn env) [mn] = some env := by
  rw [nsLookupMod_nsLift]
  simp [nsLookupMod]

/-- Flapjack infrastructure: a lifted namespace misses every nonempty module
path that prefixes an identifier which is not a long identifier under the
lift's module name. -/
private theorem nsLookupMod_nsLift_none {M N V : Type} [DecidableEq M]
    (mn : M) (env : Namespace M N V) (p1 p2 : List M) (id : Ident M N)
    (ne : p1 ≠ []) (same : idToMods id = p1 ++ p2)
    (notUnder : ∀ rest, id ≠ .long mn rest) : nsLookupMod (nsLift mn env) p1 = none := by
  cases id with
  | short name =>
    simp [idToMods] at same
    obtain ⟨rfl, _⟩ := same
    exact absurd rfl ne
  | long mn' rest' =>
    cases p1 with
    | nil => exact absurd rfl ne
    | cons m rest =>
      simp only [idToMods, List.cons_append, List.cons.injEq] at same
      obtain ⟨headSame, _⟩ := same
      subst headSame
      rw [nsLookupMod_nsLift]
      by_cases sameMn : mn = mn'
      · subst sameMn
        exact absurd rfl (notUnder rest')
      · simp [sameMn]

/-- Appending lifted namespaces preserves the namespace subsumption relation,
with the first namespace related under the lifted identifier. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_nsAppend_lift"]
theorem nsSub_nsAppend_lift {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (mn : M)
    (e1 : Namespace M N V) (e1' : Namespace M N W)
    (e2 : Namespace M N V) (e2' : Namespace M N W)
    (sub : nsSub (fun id => R (.long mn id)) e1 e1' ∧ nsSub R e2 e2') :
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2') := by
  obtain ⟨sub1, sub2⟩ := sub
  constructor
  · intro id v1 found
    rcases (nsLookup_nsAppend_some (nsLift mn e1) id e2 v1).mp found with
      direct | ⟨missLift, foundE2, vacuous⟩
    · cases id with
      | short name =>
        rw [nsLookup_nsLift] at direct
        simp at direct
      | long mn' rest =>
        rw [nsLookup_nsLift] at direct
        by_cases same : mn = mn'
        · subst same
          simp at direct
          obtain ⟨v2, found', rel⟩ := sub1.1 rest v1 direct
          have lifted : nsLookup (nsLift mn e1') (.long mn rest) = some v2 := by
            rw [nsLookup_nsLift]
            simp [found']
          exact ⟨v2, (nsLookup_nsAppend_some (nsLift mn e1') (.long mn rest) e2' v2).mpr
            (Or.inl lifted), rel⟩
        · simp [same] at direct
    · obtain ⟨v2, found', rel⟩ := sub2.1 id v1 foundE2
      have notUnder : ∀ rest, id ≠ .long mn rest := by
        intro rest under
        subst under
        have modNone := vacuous [mn] (idToMods rest) ⟨by simp, rfl⟩
        rw [nsLookupMod_nsLift_self] at modNone
        simp at modNone
      have miss' : nsLookup (nsLift mn e1') id = none :=
        nsLookup_nsLift_none mn e1' id notUnder
      refine ⟨v2, (nsLookup_nsAppend_some (nsLift mn e1') id e2' v2).mpr
        (Or.inr ⟨miss', found', ?_⟩), rel⟩
      intro p1 p2 h
      obtain ⟨ne, same⟩ := h
      exact nsLookupMod_nsLift_none mn e1' p1 p2 id ne same notUnder
  · intro path missing
    cases path with
    | nil =>
      rw [nsLookupMod] at missing
      cases missing
    | cons mn' rest =>
      by_cases same : mn = mn'
      · subst same
        rw [nsLookupMod_append_cons] at missing ⊢
        rw [nsLookupMod_nsLift_self] at missing
        rw [nsLookupMod_nsLift_self]
        simp at missing ⊢
        rw [nsLookupMod_nsLift] at missing ⊢
        simp at missing ⊢
        exact sub1.2 rest missing
      · rw [nsLookupMod_append_cons] at missing ⊢
        have inner' : nsLookupMod (nsLift mn e1') [mn'] = none := by
          rw [nsLookupMod_nsLift]
          simp [same]
        have inner : nsLookupMod (nsLift mn e1) [mn'] = none := by
          rw [nsLookupMod_nsLift]
          simp [same]
        rw [inner'] at missing
        rw [inner]
        simp at missing ⊢
        exact sub2.2 (mn' :: rest) missing

end Flapjack.NamespaceHOL
