import Flapjack.NamespaceHOL

/-! Namespace-lifting infrastructure shared by frontend simulation proofs. -/
namespace Flapjack.NamespaceHOL

/-- Flapjack infrastructure: lifting namespaces with equal value domains
preserves domain equality, as needed by the frontend HOL proofs. -/
theorem nsDom_lift_eq {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (mn : M) (left : Namespace M N V) (right : Namespace M N W)
    (domain : nsDom left = nsDom right) : nsDom (nsLift mn left) = nsDom (nsLift mn right) := by
  funext id
  apply propext
  cases id with
  | short name => simp [nsDom, nsLift, nsLookup]
  | long head rest =>
    by_cases same : head = mn
    · subst head
      exact iff_of_eq (by simpa [nsDom, nsLift, nsLookup] using congrFun domain rest)
    · simp [nsDom, nsLift, nsLookup, List.lookup, BEq.beq, same]

/-- Flapjack infrastructure: lifting namespaces with equal module domains
preserves module-domain equality, as needed by the frontend HOL proofs. -/
theorem nsDomMod_lift_eq {M N V W : Type} [DecidableEq M]
    (mn : M) (left : Namespace M N V) (right : Namespace M N W)
    (domain : nsDomMod left = nsDomMod right) :
    nsDomMod (nsLift mn left) = nsDomMod (nsLift mn right) := by
  funext path
  apply propext
  cases path with
  | nil => simp [nsDomMod, nsLookupMod]
  | cons head rest =>
    by_cases same : head = mn
    · subst head
      exact iff_of_eq (by simpa [nsDomMod, nsLift, nsLookupMod] using congrFun domain rest)
    · simp [nsDomMod, nsLift, nsLookupMod, List.lookup, BEq.beq, same]

end Flapjack.NamespaceHOL
