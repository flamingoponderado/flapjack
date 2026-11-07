import Flapjack.NamespaceProps.LiftDomains

/-! Namespace-lifting infrastructure shared by frontend simulation proofs. -/
namespace Flapjack.NamespaceHOL

/-- Flapjack infrastructure: lifting namespaces with equal value domains
preserves domain equality, as needed by the frontend HOL proofs. -/
theorem nsDom_lift_eq {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (mn : M) (left : Namespace M N V) (right : Namespace M N W)
    (domain : nsDom left = nsDom right) : nsDom (nsLift mn left) = nsDom (nsLift mn right) := by
  rw [nsDom_nsLift, nsDom_nsLift, domain]

/-- Flapjack infrastructure: lifting namespaces with equal module domains
preserves module-domain equality, as needed by the frontend HOL proofs. -/
theorem nsDomMod_lift_eq {M N V W : Type} [DecidableEq M]
    (mn : M) (left : Namespace M N V) (right : Namespace M N W)
    (domain : nsDomMod left = nsDomMod right) :
    nsDomMod (nsLift mn left) = nsDomMod (nsLift mn right) := by
  rw [nsDomMod_nsLift, nsDomMod_nsLift, domain]

end Flapjack.NamespaceHOL
