module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup through a right fold of module lifting. -/
namespace Flapjack.NamespaceHOL

/-- Folding lifts along a module path keeps the innermost short-name lookup. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_FOLDR_nsLift"]
theorem nsLookup_foldr_nsLift {M N V : Type} [DecidableEq M] [DecidableEq N]
    (e : Namespace M N V) (p : List M) (k : N) :
    nsLookup (p.foldr nsLift e) (mkId p k) = nsLookup e (.short k) := by
  induction p with
  | nil => rfl
  | cons mn p ih => simp [mkId, nsLift, nsLookup, ih]

end Flapjack.NamespaceHOL
