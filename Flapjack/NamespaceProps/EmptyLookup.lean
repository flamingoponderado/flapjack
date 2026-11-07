import Flapjack.NamespaceHOL

/-! Lookup in the empty namespace. -/
namespace Flapjack.NamespaceHOL

/-- No identifier is bound in the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsEmpty"]
theorem nsLookup_nsEmpty {M N V : Type} [DecidableEq M] [DecidableEq N] (id : Ident M N) :
    nsLookup (nsEmpty : Namespace M N V) id = none := by
  cases id <;> rfl

/-- No nonempty module path is bound in the empty namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_nsEmpty"]
theorem nsLookupMod_nsEmpty {M N V : Type} [DecidableEq M] (name : M) (path : List M) :
    nsLookupMod (nsEmpty : Namespace M N V) (name :: path) = none := rfl

end Flapjack.NamespaceHOL
