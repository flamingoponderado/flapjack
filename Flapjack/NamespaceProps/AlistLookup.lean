module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Lookup through an association-list namespace. -/
namespace Flapjack.NamespaceHOL

/-- A successful lookup in an association-list namespace is exactly a
successful first-match lookup at the short name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_alist_to_ns_some"]
theorem nsLookup_alistToNs_some {M N V : Type} [DecidableEq M] [DecidableEq N]
    (l : Alist N V) (id : Ident M N) (v : V) :
    nsLookup (alistToNs l) id = some v ↔ ∃ x', id = .short x' ∧ l.lookup x' = some v := by
  cases id with
  | short name => simp [alistToNs, nsLookup]
  | long mn rest => simp [alistToNs, nsLookup]

/-- A failed lookup in an association-list namespace is exactly a failed
first-match lookup at every short name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_alist_to_ns_none"]
theorem nsLookup_alistToNs_none {M N V : Type} [DecidableEq M] [DecidableEq N]
    (l : Alist N V) (id : Ident M N) :
    nsLookup (alistToNs l) id = none ↔ ∀ x', id = .short x' → l.lookup x' = none := by
  cases id with
  | short name => simp [alistToNs, nsLookup]
  | long mn rest => simp [alistToNs, nsLookup]

end Flapjack.NamespaceHOL
