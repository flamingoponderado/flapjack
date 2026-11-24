module

public import Flapjack.NamespaceProps.Bind
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! Original namespace-domain characterizations. -/
namespace Flapjack.NamespaceHOL

/-- Membership in the value domain is exactly a successful lookup. HOL states the
membership as `x ∈ nsDom n`; the Lean set carrier is the membership predicate. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsDom"]
theorem nsLookup_nsDom {M N V : Type} [DecidableEq M] [DecidableEq N]
    (x : Ident M N) (n : Namespace M N V) :
    nsDom n x ↔ ∃ v, nsLookup n x = some v :=
  Iff.rfl

/-- An association-list namespace has only the empty module path in its module domain. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_alist_to_ns"]
theorem nsDomMod_alistToNs {M N V : Type} [DecidableEq M] (l : Alist N V) :
    nsDomMod (alistToNs l) = ({[]} : Set (List M)) := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (alistToNs l) path = some v) ↔ path = []
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn rest => simp [alistToNs, nsLookupMod, List.lookup]

end Flapjack.NamespaceHOL
