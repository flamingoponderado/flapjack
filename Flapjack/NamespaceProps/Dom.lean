module

public import Flapjack.NamespaceProps
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert

@[expose] public section

/-! Original namespace-domain characterizations. -/
namespace Flapjack.NamespaceHOL

/-- The value domain of a bound namespace inserts the short name. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDom_nsBind"]
theorem nsDom_nsBind {M N V : Type} [DecidableEq M] [DecidableEq N]
    (x : N) (y : V) (n : Namespace M N V) :
    nsDom (nsBind x y n) = Set.insert (.short x) (nsDom n) := by
  funext id
  apply propext
  change (∃ v, nsLookup (nsBind x y n) id = some v) ↔
    (id = .short x ∨ ∃ v, nsLookup n id = some v)
  cases id with
  | short name =>
    by_cases same : name = x
    · subst x
      rw [nsLookup_nsBind.1]
      simp
    · have ne : (Ident.short name : Ident M N) ≠ .short x := by simpa using same
      rw [nsLookup_nsBind.2 _ x y n ne]
      simp [ne]
  | long mn rest =>
    have ne : (Ident.long mn rest : Ident M N) ≠ .short x := by simp
    rw [nsLookup_nsBind.2 _ x y n ne]
    simp [ne]

/-- Binding does not change the module domain. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsDomMod_nsBind"]
theorem nsDomMod_nsBind {M N V : Type} [DecidableEq M]
    (x : N) (y : V) (n : Namespace M N V) :
    nsDomMod (nsBind x y n) = nsDomMod n := by
  funext path
  apply propext
  change (∃ v, nsLookupMod (nsBind x y n) path = some v) ↔
    (∃ v, nsLookupMod n path = some v)
  cases n with | bind vs ms =>
  cases path with
  | nil => simp [nsBind, nsLookupMod]
  | cons mn rest => simp [nsBind, nsLookupMod]

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
  | cons mn rest => simp [alistToNs, nsLookupMod]

end Flapjack.NamespaceHOL
