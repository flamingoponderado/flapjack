module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Original laws relating binding and association-list namespaces. -/
namespace Flapjack.NamespaceHOL

/-- Building from a consed association list binds the head. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alist_to_ns_cons"]
theorem alistToNs_cons {M N V : Type} (k : N) (v : V) (l : Alist N V) :
    (alistToNs ((k, v) :: l) : Namespace M N V) = nsBind k v (alistToNs l) :=
  rfl

/-- Appending a bound namespace binds the entry in the appended namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_nsBind"]
theorem nsAppend_nsBind {M N V : Type} (k : N) (v : V) (e1 e2 : Namespace M N V) :
    nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  cases e1 with | bind v1 m1 =>
  cases e2 with | bind v2 m2 =>
  simp [nsBind, nsAppend]

/-- Appending two association-list namespaces concatenates the lists. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_alist_to_ns"]
theorem nsAppend_alistToNs {M N V : Type} (al1 al2 : Alist N V) :
    (nsAppend (alistToNs al1) (alistToNs al2) : Namespace M N V) = alistToNs (al1 ++ al2) :=
  rfl

/-- Binding is injective in the name, the value and the namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsBind_11"]
theorem nsBind_eq_iff {M N V : Type} (x : N) (y : V) (n : Namespace M N V)
    (x' : N) (y' : V) (n' : Namespace M N V) :
    nsBind x y n = nsBind x' y' n' ↔ x = x' ∧ y = y' ∧ n = n' := by
  cases n with | bind vs ms =>
  cases n' with | bind vs' ms' =>
  simp [nsBind, and_assoc]

/-- Looking up a nonempty module path in an association-list namespace fails. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookupMod_alist_to_ns"]
theorem nsLookupMod_alistToNs {M N V : Type} [DecidableEq M] (l : Alist N V)
    (mn : M) (rest : List M) :
    nsLookupMod (alistToNs l) (mn :: rest) = (none : Option (Namespace M N V)) := by
  simp [alistToNs, nsLookupMod, List.lookup]

/-- Building a namespace from an association list is injective. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "alist_to_ns_11"]
theorem alistToNs_eq_iff {M N V : Type} (l1 l2 : Alist N V) :
    (alistToNs l1 : Namespace M N V) = alistToNs l2 ↔ l1 = l2 := by
  simp [alistToNs]

/-- Looking up in a bare association-list namespace succeeds exactly at a short name
whose entry is found by association-list lookup. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_Bind_v_some"]
theorem nsLookup_bind_alist {M N V : Type} [DecidableEq M] [DecidableEq N]
    (v : Alist N V) (k : Ident M N) (x : V) :
    nsLookup (.bind v []) k = some x ↔ ∃ y, k = .short y ∧ v.lookup y = some x := by
  cases k with
  | short name => simp [nsLookup]
  | long mn rest => simp [nsLookup, List.lookup]

end Flapjack.NamespaceHOL
