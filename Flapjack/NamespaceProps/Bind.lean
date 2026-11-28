module

public import Flapjack.NamespaceHOL
public import Flapjack.NamespaceProps

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

/-- An optional binding preserves a namespace-wide predicate when its entry
satisfies it. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsOptBind"]
theorem nsAll_nsOptBind {M N V : Type} [DecidableEq M] [DecidableEq N]
    (P : Ident M N → V → Prop)
    (x : Option N) (v : V) (e : Namespace M N V)
    (premise : (x = none ∨ ∃ n, x = some n ∧ P (.short n) v) ∧ nsAll P e) :
    nsAll P (nsOptBind x v e) := by
  obtain ⟨head, all⟩ := premise
  cases x with
  | none =>
    intro id value found
    simpa [nsOptBind] using all id value found
  | some n =>
    have rel : P (.short n) v := by
      rcases head with h | ⟨n', same, rel⟩
      · simp at h
      · simp only [Option.some.injEq] at same
        subst same
        exact rel
    change nsAll P (nsBind n v e)
    intro id value found
    by_cases sameId : id = .short n
    · rw [sameId] at found ⊢
      change nsLookup (nsBind n v e) (.short n) = some value at found
      rw [nsLookup_nsBind.1 n v e] at found
      simp at found
      rw [← found]
      exact rel
    · change nsLookup (nsBind n v e) id = some value at found
      rw [nsLookup_nsBind.2 id n v e sameId] at found
      exact all id value found

end Flapjack.NamespaceHOL
