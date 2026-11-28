module

public import Flapjack.NamespaceProps.Sub
public import Flapjack.NamespaceProps.Empty
public import Batteries.Data.List.Basic

@[expose] public section

/-! Two-way namespace relations for association lists and binding lists. -/
namespace Flapjack.NamespaceHOL

/-- Pointwise related association lists build two-way related namespaces. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_alist_to_ns"]
theorem nsAll2_alistToNs {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (l1 : Alist N V) (l2 : Alist N W)
    (related : List.Forall₂ (fun p q => p.1 = q.1 ∧ R (.short p.1) p.2 q.2) l1 l2) :
    nsAll2 R (alistToNs l1) (alistToNs l2) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simpa [alistToNs, nsEmpty] using nsAll2_nsEmpty (r := R) (V := V) (W := W)
    | cons entry rest => cases related
  | cons entry l1 ih =>
    cases l2 with
    | nil => cases related
    | cons entry' l2 =>
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      obtain ⟨k, v⟩ := entry
      obtain ⟨k', v'⟩ := entry'
      obtain ⟨sameKey, rel⟩ := head
      subst sameKey
      simpa [alistToNs, nsBind] using nsAll2_nsBind R k v v' (alistToNs l1) (alistToNs l2)
        ⟨rel, ih l2 tail⟩

/-- Pointwise related binding lists keep two-way related namespaces related. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_nsBindList"]
theorem nsAll2_nsBindList {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (l1 : Alist N V) (l2 : Alist N W)
    (e1 : Namespace M N V) (e2 : Namespace M N W)
    (premise : List.Forall₂ (fun p q => p.1 = q.1 ∧ R (.short p.1) p.2 q.2) l1 l2 ∧
      nsAll2 R e1 e2) :
    nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  obtain ⟨related, both⟩ := premise
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simpa [nsBindList] using both
    | cons entry rest => cases related
  | cons entry l1 ih =>
    cases l2 with
    | nil => cases related
    | cons entry' l2 =>
      obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
      obtain ⟨k, v⟩ := entry
      obtain ⟨k', v'⟩ := entry'
      obtain ⟨sameKey, rel⟩ := head
      subst sameKey
      simpa [nsBindList, nsBind] using nsAll2_nsBind R k v v' (nsBindList l1 e1)
        (nsBindList l2 e2) ⟨rel, ih l2 tail⟩

end Flapjack.NamespaceHOL
