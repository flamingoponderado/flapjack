module

public import Flapjack.NamespaceProps

@[expose] public section

/-! Quantification over namespaces built from association lists. -/
namespace Flapjack.NamespaceHOL

noncomputable local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

/-- If every association satisfies a predicate, so does its namespace. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_alist_to_ns"]
theorem nsAllAlistToNs {M N V : Type}
    (R : Ident M N → V → Prop) (l : List (N × V)) :
    (∀ entry ∈ l, R (.short entry.1) entry.2) → nsAll R (alistToNs l) := by
  intro all id v found
  cases id with
  | long mod rest => simp [alistToNs, nsLookup] at found
  | short name =>
    simp only [alistToNs, nsLookup] at found
    induction l with
    | nil => simp at found
    | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · subst key
        simp [List.lookup] at found
        subst v
        exact all (name, value) (by simp)
      · have ne : (name == key) = false := by simp [same]
        simp [List.lookup, ne] at found
        apply ih (by intro entry member; exact all entry (by simp [member])) found

end Flapjack.NamespaceHOL
