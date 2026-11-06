import Flapjack.NamespaceHOL

/-! Properties of the original namespace operations. -/
namespace Flapjack.NamespaceHOL

section

noncomputable local instance (α : Type) : DecidableEq α := Classical.typeDecidableEq α

/-- Appending namespaces preserves a predicate that holds in each one. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_nsAppend"]
theorem nsAll_nsAppend {M N V : Type} (f : Ident M N → V → Prop)
    (e1 e2 : Namespace M N V) (premises : nsAll f e1 ∧ nsAll f e2) :
    nsAll f (nsAppend e1 e2) := by
  intro id value found
  cases e1 with
  | bind vs1 ms1 =>
    cases e2 with
    | bind vs2 ms2 =>
      cases id with
      | short name =>
        cases h : vs1.lookup name with
        | none =>
          apply premises.2 (.short name) value
          simpa [nsAppend, nsLookup, List.lookup_append, h] using found
        | some v =>
          apply premises.1 (.short name) value
          simpa [nsAppend, nsLookup, List.lookup_append, h] using found
      | long name rest =>
        cases h : ms1.lookup name with
        | none =>
          apply premises.2 (.long name rest) value
          simpa [nsAppend, nsLookup, List.lookup_append, h] using found
        | some env =>
          apply premises.1 (.long name rest) value
          simpa [nsAppend, nsLookup, List.lookup_append, h] using found

end

end Flapjack.NamespaceHOL
