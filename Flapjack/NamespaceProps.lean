module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Properties of the original namespace operations. -/
namespace Flapjack.NamespaceHOL

/-- The empty namespace is a two-sided identity for append. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_nsEmpty"]
theorem nsAppend_nsEmpty {M N V : Type} (env : Namespace M N V) :
    nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  cases env
  simp [nsAppend, nsEmpty]

/-- Namespace append is associative. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_assoc"]
theorem nsAppend_assoc {M N V : Type} (e1 e2 e3 : Namespace M N V) :
    nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  cases e1
  cases e2
  cases e3
  simp [nsAppend, List.append_assoc]

/-- Appending an association-list namespace is the same as binding that list. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAppend_to_nsBindList"]
theorem nsAppend_to_nsBindList {M N V : Type} (env : Namespace M N V) :
    ∀ bindings : List (N × V), nsAppend (alistToNs bindings) env = nsBindList bindings env := by
  intro bindings
  symm
  cases env with
  | bind values modules =>
    induction bindings with
    | nil => rfl
    | cons p rest ih =>
      simp only [nsBindList, List.foldr_cons] at ih ⊢
      rw [ih]
      cases p
      rfl

/-- Looking up a new binding finds it, and other identifiers are unchanged. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsLookup_nsBind"]
theorem nsLookup_nsBind :
    (∀ {M N V : Type} [DecidableEq M] [DecidableEq N]
      (n : N) (v : V) (e : Namespace M N V), nsLookup (nsBind n v e) (.short n) = some v) ∧
    (∀ {M N V : Type} [DecidableEq M] [DecidableEq N]
      (n : Ident M N) (n' : N) (v : V) (e : Namespace M N V),
      n ≠ .short n' → nsLookup (nsBind n' v e) n = nsLookup e n) := by
  constructor
  · intro M N V instM instN n v e
    cases e
    simp [nsLookup, nsBind]
  · intro M N V instM instN n n' v e different
    cases e
    cases n with
    | short name =>
      have ne : name ≠ n' := by simpa using different
      simp [nsLookup, nsBind, List.lookup, BEq.beq, ne]
    | long moduleName id => rfl

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
