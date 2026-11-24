module

public import Flapjack.NamespaceHOL

@[expose] public section

/-! Original monotonicity laws for namespace relations. -/
namespace Flapjack.NamespaceHOL

/-- A pointwise implication lifts through `nsAll`. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll_mono"]
theorem nsAll_mono {M N V : Type} [DecidableEq M] [DecidableEq N]
    (P Q : Ident M N → V → Prop) (mono : ∀ id x, P id x → Q id x)
    (env : Namespace M N V) (all : nsAll P env) : nsAll Q env := by
  intro id value found
  exact mono id value (all id value found)

end Flapjack.NamespaceHOL
