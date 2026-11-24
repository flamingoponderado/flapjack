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

/-- A pointwise implication lifts through `nsSub`. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_mono"]
theorem nsSub_mono {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R1 R2 : Ident M N → V → W → Prop) (mono : ∀ x y z, R1 x y z → R2 x y z)
    (e1 : Namespace M N V) (e2 : Namespace M N W) (sub : nsSub R1 e1 e2) :
    nsSub R2 e1 e2 := by
  constructor
  · intro id v1 found
    obtain ⟨v2, found', related⟩ := sub.1 id v1 found
    exact ⟨v2, found', mono id v1 v2 related⟩
  · intro path absent
    exact sub.2 path absent

/-- A lookup-dependent pointwise implication lifts through `nsSub`. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_mono2"]
theorem nsSub_mono2 {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R1 R2 : Ident M N → V → W → Prop) (e1 : Namespace M N V) (e2 : Namespace M N W)
    (mono : ∀ x y z, nsLookup e1 x = some y ∧ nsLookup e2 x = some z ∧ R1 x y z → R2 x y z)
    (sub : nsSub R1 e1 e2) : nsSub R2 e1 e2 := by
  constructor
  · intro id v1 found
    obtain ⟨v2, found', related⟩ := sub.1 id v1 found
    exact ⟨v2, found', mono id v1 v2 ⟨found, found', related⟩⟩
  · intro path absent
    exact sub.2 path absent

/-- A pointwise implication lifts through `nsAll2`. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_mono"]
theorem nsAll2_mono {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R1 R2 : Ident M N → V → W → Prop) (mono : ∀ x y z, R1 x y z → R2 x y z)
    (e1 : Namespace M N V) (e2 : Namespace M N W) (both : nsAll2 R1 e1 e2) :
    nsAll2 R2 e1 e2 :=
  ⟨nsSub_mono R1 R2 mono e1 e2 both.1,
    nsSub_mono (fun id left right => R1 id right left) (fun id left right => R2 id right left)
      (fun x y z related => mono x z y related) e2 e1 both.2⟩

end Flapjack.NamespaceHOL
