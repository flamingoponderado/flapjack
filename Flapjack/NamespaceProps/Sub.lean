module

public import Flapjack.NamespaceProps

@[expose] public section

/-! Original laws for namespace sub-relations. -/
namespace Flapjack.NamespaceHOL

/-- A conjunctive relation relates exactly when both relations do. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_conj"]
theorem nsSub_conj {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (P Q : Ident M N → V → W → Prop) (e1 : Namespace M N V) (e2 : Namespace M N W) :
    nsSub (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  unfold nsSub
  constructor
  · intro both
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro id v1 found
      obtain ⟨v2, found', related⟩ := both.1 id v1 found
      exact ⟨v2, found', related.1⟩
    · intro path absent
      exact both.2 path absent
    · intro id v1 found
      obtain ⟨v2, found', related⟩ := both.1 id v1 found
      exact ⟨v2, found', related.2⟩
    · intro path absent
      exact both.2 path absent
  · intro conj
    refine ⟨?_, ?_⟩
    · intro id v1 found
      obtain ⟨v2, found', related⟩ := conj.1.1 id v1 found
      obtain ⟨v2', found'', related'⟩ := conj.2.1 id v1 found
      rw [found'] at found''
      obtain rfl := Option.some.inj found''
      exact ⟨v2, found', related, related'⟩
    · intro path absent
      exact conj.1.2 path absent

/-- A pointwise implication makes every namespace a sub-namespace of itself. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_refl"]
theorem nsSub_refl {M N V : Type} [DecidableEq M] [DecidableEq N]
    (P : Ident M N → V → Prop) (R : Ident M N → V → V → Prop)
    (step : ∀ n x, P n x → R n x x) (e : Namespace M N V) (all : nsAll P e) :
    nsSub R e e := by
  constructor
  · intro id v1 found
    exact ⟨v1, found, step id v1 (all id v1 found)⟩
  · intro path absent
    exact absent

/-- Binding related entries into related namespaces keeps them related. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsSub_nsBind"]
theorem nsSub_nsBind {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (x : N) (v1 : V) (v2 : W)
    (e1 : Namespace M N V) (e2 : Namespace M N W)
    (premise : R (.short x) v1 v2 ∧ nsSub R e1 e2) :
    nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  obtain ⟨head, sub⟩ := premise
  constructor
  · intro id value found
    by_cases bound : id = .short x
    · subst bound
      rw [nsLookup_nsBind.1] at found
      obtain rfl := Option.some.inj found.symm
      exact ⟨v2, nsLookup_nsBind.1 x v2 e2, head⟩
    · rw [nsLookup_nsBind.2 id x v1 e1 bound] at found
      obtain ⟨other, found', related⟩ := sub.1 id value found
      have shifted : nsLookup (nsBind x v2 e2) id = some other := by
        rw [nsLookup_nsBind.2 id x v2 e2 bound]
        exact found'
      exact ⟨other, shifted, related⟩
  · intro path absent
    cases path with
    | nil => simp [nsLookupMod] at absent
    | cons mn rest =>
      cases e1 with | bind vs ms =>
      cases e2 with | bind vs' ms' =>
      simp only [nsBind, nsLookupMod] at absent ⊢
      exact sub.2 (mn :: rest) absent

/-- A conjunctive relation relates two namespaces exactly when both relations do. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_conj"]
theorem nsAll2_conj {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (P Q : Ident M N → V → W → Prop) (e1 : Namespace M N V) (e2 : Namespace M N W) :
    nsAll2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  unfold nsAll2
  rw [nsSub_conj, nsSub_conj]
  constructor
  · intro both
    exact ⟨⟨both.1.1, both.2.1⟩, ⟨both.1.2, both.2.2⟩⟩
  · intro conj
    exact ⟨⟨conj.1.1, conj.2.1⟩, ⟨conj.1.2, conj.2.2⟩⟩

/-- Binding related entries into related namespaces keeps them two-way related. -/
@[hol "cakeml/semantics/proofs/namespacePropsScript.sml" "nsAll2_nsBind"]
theorem nsAll2_nsBind {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (R : Ident M N → V → W → Prop) (x : N) (v1 : V) (v2 : W)
    (e1 : Namespace M N V) (e2 : Namespace M N W)
    (premise : R (.short x) v1 v2 ∧ nsAll2 R e1 e2) :
    nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  obtain ⟨head, both⟩ := premise
  exact ⟨nsSub_nsBind R x v1 v2 e1 e2 ⟨head, both.1⟩,
    nsSub_nsBind (fun id left right => R id right left) x v2 v1 e2 e1 ⟨head, both.2⟩⟩

end Flapjack.NamespaceHOL
