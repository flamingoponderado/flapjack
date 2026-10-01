import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvs
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnv

namespace Flapjack.WordAlloc

/-- Exact HOL cut_env_lemma (word_allocProofScript.sml:340-378): one global
scoped injection on the union name-set domains, a successful source `cut_env`
and the union-scoped local relation produce a successful renamed target
`cut_env`, the full image domain of the source cut, the union relation on it,
the inherited injection, and the source-cut domain equality. The union argument
is the reviewed `strongLocalsRelRestrictedTreeUnion`; the paired cut is
`cutEnvsLemma`; `cut_env` is `union e2 e1` as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "cut_env_lemma"]
theorem cutEnvLemma {β : Type}
    (n1 n2 : NumSet) (sloc tloc x : Spt β) (f : Nat → Nat)
    (h : (∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) → (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b) ∧
      wordSemCutEnv (n1, n2) sloc = some x ∧
      strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) sloc tloc) :
    ∃ y, wordSemCutEnv (applyNummapsKey f (n1, n2)) tloc = some y ∧
      sptDomain y = (fun key => ∃ source, sptDomain x source ∧ f source = key) ∧
      strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) x y ∧
      (∀ a b, sptDomain x a → sptDomain x b → f a = f b → a = b) ∧
      sptDomain x = (fun key => sptDomain n1 key ∨ sptDomain n2 key) := by
  rcases h with ⟨hinj, hcut, hrel⟩
  obtain ⟨x1, x2, hcuts, hx⟩ :
      ∃ x1 x2, wordSemCutEnvs (n1, n2) sloc = some (x1, x2) ∧ x = sptUnion x2 x1 := by
    cases hcs : wordSemCutEnvs (n1, n2) sloc with
    | none => simp [wordSemCutEnv, hcs] at hcut
    | some p =>
      obtain ⟨a, b⟩ := p
      simp only [wordSemCutEnv, hcs] at hcut
      exact ⟨a, b, rfl, (Option.some.inj hcut).symm⟩
  have hinj1 : ∀ a b, sptDomain n1 a → sptDomain n1 b → f a = f b → a = b :=
    fun a b ha hb heq => hinj a b (Or.inl ha) (Or.inl hb) heq
  have hinj2 : ∀ a b, sptDomain n2 a → sptDomain n2 b → f a = f b → a = b :=
    fun a b ha hb heq => hinj a b (Or.inr ha) (Or.inr hb) heq
  have hrel1 : strongLocalsRel f (sptDomain n1) sloc tloc :=
    fun n v hn => hrel n v ⟨Or.inl hn.1, hn.2⟩
  have hrel2 : strongLocalsRel f (sptDomain n2) sloc tloc :=
    fun n v hn => hrel n v ⟨Or.inr hn.1, hn.2⟩
  obtain ⟨y1, y2, hy, hdy1, hdy2, hrelx1, hrelx2, hinjx1, hinjx2, hx1, hx2⟩ :=
    cutEnvsLemma n1 n2 sloc tloc x1 x2 f ⟨hinj1, hinj2, hcuts, hrel1, hrel2⟩
  have hxdom : sptDomain x = (fun key => sptDomain n1 key ∨ sptDomain n2 key) := by
    rw [hx, sptDomain_sptUnion, hx1, hx2]
    funext key
    exact propext (Iff.intro Or.symm Or.symm)
  refine ⟨sptUnion y2 y1, ?_, ?_, ?_, ?_, hxdom⟩
  · simp [wordSemCutEnv, hy]
  · rw [sptDomain_sptUnion, hdy1, hdy2, hxdom]
    funext key
    apply propext
    constructor
    · rintro (⟨s, h2, heq⟩ | ⟨s, h1, heq⟩)
      · exact ⟨s, Or.inr h2, heq⟩
      · exact ⟨s, Or.inl h1, heq⟩
    · rintro ⟨s, hs, heq⟩
      rcases hs with h1 | h2
      · exact Or.inr ⟨s, h1, heq⟩
      · exact Or.inl ⟨s, h2, heq⟩
  · rw [hx]
    exact strongLocalsRelRestrictedTreeUnion f (sptDomain n1) (sptDomain n2) x1 x2 y1 y2
      hinj hx1 hx2 hdy2 hrelx1 hrelx2
  · intro a b ha hb heq
    rw [hxdom] at ha hb
    exact hinj a b ha hb heq

end Flapjack.WordAlloc
