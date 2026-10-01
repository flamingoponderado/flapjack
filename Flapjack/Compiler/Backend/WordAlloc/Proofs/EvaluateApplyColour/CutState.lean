import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Leaves

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

/-- Flapjack infrastructure lifting the reviewed `cutEnvLemma` to the native
evaluator state. HOL uses this step inside `evaluate_apply_colour_Loop_helper`
for entry and exit cuts; it has no independently named HOL declaration, hence
no tag. Only source cut success is assumed; target success, state equality,
exact domains and the output locals relation are proved. Neither oracle is
constrained and colour injection is scoped to the cut names. -/
theorem cutStateColourTransport {width : Nat} [NeZero width] {C F : Type}
    (n1 n2 : NumSet) (f : Nat → Nat)
    (st cst rst : WordSemStateFiniteExact width C F)
    (hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
      (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b)
    (hs : wordStateEqRel st cst)
    (hl : strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key)
      st.locals cst.locals)
    (hc : cutState (n1, n2) st = some rst) :
    ∃ rcst, cutState (applyNummapsKey f (n1, n2)) cst = some rcst ∧
      wordStateEqRel rst rcst ∧
      sptDomain rst.locals = (fun key => sptDomain n1 key ∨ sptDomain n2 key) ∧
      strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key)
        rst.locals rcst.locals ∧
      sptDomain rcst.locals =
        (fun key => ∃ source, sptDomain rst.locals source ∧ f source = key) := by
  cases he : wordSemCutEnv (n1, n2) st.locals with
  | none => simp [cutState, he] at hc
  | some env =>
    simp only [cutState, he, Option.some.injEq] at hc
    subst rst
    obtain ⟨target, ht, hdomain, hlocals, _, hsource⟩ :=
      cutEnvLemma n1 n2 st.locals cst.locals env f ⟨hinj, he, hl⟩
    refine ⟨{ cst with locals := target }, ?_, ?_, hsource, hlocals, hdomain⟩
    · simp only [cutState, ht]
    · exact wsrLocals env target hs

/-- Local infrastructure composing cut transport with the reviewed
`strongLocalsRelExtendAux`. The exact source-cut domain allows extension to
any body live-before set: absent source bindings make the relation vacuous.
No additional set-inclusion premise is needed; no separate HOL declaration
names this composition, so it is untagged. -/
theorem cutStateColourTransportLive {width : Nat} [NeZero width] {C F : Type}
    (n1 n2 : NumSet) (f : Nat → Nat) (live : Nat → Prop)
    (st cst rst : WordSemStateFiniteExact width C F)
    (hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
      (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b)
    (hs : wordStateEqRel st cst)
    (hl : strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key)
      st.locals cst.locals)
    (hc : cutState (n1, n2) st = some rst) :
    ∃ rcst, cutState (applyNummapsKey f (n1, n2)) cst = some rcst ∧
      wordStateEqRel rst rcst ∧ strongLocalsRel f live rst.locals rcst.locals := by
  obtain ⟨rcst, ht, heq, hd, hr, _⟩ :=
    cutStateColourTransport n1 n2 f st cst rst hinj hs hl hc
  refine ⟨rcst, ht, heq, strongLocalsRelExtendAux f _ live _ _ ⟨?_, hr⟩⟩
  intro key hk
  rwa [hd] at hk

end Flapjack.WordAlloc
