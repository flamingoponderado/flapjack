import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermSeqSupport
/-- Representation infrastructure: the canonical state roundtrip has no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermSeqSupport

/-- Original evaluate_fperm Seq conjunct, with the literal evaluate_ind continuation
IH guarded by the source first run and NONE result, together with the first IH. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Seq {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (first second : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ihSecond : ∀ (r1 : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      (r1, s1) = evaluateHOLFiniteState state first ∧ r1 = none →
      ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        evaluateHOLFiniteState s1 second = (res, post) →
        evaluateHOLFiniteState { s1 with code := fpermCodeHOL f g s1.code }
          (fpermHOL f g second) = (res, { post with code := fpermCodeHOL f g post.code }))
    (ihFirst : ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
      evaluateHOLFiniteState state first = (res, post) →
      evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
        (fpermHOL f g first) = (res, { post with code := fpermCodeHOL f g post.code }))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.seq first second) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.seq first second)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  rw [evaluateHOLFiniteState_seq_line780] at heval
  rw [fpermHOL, evaluateHOLFiniteState_seq_line780]
  cases hfirst : evaluateHOLFiniteState state first with
  | mk r1 s1 =>
      have ht := ihFirst r1 s1 hfirst
      rw [ht]
      cases r1 with
      | none =>
          simp only [hfirst] at heval
          exact ihSecond none s1 ⟨hfirst.symm, rfl⟩ res post heval
      | some result =>
          simp only [hfirst] at heval
          have hr := congrArg Prod.fst heval
          have hs := congrArg Prod.snd heval
          cases hr
          cases hs
          rfl

end Flapjack
