import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermIfSupport
/-- Representation infrastructure: the canonical state roundtrip has no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermIfSupport

/-- Literal evaluate_ind If guard for the original evaluate_fperm constructor case.
The IH selects precisely the source branch under a successful word condition. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_If {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (condition : ExpHOL width) (first second : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ih : ∀ (value : ValueHOL width) (lab : HolWordLab width) (word : BitVec width),
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) condition = some value ∧
        value = .val lab ∧ lab = .word word →
      ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        evaluateHOLFiniteState state (if word ≠ 0 then first else second) = (res, post) →
        evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
          (fpermHOL f g (if word ≠ 0 then first else second)) =
          (res, { post with code := fpermCodeHOL f g post.code }))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.ite condition first second) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.ite condition first second)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  rw [evaluateHOLFiniteState_ite] at heval
  rw [fpermHOL, evaluateHOLFiniteState_ite]
  have hcode := @evalHOLFinite_upd_code_eq width σ _ state
    (fun address => Classical.propDecidable (state.memaddrs address))
    (fpermCodeHOL f g state.code) condition
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases hc : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none =>
      simp only [hc] at heval
      have hr := congrArg Prod.fst heval
      have hs := congrArg Prod.snd heval
      cases hr
      cases hs
      rfl
  | some value =>
      cases value with
      | rStruct fields =>
          simp only [hc] at heval
          have hr := congrArg Prod.fst heval
          have hs := congrArg Prod.snd heval
          cases hr
          cases hs
          rfl
      | nStruct name fields =>
          simp only [hc] at heval
          have hr := congrArg Prod.fst heval
          have hs := congrArg Prod.snd heval
          cases hr
          cases hs
          rfl
      | val lab =>
          cases lab with
          | word word =>
              have hh := ih (.val (.word word)) (.word word) word ⟨hc, rfl, rfl⟩ res post
              by_cases hz : word = 0
              · simp only [hc, hz, if_true, ne_eq, not_true_eq_false, if_false] at heval hh ⊢
                exact hh heval
              · simp only [hc, hz, if_false, ne_eq, not_false_eq_true, if_true] at heval hh ⊢
                exact hh heval

end Flapjack
