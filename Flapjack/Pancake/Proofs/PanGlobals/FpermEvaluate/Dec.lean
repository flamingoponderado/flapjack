import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermDecSupport
/-- Representation infrastructure: the canonical state roundtrip has no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermDecSupport

/-- Original evaluate_fperm Dec case with its literal guarded body IH at the
source locals update. Initializer and shape failures remain total error runs. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Dec {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width)
    (body : ProgHOL width) (state : PanSemStateFiniteExact width σ)
    (ih : ∀ value : ValueHOL width,
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some value ∧
        shape = shapeOfHOLExact value →
      ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
        evaluateHOLFiniteState { state with locals := state.locals.update (name,value) } body =
          (res, post) →
        evaluateHOLFiniteState
          { { state with locals := state.locals.update (name,value) } with
            code := fpermCodeHOL f g state.code } (fpermHOL f g body) =
          (res, { post with code := fpermCodeHOL f g post.code }))
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.dec name shape initializer body) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.dec name shape initializer body)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  rw [evaluateHOLFiniteState_dec_total] at heval
  rw [fpermHOL, evaluateHOLFiniteState_dec_total]
  dsimp only at heval ⊢
  have hcode := @evalHOLFinite_upd_code_eq width σ _ state
    (fun address => Classical.propDecidable (state.memaddrs address))
    (fpermCodeHOL f g state.code) initializer
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases hc : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer with
  | none =>
      simp only [hc] at heval ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
      rfl
  | some value =>
      simp only [hc] at heval ⊢
      by_cases hs : shapeEqHOL shape (shapeOfHOLExact value) = true
      · simp only [hs, if_true, setVarHOLFinite] at heval ⊢
        cases hb : evaluateHOLFiniteState
            { state with locals := state.locals.update (name,value) } body with
        | mk r1 s1 =>
            rw [hb] at heval
            have ht := ih value ⟨hc, (shapeEqHOL_eq_true _ _).mp hs⟩ r1 s1 hb
            rw [ht]
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
            rfl
      · simp only [hs] at heval ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heval
        rfl

end Flapjack
