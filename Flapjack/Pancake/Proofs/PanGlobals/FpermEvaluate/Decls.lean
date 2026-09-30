import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermDeclsSupport
/-- Imported canonical-state roundtrip infrastructure; no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Lawful native-name Boolean update and HOL equality update coincide.
This proof factoring has no separately named HOL original. -/
private theorem update_eq_updateEq {β : Type} (map : HolFiniteMapExact MlS β)
    (entry : MlS × β) : map.update entry = map.updateEq entry := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases h : key = entry.1
  · subst key
    simp [HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE, FUPDATE_HOL]
  · have hrev : entry.1 ≠ key := Ne.symm h
    simp [HolFiniteMapExact.update, HolFiniteMapExact.updateEq, FUPDATE, FUPDATE_HOL, h, hrev]

/-- The declaration evaluator's function-code update commutes with permutation.
This is derived infrastructure for the source induction, not a separate HOL port. -/
theorem functionUpdate {width : Nat} [NeZero width] (f g : MlS)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL) :
    fpermCodeHOL f g (code.update entry) =
      (fpermCodeHOL f g code).update
        (fpermName f g entry.1, entry.2.1, fpermHOL f g entry.2.2.1, entry.2.2.2) := by
  simpa only [update_eq_updateEq] using fpermCodeHOL_updateEq f g code entry
end FpermDeclsSupport

/-- Original declaration permutation theorem over the canonical evaluator. The source evaluation
is the only premise; successful initializer/function/exception guards are
derived from it during declaration induction. No program simulation is assumed. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsFperm {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ) (declarations : List (DeclHOL width))
    (post : PanSemStateFiniteExact width σ)
    (heval : @evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address)) declarations = some post) :
    @evaluateDeclsHOLFinite width σ _ { state with code := fpermCodeHOL f g state.code }
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermDecsHOL f g declarations) =
      some { post with code := fpermCodeHOL f g post.code } := by
  classical
  induction declarations generalizing state post with
  | nil =>
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at heval
      subst post
      simp only [fpermDecsHOL, evaluateDeclsHOLFinite]
  | cons declaration rest ih =>
    cases declaration with
    | name name fields =>
      simpa only [fpermDecsHOL, evaluateDeclsHOLFinite] using ih state post heval
    | decl shape name expression =>
      simp only [evaluateDeclsHOLFinite] at heval
      simp only [fpermDecsHOL, evaluateDeclsHOLFinite]
      have he := congrFun (@evalHOL_upd_code_eta width σ _ (emptyLocalsHOLFinite state)
        (fun address => Classical.propDecidable (state.memaddrs address))
        (fpermCodeHOL f g state.code)) expression
      simp only [emptyLocalsHOLFinite, setGlobalHOLFinite] at he heval ⊢
      with_unfolding_all rw [he]
      simp only [evalHOLFinite, toExact] at heval ⊢
      cases hv : @evalHOLFinite width σ _ (emptyLocalsHOLFinite state)
          (fun address => Classical.propDecidable (state.memaddrs address)) expression with
      | none =>
        simp only [evalHOLFinite, toExact, emptyLocalsHOLFinite] at hv
        simp only [hv] at heval
        cases heval
      | some value =>
        simp only [evalHOLFinite, toExact, emptyLocalsHOLFinite] at hv
        simp only [hv] at heval ⊢
        by_cases hs : shapeEqHOL shape (shapeOfHOLExact value) = true
        · simp only [hs, if_true] at heval ⊢
          exact ih (setGlobalHOLFinite name value state) post heval
        · simp [hs] at heval
    | function declaration =>
      simp only [evaluateDeclsHOLFinite] at heval
      simp only [fpermDecsHOL, evaluateDeclsHOLFinite]
      by_cases hc : (declaration.params.all
          (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
          isWfShapeExactHOL state.structs declaration.returnShape) = true
      · simp only [hc, if_true] at heval ⊢
        have hh := ih { state with code := state.code.update (declaration.name,
            (declaration.params, declaration.body, declaration.returnShape)) } post heval
        simpa only [FpermDeclsSupport.functionUpdate] using hh
      · simp [hc] at heval
    | exnDecl name shape =>
      simp only [evaluateDeclsHOLFinite] at heval
      simp only [fpermDecsHOL, evaluateDeclsHOLFinite]
      by_cases hc : ((state.eshapes.lookup name).isNone && isWfShapeExactHOL state.structs shape) = true
      · simp only [hc, if_true] at heval ⊢
        exact ih { state with eshapes := state.eshapes.update (name, shape) } post heval
      · simp [hc] at heval

end Flapjack
