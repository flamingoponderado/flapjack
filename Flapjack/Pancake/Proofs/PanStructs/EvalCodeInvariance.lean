module

public import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

@[expose] public section

/-! `pan_structsProofScript.sml:800-804`: the point-free form of HOL
`eval_upd_code_eq`, that evaluating with a replaced code map is the same
function.  HOL states the equation between the two curried evaluators, so the
Lean statement keeps the two functions and closes by extensionality over the
expression. -/

namespace Flapjack.Pancake.Proofs.PanStructs.EvalCodeInvariance

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Flapjack-only canonical state codec witness. HOL has no declaration about
the finite-support carrier's Lean roundtrip. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Exact HOL `eval_upd_code_eq2[local]`
(`pan_structsProofScript.sml:800-804`): `eval (t with code := code) = eval t`,
with the typed capture `eval_upd_code_eq2_typed`
(`pancake_pan_structs_proof_typed_probe.out`).  The evaluator never inspects
`code`, and every other state field is untouched by the update. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "eval_upd_code_eq2"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalHOLFinite_upd_code_eq2 {width : Nat} {σ : Type} [NeZero width]
    (t : PanSemStateFiniteExact width σ)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _
        { t with code := code } (fun address => Classical.propDecidable (t.memaddrs address)) =
      @PanSemStateFiniteExact.evalHOLFinite width σ _
        t (fun address => Classical.propDecidable (t.memaddrs address)) := by
  funext expression
  exact @PanSemStateFiniteExact.evalHOLFinite_upd_code_eq width σ _
    t (fun address => Classical.propDecidable (t.memaddrs address)) code expression

end Flapjack.Pancake.Proofs.PanStructs.EvalCodeInvariance
