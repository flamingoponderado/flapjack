import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermExtCallSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermExtCallSupport

set_option backward.isDefEq.respectTransparency false in
/-- Original evaluate_fperm ExtCall conjunct. All four expression evaluations,
both byte-array reads, and returning/final FFI outcomes are unchanged by a
code-only update. No successful-call or target-evaluation premise is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_ExtCall {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state
      (.extCall function configuration configurationLength array arrayLength) = (res,post)) :
    evaluateHOLFiniteState {state with code := fpermCodeHOL f g state.code}
      (fpermHOL f g (.extCall function configuration configurationLength array arrayLength)) =
      (res,{post with code := fpermCodeHOL f g post.code}) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermCodeHOL f g state.code)) expression
  have mapped := congrArg
    (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
      (run.1,{run.2 with code := fpermCodeHOL f g run.2.code})) heval
  have hperm : fpermHOL f g (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
      .extCall function configuration configurationLength array arrayLength := by simp [fpermHOL]
  rw [hperm, evaluateHOLFiniteState_extCall_source]
  rw [evaluateHOLFiniteState_extCall_source] at mapped
  simp only [evalHOLFinite] at mapped ⊢
  rw [point configuration,point configurationLength,point array,point arrayLength]
  repeat' split <;> simp_all only []
  all_goals simpa only [emptyLocalsHOLFinite,ofExact] using mapped

end Flapjack
