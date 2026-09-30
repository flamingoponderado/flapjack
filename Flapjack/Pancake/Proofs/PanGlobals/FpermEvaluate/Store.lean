import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! Store case of pan_globalsProofScript's evaluate_fperm.
Both operand evaluations and memory stores are unchanged by code updates.
Non-word addresses and expression/memory failures remain explicit.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermStoreSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermStoreSupport

/-- Original evaluate_fperm Store case, retaining the sole source-run premise
and complete target/post-state equality. Both expressions, the word-address
guard, memory domain/failure and successful memory update follow HOL. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_Store {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (destination source : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.store destination source : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.store destination source : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLExact width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ).toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression =
      @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address))
      (fpermCodeHOL f g state.code)) expression
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_store] at heval ⊢
    rw [point destination]
    cases hd : @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) destination with
    | none =>
        simp only [hd] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some destinationValue =>
        cases destinationValue with
        | val payload =>
            cases payload with
            | word address =>
                simp only [hd] at heval ⊢
                rw [point source]
                cases hs : @evalHOLExact width σ _ state.toExact
                    (fun address => Classical.propDecidable (state.memaddrs address)) source with
                | none =>
                    simp only [hs] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
                | some value =>
                    simp only [hs] at heval ⊢
                    cases hm : @panMemStoresHOL width _ address (flattenHOL value) state.memaddrs
                        (fun address => Classical.propDecidable (state.memaddrs address)) state.memory with
                    | none =>
                        simp only [hm] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
                    | some memory =>
                        simp only [hm] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        | rStruct _ | nStruct _ _ =>
            simp only [hd] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

end Flapjack
