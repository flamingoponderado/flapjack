import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! ShMemStore case of pan_globalsProofScript's evaluate_fperm.
Expression evaluation, domain checks and FFI calls are independent of code.
Every original failure, returning FFI and final FFI branch is retained.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermShMemStoreSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermShMemStoreSupport

/-- Original evaluate_fperm ShMemStore case, with the sole source-run premise
and complete result/post-code equality. No success or target-run assumption. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_ShMemStore {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (address value : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state (.shMemStore operator address value : ProgHOL width) =
      (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.shMemStore operator address value : ProgHOL width)) =
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
  rw [fpermHOL, evaluateHOLFiniteState_shMemStore_total]
  rw [evaluateHOLFiniteState_shMemStore_total] at heval
  rw [point address, point value]
  cases ha : @evalHOLExact width σ _ state.toExact
      (fun key => Classical.propDecidable (state.memaddrs key)) address with
  | none =>
      simp only [ha] at heval ⊢
      cases heval
      rfl
  | some av =>
      cases av with
      | rStruct _ | nStruct _ _ =>
          simp only [ha] at heval ⊢
          cases heval
          rfl
      | val aw =>
          cases aw with
          | word addr =>
              cases hv : @evalHOLExact width σ _ state.toExact
                  (fun key => Classical.propDecidable (state.memaddrs key)) value with
              | none =>
                  simp only [ha, hv] at heval ⊢
                  cases heval
                  rfl
              | some vv =>
                  cases vv with
                  | rStruct _ | nStruct _ _ =>
                      simp only [ha, hv] at heval ⊢
                      cases heval
                      rfl
                  | val vw =>
                      cases vw with
                      | word bytes =>
                          simp only [ha, hv] at heval ⊢
                          unfold shMemStoreHOLExact at heval ⊢
                          by_cases hn : nbOpHOL operator = 0
                          · simp only [hn, if_true] at heval ⊢
                            by_cases hd : state.shMemaddrs addr
                            · simp only [hd, if_true] at heval ⊢
                              obtain ⟨outcome, hf⟩ : ∃ outcome, callFFIHOL state.ffi
                                  (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
                                  (panWordToBytesHOL bytes false ++ panWordToBytesHOL addr false) =
                                    outcome := ⟨_, rfl⟩
                              cases outcome <;> simp only [hf] at heval ⊢ <;>
                                cases heval <;> cases state <;> rfl
                            · simp only [hd, if_false] at heval ⊢
                              cases heval
                              cases state
                              rfl
                          · simp only [hn, if_false] at heval ⊢
                            by_cases hd : state.shMemaddrs (panByteAlignHOL addr)
                            · simp only [hd, if_true] at heval ⊢
                              obtain ⟨outcome, hf⟩ : ∃ outcome, callFFIHOL state.ffi
                                  (.sharedMem .mappedWrite) [BitVec.ofNat 8 (nbOpHOL operator)]
                                  ((panWordToBytesHOL bytes false).take (nbOpHOL operator) ++
                                    panWordToBytesHOL addr false) = outcome := ⟨_, rfl⟩
                              cases outcome <;> simp only [hf] at heval ⊢ <;>
                                cases heval <;> cases state <;> rfl
                            · simp only [hd, if_false] at heval ⊢
                              cases heval
                              cases state
                              rfl

  all_goals simp

end Flapjack
