import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves

/-! ShMemLoad case of pan_globalsProofScript's evaluate_fperm.
The address evaluation, keyed-variable validity guard, shared-memory read and
its FFI final/return/error outcomes are unchanged by a code-only update; the
non-recursive HOL generic arm needs no sub-program induction premise.
-/
namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact
namespace FpermShMemLoadSupport
/-- Canonical representation infrastructure, not an independently named HOL theorem. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermShMemLoadSupport

/-- The shared-memory read commutes with the `fpermCodeHOL`-permuted code
update: it inspects only the shared-memory domain and the FFI, and every branch
preserves the input `code` field, so the loaded post-state's `code` is permuted
exactly as `evaluate_fperm` requires. Flapjack-specific commutation bridge, not
an independent HOL declaration. -/
theorem shMemLoadHOLFiniteExact_permCode {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    let loaded := @shMemLoadHOLFiniteExact width σ _ state
        (fun current => Classical.propDecidable (state.shMemaddrs current))
        kind name address nb
    @shMemLoadHOLFiniteExact width σ _ { state with code := fpermCodeHOL f g state.code }
        (fun current => Classical.propDecidable (state.shMemaddrs current))
        kind name address nb =
      (loaded.1, { loaded.2 with code := fpermCodeHOL f g loaded.2.code }) := by
  classical
  cases state with
  | mk locals globals structs code0 eshapes memory memaddrs shMemaddrs clock be ffi baseAddr topAddr =>
    dsimp only
    unfold shMemLoadHOLFiniteExact emptyLocalsHOLFinite setKvarFfiHOLFinite
      setKvarHOLFinite setVarHOLFinite setGlobalHOLFinite
    cases hffi : callFFIHOL ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL address false) with
    | final event =>
      by_cases hnb : nb = 0
      · simp only [hnb, if_true]
        by_cases haddr : shMemaddrs address
        · simp only [haddr, if_true]
        · simp only [haddr, if_false]
      · simp only [hnb, if_false]
        by_cases haddr : shMemaddrs (panByteAlignHOL address)
        · simp only [haddr, if_true]
        · simp only [haddr, if_false]
    | ret newFfi newBytes =>
      by_cases hnb : nb = 0
      · simp only [hnb, if_true]
        by_cases haddr : shMemaddrs address
        · simp only [haddr, if_true]
          cases kind <;> rfl
        · simp only [haddr, if_false]
      · simp only [hnb, if_false]
        by_cases haddr : shMemaddrs (panByteAlignHOL address)
        · simp only [haddr, if_true]
          cases kind <;> rfl
        · simp only [haddr, if_false]

set_option backward.isDefEq.respectTransparency false in
/-- Original evaluate_fperm ShMemLoad case. The sole original source-run premise
and full target/post-state equality retain expression failure, the keyed-variable
guard and the shared-memory FFI final/return/error outcomes. The address read and
shared-memory read are unchanged by the code-only update, and the loaded state's
code field is permuted exactly as HOL does. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_ShMemLoad {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (state : PanSemStateFiniteExact width σ)
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (heval : evaluateHOLFiniteState state
      (.shMemLoad operator kind name address : ProgHOL width) = (res, post)) :
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g (.shMemLoad operator kind name address : ProgHOL width)) =
      (res, { post with code := fpermCodeHOL f g post.code }) := by
  classical
  have point (expression : ExpHOL width) : @evalHOLFinite width σ _
      ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ)
      (fun current => Classical.propDecidable (state.memaddrs current)) expression =
      @evalHOLFinite width σ _ state
      (fun current => Classical.propDecidable (state.memaddrs current)) expression :=
    congrFun (@evalHOL_upd_code_eta width σ _ state
      (fun current => Classical.propDecidable (state.memaddrs current))
      (fpermCodeHOL f g state.code)) expression
  have hlookup :
      lookupKvarHOLFinite kind name
        ({ state with code := fpermCodeHOL f g state.code } : PanSemStateFiniteExact width σ) =
      lookupKvarHOLFinite kind name state := by
    cases kind <;> rfl
  rw [fpermHOL]
  · rw [evaluateHOLFiniteState_shMemLoad_source] at heval ⊢
    rw [point, hlookup]
    cases hv : @evalHOLFinite width σ _ state
        (fun current => Classical.propDecidable (state.memaddrs current)) address with
    | none =>
        simp only [hv] at heval ⊢
        simpa only [Prod.fst, Prod.snd] using congrArg
          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
    | some value =>
        cases value with
        | val payload =>
            cases payload with
            | word addr =>
                simp only [hv] at heval ⊢
                cases hk : lookupKvarHOLFinite kind name state with
                | none =>
                    simp only [hk] at heval ⊢
                    simpa only [Prod.fst, Prod.snd] using congrArg
                      (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                        (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
                | some kvalue =>
                    cases kvalue with
                    | val kpayload =>
                        cases kpayload with
                        | word _ =>
                            simp only [hk] at heval ⊢
                            rw [shMemLoadHOLFiniteExact_permCode f g state kind name addr
                              (nbOpHOL operator)]
                            simpa only [Prod.fst, Prod.snd] using congrArg
                              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
                    | rStruct fields =>
                        simp only [hk] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
                    | nStruct kname fields =>
                        simp only [hk] at heval ⊢
                        simpa only [Prod.fst, Prod.snd] using congrArg
                          (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                            (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        | rStruct fields =>
            simp only [hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
        | nStruct valueName fields =>
            simp only [hv] at heval ⊢
            simpa only [Prod.fst, Prod.snd] using congrArg
              (fun (run : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) =>
                (run.1, { run.2 with code := fpermCodeHOL f g run.2.code })) heval
  all_goals simp

end Flapjack
