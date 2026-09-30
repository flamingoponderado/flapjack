import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.Leaves
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace Flapjack
open Pancake.PanLang PanSemStateFiniteExact

namespace FpermWhileSupport
/-- Representation infrastructure: the canonical state roundtrip has no separate HOL original. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness
end FpermWhileSupport

/-- Flapjack spelling of the original evaluate_fperm induction motive;
this is statement infrastructure, with no independent HOL original. -/
def fpermEvaluateGoal {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (program : ProgHOL width) (state : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ),
    evaluateHOLFiniteState state program = (res,post) →
    evaluateHOLFiniteState { state with code := fpermCodeHOL f g state.code }
      (fpermHOL f g program) = (res,{ post with code := fpermCodeHOL f g post.code })

/-- Original While case with the three literal evaluate_ind guarded IHs,
including both distinct backedges and the body at the decremented clock. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_fperm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateFperm_While {width : Nat} {σ : Type} [NeZero width]
    (f g : MlS) (condition : ExpHOL width) (body : ProgHOL width)
    (state : PanSemStateFiniteExact width σ)
    (ihContinue : ∀ (v2 : ValueHOL width) (lab : HolWordLab width) (word : BitVec width)
      (r1 : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
      (result : PanSemResultExact width),
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
      v2 = .val lab ∧ lab = .word word ∧ word ≠ 0 ∧ state.clock ≠ 0 ∧
      (r1,s1) = evaluateHOLFiniteState state.decClockHOLFinite body ∧
      r1 = some result ∧ result = .continue →
      fpermEvaluateGoal f g (.while condition body) s1)
    (ihNone : ∀ (v2 : ValueHOL width) (lab : HolWordLab width) (word : BitVec width)
      (r1 : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ),
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
      v2 = .val lab ∧ lab = .word word ∧ word ≠ 0 ∧ state.clock ≠ 0 ∧
      (r1,s1) = evaluateHOLFiniteState state.decClockHOLFinite body ∧ r1 = none →
      fpermEvaluateGoal f g (.while condition body) s1)
    (ihBody : ∀ (v2 : ValueHOL width) (lab : HolWordLab width) (word : BitVec width),
      @evalHOLExact width σ _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
      v2 = .val lab ∧ lab = .word word ∧ word ≠ 0 ∧ state.clock ≠ 0 →
      fpermEvaluateGoal f g body state.decClockHOLFinite) :
    fpermEvaluateGoal f g (.while condition body) state := by
  classical
  intro res post heval
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at heval
  rw [fpermHOL, evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [evalHOLFinite] at heval ⊢
  have hcode := @evalHOLFinite_upd_code_eq width σ _ state
    (fun address => Classical.propDecidable (state.memaddrs address))
    (fpermCodeHOL f g state.code) condition
  simp only [evalHOLFinite] at hcode
  rw [hcode]
  cases hc : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none =>
      simp only [hc] at heval ⊢
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
      rfl
  | some value =>
      cases value with
      | rStruct fields =>
          simp only [hc] at heval ⊢
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
          rfl
      | nStruct name fields =>
          simp only [hc] at heval ⊢
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
          rfl
      | val lab =>
          cases lab with
          | word word =>
              simp only [hc] at heval ⊢
              by_cases hw : word ≠ 0
              · simp only [hw,if_true,ne_eq,not_false_eq_true] at heval ⊢
                by_cases hz : state.clock = 0
                · simp only [hz,if_true] at heval ⊢
                  obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
                  simp only [emptyLocalsHOLFinite,hz]
                · simp only [hz,if_false] at heval ⊢
                  cases hb : evaluateHOLFiniteState state.decClockHOLFinite body with
                  | mk r1 s1 =>
                      simp only [hb] at heval
                      have ht := ihBody (.val (.word word)) (.word word) word
                        ⟨hc,rfl,rfl,hw,hz⟩ r1 s1 hb
                      have ht' : evaluateHOLFiniteState
                          ({ state with code := fpermCodeHOL f g state.code }).decClockHOLFinite
                          (fpermHOL f g body) =
                          (r1,{ s1 with code := fpermCodeHOL f g s1.code }) := by
                        simpa only [decClockHOLFinite] using ht
                      rw [ht']
                      cases r1 with
                      | none =>
                          simpa only [fpermHOL] using ihNone (.val (.word word)) (.word word) word none s1
                            ⟨hc,rfl,rfl,hw,hz,hb.symm,rfl⟩ res post heval
                      | some result =>
                          cases result with
                          | «continue» =>
                              simpa only [fpermHOL] using ihContinue (.val (.word word)) (.word word) word
                                (some .continue) s1 .continue
                                ⟨hc,rfl,rfl,hw,hz,hb.symm,rfl,rfl⟩ res post heval
                          | «break» =>
                              obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
                              rfl
                          | error | timeOut | returned value | exception eid value | finalFfi event =>
                              obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
                              rfl
              · simp only [hw,if_false] at heval ⊢
                obtain ⟨rfl,rfl⟩ := Prod.mk.inj heval
                rfl

end Flapjack
