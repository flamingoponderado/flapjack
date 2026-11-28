module

public import Flapjack.SemanticsProps.Implements
public import Flapjack.SemanticsProps.Determinism

@[expose] public section

/-! Short independent refinement facts from `semanticsPropsScript.sml`. -/
namespace Flapjack.SemanticsPropsHOL
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticsHOL Flapjack.AstHOL
open Flapjack.SemanticsProps

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_intro"]
theorem implementsIntroHOL (b : Prop) (x y : HolBehaviour)
    (h : b → x ≠ .fail → y = x) (hb : b) :
    implementsHOL (fun result => result = y) (fun result => result = x) := by
  intro hxFail result hresult
  subst hresult
  exact Or.inl (h hb (fun hx => hxFail hx.symm))

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_trivial_intro"]
theorem implementsTrivialIntroHOL (x y : HolBehaviour) (h : y = x) :
    implementsHOL (fun result => result = y) (fun result => result = x) := by
  subst h
  intro _ result hresult
  subst hresult
  exact Or.inl rfl

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_intro_ext"]
theorem implementsIntroExtHOL (b : Prop) (x y : HolBehaviour)
    (h : b → x ≠ .fail → extendWithResourceLimitHOL (fun result => result = x) y)
    (hb : b) :
    implementsHOL (fun result => result = y) (fun result => result = x) := by
  intro hxFail result hresult
  subst hresult
  exact h hb (fun hx => hxFail hx.symm)

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit'_SUBSET"]
theorem extendWithResourceLimitPrimeSubsetHOL (precise : Bool) (behaviours : BehaviourSetHOL) :
    ∀ result, extendWithResourceLimitPrimeHOL precise behaviours result →
      extendWithResourceLimitHOL behaviours result := by
  intro result hresult
  cases precise with
  | true => exact Or.inl hresult
  | false => exact hresult

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_strengthen"]
theorem implementsPrimeStrengthenHOL (compiled source : BehaviourSetHOL) (b b' : Bool)
    (h : (b' = true → b = true) ∧ implementsPrimeHOL b compiled source) :
    implementsPrimeHOL b' compiled source := by
  rcases h with ⟨himp, hprime⟩
  intro hsourceFail result hresult
  cases b with
  | true =>
    cases b' with
    | true => exact hprime hsourceFail result hresult
    | false => exact Or.inl (hprime hsourceFail result hresult)
  | false =>
    cases b' with
    | false => exact hprime hsourceFail result hresult
    | true => exact absurd (himp rfl) (by decide)

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_IMP_implements"]
theorem implementsPrimeImpImplementsHOL (compiled source : BehaviourSetHOL) (b : Bool)
    (h : implementsPrimeHOL b compiled source) : implementsHOL compiled source := by
  intro hsourceFail result hresult
  cases b with
  | true => exact Or.inl (h hsourceFail result hresult)
  | false => exact h hsourceFail result hresult

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "semantics_prog_Terminate_not_Fail"]
theorem semanticsProg_terminate_not_fail {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (outcome : HolOutcome) (events : List HolIoEvent)
    (h : semanticsProg st env prog (.terminate outcome events)) :
    ¬ semanticsProg st env prog .fail ∧
      semanticsProg st env prog = (fun behaviour => behaviour = .terminate outcome events) := by
  constructor
  · intro hfail
    have := semanticsProg_deterministic st env prog .fail (.terminate outcome events) ⟨hfail, h⟩
    cases this
  · funext behaviour
    apply propext
    constructor
    · intro hb
      exact semanticsProg_deterministic st env prog behaviour (.terminate outcome events) ⟨hb, h⟩
    · intro hb
      rw [hb]
      exact h

@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "semantics_prog_Diverge_not_Fail"]
theorem semanticsProg_diverge_not_fail {σ : Type} (st : State σ) (env : SemEnv Value)
    (prog : List Dec) (trace : HolLList HolIoEvent)
    (h : semanticsProg st env prog (.diverge trace)) :
    ¬ semanticsProg st env prog .fail ∧
      semanticsProg st env prog = (fun behaviour => behaviour = .diverge trace) := by
  constructor
  · intro hfail
    have := semanticsProg_deterministic st env prog .fail (.diverge trace) ⟨hfail, h⟩
    cases this
  · funext behaviour
    apply propext
    constructor
    · intro hb
      exact semanticsProg_deterministic st env prog behaviour (.diverge trace) ⟨hb, h⟩
    · intro hb
      rw [hb]
      exact h

end Flapjack.SemanticsPropsHOL
