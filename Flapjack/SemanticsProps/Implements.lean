import Flapjack.FfiHOL

/-! Literal CakeML behavior refinement for the Lab-to-target correctness chain.
The canonical FfiHOL behavior/outcome/event carriers and HolLList are reviewed
ports; legacy String/Array-backed CakeBehaviour remains separate infrastructure.
-/

namespace Flapjack.SemanticsPropsHOL

/-- Predicate representation of a HOL behavior set, with no separate HOL declaration. -/
abbrev BehaviourSetHOL := HolBehaviour → Prop

/-- HOL finite-list prefix implies lazy-list prefix on the reviewed llist carrier. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "isPREFIX_IMP_LPREFIX"]
theorem isPrefixImpLprefixHOL {α : Type} (xs ys : List α) :
    xs <+: ys → HolLList.lprefix (HolLList.fromList xs) (HolLList.fromList ys) :=
  (HolLList.lprefix_fromList xs ys).mpr

/-- Synthesized prefix composition step; no independent HOL declaration. -/
private theorem listPrefixLprefixTrans {α : Type} {xs ys : List α}
    {trace : HolLList α} (hxy : xs <+: ys)
    (htrace : HolLList.lprefix (HolLList.fromList ys) trace) :
    HolLList.lprefix (HolLList.fromList xs) trace :=
  HolLList.lprefix_trans (isPrefixImpLprefixHOL xs ys hxy) htrace

/-- Membership in HOL `extend_with_resource_limit`: retain existing
    behaviors, allow finite prefixes of terminating traces, and allow finite
    prefixes of divergent traces as resource-limit termination. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit_def"]
def extendWithResourceLimitHOL (behaviours : BehaviourSetHOL)
    (result : HolBehaviour) : Prop :=
  behaviours result ∨
    (∃ events outcome complete,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.terminate outcome complete) ∧
        List.IsPrefix events complete) ∨
    (∃ events trace,
        result = .terminate .resourceLimitHit events ∧
        behaviours (.diverge trace) ∧ HolLList.lprefix (HolLList.fromList events) trace)

/-- The precise flag chooses either the original behavior set or its
    resource-limit extension, matching `extend_with_resource_limit'`. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit'_def"]
def extendWithResourceLimitPrimeHOL (precise : Bool)
    (behaviours : BehaviourSetHOL) : BehaviourSetHOL :=
  if precise then behaviours else extendWithResourceLimitHOL behaviours

/-- Cake's `implements' precise x y`: compiled behavior `x` refines source
    behavior `y`, modulo the resource-limit extension, on the reviewed
    canonical HOL behavior carrier. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_def"]
def implementsPrimeHOL (precise : Bool) (compiled source : BehaviourSetHOL) : Prop :=
  ¬ source .fail → ∀ result, compiled result →
    extendWithResourceLimitPrimeHOL precise source result

private theorem extendNotFail (behaviours : BehaviourSetHOL)
    (result : HolBehaviour) (hresult : extendWithResourceLimitHOL behaviours result)
    (hfail : ¬ behaviours .fail) : result ≠ .fail := by
  rcases hresult with hresult | hresult | hresult
  · intro heq
    subst result
    exact hfail hresult
  · rcases hresult with ⟨events, outcome, complete, heq, _, _⟩
    cases heq <;> simp
  · rcases hresult with ⟨events, trace, heq, _, _⟩
    cases heq <;> simp

/-- Extending behaviors twice adds no new resource-limit observations: list
    prefix and lazy-list prefix are transitive. This is the set-inclusion core
    needed by Cake's `implements'_trans`. -/
private theorem extendWithResourceLimitHOL_idempotent (behaviours : BehaviourSetHOL)
    (result : HolBehaviour)
    (hresult : extendWithResourceLimitHOL
      (extendWithResourceLimitHOL behaviours) result) :
    extendWithResourceLimitHOL behaviours result := by
  rcases hresult with hresult | hresult | hresult
  · exact hresult
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    change extendWithResourceLimitHOL behaviours (.terminate outcome complete) at hcomplete
    rcases hcomplete with hcomplete | hcomplete | hcomplete
    · exact Or.inr (Or.inl ⟨events, outcome, complete, rfl, hcomplete, hpref⟩)
    · rcases hcomplete with ⟨middle, middleOutcome, middleComplete, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inl ⟨events, middleOutcome, middleComplete, rfl, hmiddle,
        List.IsPrefix.trans hpref hmidPrefix⟩)
    · rcases hcomplete with ⟨middle, trace, hmid, hmiddle, hmidPrefix⟩
      cases hmid
      exact Or.inr (Or.inr ⟨events, trace, rfl, hmiddle,
        listPrefixLprefixTrans hpref hmidPrefix⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    change extendWithResourceLimitHOL behaviours (.diverge trace) at htrace
    rcases htrace with htrace | htrace | htrace
    · exact Or.inr (Or.inr ⟨events, trace, rfl, htrace, hpref⟩)
    · rcases htrace with ⟨_, _, _, hdiverge, _⟩
      cases hdiverge
    · rcases htrace with ⟨_, _, hdiverge, _⟩
      cases hdiverge

private theorem extendWithResourceLimitPrimeHOL_idempotent (precise : Bool)
    (behaviours : BehaviourSetHOL) (result : HolBehaviour)
    (hresult : extendWithResourceLimitPrimeHOL precise
      (extendWithResourceLimitPrimeHOL precise behaviours) result) :
    extendWithResourceLimitPrimeHOL precise behaviours result := by
  cases precise with
  | true => exact hresult
  | false => exact extendWithResourceLimitHOL_idempotent behaviours result hresult

private theorem extendWithResourceLimitHOL_mono {left right : BehaviourSetHOL}
    (hsubset : ∀ result, left result → right result) (result : HolBehaviour)
    (hresult : extendWithResourceLimitHOL left result) :
    extendWithResourceLimitHOL right result := by
  rcases hresult with hresult | hresult | hresult
  · exact Or.inl (hsubset result hresult)
  · rcases hresult with ⟨events, outcome, complete, rfl, hcomplete, hpref⟩
    exact Or.inr (Or.inl ⟨events, outcome, complete, rfl,
      hsubset (.terminate outcome complete) hcomplete, hpref⟩)
  · rcases hresult with ⟨events, trace, rfl, htrace, hpref⟩
    exact Or.inr (Or.inr ⟨events, trace, rfl, hsubset (.diverge trace) htrace, hpref⟩)

private theorem extendWithResourceLimitPrimeHOL_mono (precise : Bool)
    {left right : BehaviourSetHOL} (hsubset : ∀ result, left result → right result)
    (result : HolBehaviour)
    (hresult : extendWithResourceLimitPrimeHOL precise left result) :
    extendWithResourceLimitPrimeHOL precise right result := by
  cases precise with
  | false => exact extendWithResourceLimitHOL_mono hsubset result hresult
  | true => exact hsubset result hresult

/-- Full HOL refinement transitivity, with both precise flag cases and the
original conjunction premise. No intermediate non-Fail assumption is added;
it is derived from the source non-Fail guard. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_trans"]
theorem implementsPrimeTransHOL (compiled intermediate source : BehaviourSetHOL)
    (precise : Bool)
    (h : implementsPrimeHOL precise intermediate source ∧
      implementsPrimeHOL precise compiled intermediate) :
    implementsPrimeHOL precise compiled source := by
  rcases h with ⟨hintermediate, hcompiled⟩
  intro hsourceFail result hresult
  have hintermediateSubset := hintermediate hsourceFail
  have hintermediateFail : ¬ intermediate .fail := by
    intro hfail
    have hfailExtended : extendWithResourceLimitPrimeHOL precise source .fail :=
      hintermediateSubset .fail hfail
    cases precise with
    | false => exact extendNotFail source .fail hfailExtended hsourceFail rfl
    | true => exact hsourceFail hfailExtended
  have hcompiledSubset := hcompiled hintermediateFail
  have hcompiledExtended := extendWithResourceLimitPrimeHOL_mono precise hintermediateSubset result
    (hcompiledSubset result hresult)
  exact extendWithResourceLimitPrimeHOL_idempotent precise source
    result hcompiledExtended

/-- HOL resource-limit refinement without the precise flag. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_def"]
def implementsHOL (compiled source : BehaviourSetHOL) : Prop :=
  ¬ source .fail → ∀ result, compiled result → extendWithResourceLimitHOL source result

/-- HOL false-flag refinement is exactly the unprimed relation. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements'_F"]
theorem implementsPrimeFalseHOL : implementsPrimeHOL false = implementsHOL := rfl

/-- Full unprimed refinement transitivity, with HOL's two implication premises. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "implements_trans"]
theorem implementsTransHOL (compiled intermediate source : BehaviourSetHOL) :
    implementsHOL intermediate source → implementsHOL compiled intermediate →
      implementsHOL compiled source := by
  intro hi hc
  exact implementsPrimeTransHOL compiled intermediate source false ⟨hi, hc⟩

/-- HOL's conjunction guard excludes failure from resource-limit extension. -/
@[hol "cakeml/semantics/proofs/semanticsPropsScript.sml" "extend_with_resource_limit_not_fail"]
theorem extendWithResourceLimitNotFailHOL (result : HolBehaviour)
    (behaviours : BehaviourSetHOL) :
    extendWithResourceLimitHOL behaviours result ∧ ¬ behaviours .fail → result ≠ .fail := by
  intro h
  exact extendNotFail behaviours result h.1 h.2

end Flapjack.SemanticsPropsHOL
