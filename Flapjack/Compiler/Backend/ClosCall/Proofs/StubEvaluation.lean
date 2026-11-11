module

public import Flapjack.Compiler.Backend.ClosCall.Stubs
public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend

@[expose] public section

/-! Evaluation of the variable expressions generated for direct-call stubs. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosSem ClosProps

namespace StubEvaluationPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StubEvaluationPort

/-- Generated variables evaluate to the corresponding environment prefix,
or produce a type error when the environment is too short. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "evaluate_GENLIST_Var_tra"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_variables {C F : Type} (env : List Value) (s : ClosSem.State C F) :
    ∀ (n : Nat) (tr : BackendCommon.Tra) (i : Nat),
    evaluate (variablesSource tr i n) env s =
      if n ≤ env.length then (.val (env.take n), s)
      else (.err (.abort .typeError), s) := by
  intro n
  induction n with
  | zero => simp [variablesSource, evaluate]
  | succ n ih =>
    intro tr i
    rw [variablesSource, evaluateSnoc, ih]
    by_cases h : n < env.length
    · have hn : n ≤ env.length := by omega
      have hs : n + 1 ≤ env.length := by omega
      simp only [hn, hs, ↓reduceIte]
      simp only [evaluate, List.getElem?_eq_getElem h]
      rw [List.take_append_getElem h]
    · have hs : ¬ n + 1 ≤ env.length := by omega
      by_cases hn : n ≤ env.length
      · have eq : n = env.length := by omega
        simp [evaluate, eq]
      · simp [hn, hs]

end Flapjack.Compiler.Backend.ClosCall
