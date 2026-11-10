module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate

@[expose] public section

/-! Pure expression evaluation for the direct-call proof. -/
namespace Flapjack.Compiler.Backend.ClosCall.PureCorrectPort
open ClosSem Flapjack.SemanticPrimitivesHOL ClosProps

/-- Closure states use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- A pure singleton evaluation preserves the state and returns one value,
or terminates with a type error. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "pure_correct_eq"
  (fmap_as_finite_support := [refs, code])]
theorem pureCorrectEq {C F : Type} (e : ClosLang.Exp) (env : List ClosSem.Value) (s : State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s2 : State C F)
    (h : ClosLang.pure e = true ∧ evaluate [e] env s = (res, s2)) :
    match (generalizing := false) res with
    | .val vs => s2 = s ∧ vs.length = 1
    | .err (.raise _) => False
    | .err (.abort a) => a = .typeError := by
  have p := everyPureCorrect [e] env s (by simpa using h.1)
  rw [h.2] at p
  cases res with
  | val vs => simpa using p
  | err error => cases error <;> simp_all

end Flapjack.Compiler.Backend.ClosCall.PureCorrectPort
