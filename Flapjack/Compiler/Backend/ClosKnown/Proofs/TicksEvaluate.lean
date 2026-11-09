module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.AppExact

@[expose] public section


/-! Evaluation of the tick sequence emitted by closure inlining. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TicksEvaluate
open ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The inserted ticks consume exactly their count, or time out with a zero
clock before evaluating the body. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "evaluate_mk_Ticks_rw"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateTicksRw {C F : Type} (trace : BackendCommon.Tra) (index n : Nat)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (s : State C F) :
    evaluate [ticks trace index n body] env s =
      if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
      else evaluate [body] env (decClock n s) := by
  induction n generalizing index body s with
  | zero => simp [ticks, decClock]
  | succ n ih =>
    rw [ticks, ih]
    by_cases less : s.clock < n
    · have lessSucc : s.clock < n + 1 := by omega
      simp [less, lessSucc]
    · have enough : n ≤ s.clock := by omega
      by_cases equal : s.clock = n
      · have lessSucc : s.clock < n + 1 := by omega
        have decZero : decClock n s = { s with clock := 0 } := by simp [decClock, equal]
        simp [less, lessSucc, evaluate, decZero]
      · have enoughSucc : ¬ s.clock < n + 1 := by omega
        have nonzero : (decClock n s).clock ≠ 0 := by simp [decClock]; omega
        have decEq : decClock 1 (decClock n s) = decClock (n + 1) s := by
          simp [decClock, Nat.sub_sub]
        simp [less, enoughSucc, evaluate, nonzero, decEq]

/-- The inliner's ticks have exactly the observable behavior of an exact
annotated closure application, including timeouts. This is Flapjack proof
infrastructure for the inlining branch. -/
theorem exactApplicationEqTicks {C F : Type} (trace : BackendCommon.Tra)
    (index loc : Nat) (args captured : List ClosSem.Value) (body : ClosLang.Exp)
    (s : State C F) (nonempty : args ≠ []) :
    evaluateApp (some loc) (.closure (some loc) [] captured args.length body) args s =
      evaluate [ticks trace index args.length body] (args ++ captured) s := by
  rw [Relations.AppExact.evaluateAppExactRw args captured args.length loc body s ⟨nonempty, rfl⟩,
    evaluateTicksRw]

end Flapjack.Compiler.Backend.ClosKnown.TicksEvaluate
