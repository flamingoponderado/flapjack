module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.Install

@[expose] public section

/-! Source-shaped installation simulation for closure numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem

/-- The adapter preserves the auxiliary part of the input pair. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "ignore_table_imp"]
theorem ignoreTable_imp {S Code S' Code' Aux : Type}
    (f : S → Code → S' × Code') (st : S) (input : Code × Aux)
    (st' : S') (output : Code' × Aux)
    (run : ignoreTable f st input = (st', output)) : output.2 = input.2 := by
  cases input with
  | mk code aux =>
    cases h : f st code with
    | mk nextState nextCode => simpa [ignoreTable, h] using (congrArg (fun p => p.2.2) run).symm

namespace InstallPort
/-- The closure state has the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Numbering simulates both timeout and successful installation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "do_install"
  (fmap_as_finite_support := [refs, code])]
theorem do_install {C F α : Type} (source : State (Nat × C) F) (target : State C F)
    (sourceValues targetValues : List Value)
    (h : StateRel source target ∧ List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues) :
    (∀ (_err : α) final, doInstall sourceValues source = (.err (.abort .timeoutError), final) →
      ∃ targetFinal, doInstall targetValues target = (.err (.abort .timeoutError), targetFinal) ∧
        StateRel final targetFinal) ∧
    (∀ expressions final, doInstall sourceValues source = (.val expressions, final) →
      ∃ targetExpressions targetFinal,
        doInstall targetValues target = (.val targetExpressions, targetFinal) ∧
        ¬ ClosProps.containsAppSome final.maxApp expressions ∧ final.maxApp = source.maxApp ∧
        targetExpressions = (compileInc (source.compileOracle 0).1.1 expressions).2 ∧
        StateRel final targetFinal) := by
  constructor
  · intro _ final run
    obtain ⟨expressions, targetFinal, targetRun, resultEq, _, _, finalRel⟩ :=
      doInstall_related source target sourceValues targetValues _ final h.1 h.2 run (by simp)
    by_cases zero : source.clock = 0
    · exact ⟨targetFinal, by simpa [zero] using targetRun, finalRel⟩
    · simp [zero] at resultEq
  · intro expressions final run
    obtain ⟨out, targetFinal, targetRun, resultEq, safe, maxApp, finalRel⟩ :=
      doInstall_related source target sourceValues targetValues _ final h.1 h.2 run (by simp)
    by_cases zero : source.clock = 0
    · simp [zero] at resultEq
    · simp [zero] at resultEq
      subst out
      refine ⟨_, targetFinal, by simpa [zero] using targetRun, ?_, maxApp, rfl, finalRel⟩
      simpa [maxApp] using safe
end InstallPort
end Flapjack.Compiler.Backend.ClosNumber
