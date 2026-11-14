module

public import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterCons

@[expose] public section

/-! Assembly of the interpreter simulation over the proof-side evaluator.
The evaluator and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Every list member has strictly smaller weight than its containing list. -/
theorem expression_weight_lt_list_weight (expressions : List ClosLang.Exp)
    (expression : ClosLang.Exp) (member : expression ∈ expressions) :
    ClosSem.expWeight expression < ClosSem.expsWeight expressions := by
  induction expressions with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    simp only [ClosSem.expsWeight]
    rcases member with rfl | member
    · omega
    · have smaller := ih member
      omega

/-- The interpreter simulates both expressions and expression lists. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "clos_interpreter_correct"
  (fmap_as_finite_support := [refs, code])]
theorem interpreter_correct {C F : Type} :
    (∀ (expression : ClosLang.Exp) (env : List ClosSem.Value)
      (source target : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
      (sourceFinal : ClosSem.State C F),
      ClosSem.evaluate [expression] env source = (result, sourceFinal) ∧ canInterpret expression = true ∧
      InterpAssum C F source.clock ∧ StateRel source target ∧ result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstant expression), .block 0 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal) ∧
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
      (source target : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
      (sourceFinal : ClosSem.State C F),
      ClosSem.evaluate expressions env source = (result, sourceFinal) ∧ canInterpretList expressions = true ∧
      InterpAssum C F source.clock ∧ StateRel source target ∧ result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal targetResult,
        ClosSem.evaluate [closInterpreterBody]
          [ClosSem.makeConst (toConstantList expressions), .block 1 [], ClosSem.listToValue env]
          { target with clock := extra + target.clock } = (targetResult, targetFinal) ∧
        StateRel sourceFinal targetFinal ∧
        (match result with
         | .val values => targetResult = .val [ClosSem.listToValue values]
         | .err _ => result = targetResult)) := by
  have all : ∀ weight, ∀ expression : ClosLang.Exp, ClosSem.expWeight expression = weight →
      ∀ (env : List ClosSem.Value) (source target sourceFinal : ClosSem.State C F)
        (result : Result (List ClosSem.Value) ClosSem.Value),
        ClosSem.evaluate [expression] env source = (result, sourceFinal) → canInterpret expression = true →
        InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
        ∃ extra targetFinal,
          ClosSem.evaluate [closInterpreterBody]
            [ClosSem.makeConst (toConstant expression), .block 0 [], ClosSem.listToValue env]
            { target with clock := extra + target.clock } = (result, targetFinal) ∧
          StateRel sourceFinal targetFinal := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight weightIH =>
      intro expression measure env source target sourceFinal result run valid assumption related notTypeError
      have ih (child : ClosLang.Exp) (smaller : ClosSem.expWeight child < weight) :=
        weightIH (ClosSem.expWeight child) smaller child rfl
      cases expression with
      | var trace index =>
        exact interpreter_correct_variable trace index env source target sourceFinal result run valid assumption related notTypeError
      | ifThenElse trace condition yes no =>
        apply interpreter_correct_if trace condition yes no ?_ ?_ ?_ env source target sourceFinal result run valid assumption related notTypeError
        · exact ih condition (by simp only [ClosSem.expWeight] at measure; omega)
        · exact ih yes (by simp only [ClosSem.expWeight] at measure; omega)
        · exact ih no (by simp only [ClosSem.expWeight] at measure; omega)
      | «let» trace bindings body =>
        apply interpreter_correct_let trace bindings body ?_ ?_ env source target sourceFinal result run valid assumption related notTypeError
        · intro listEnv listSource listTarget listFinal listResult listRun listValid listAssumption listRelated listNotTypeError
          cases listResult <;>
            apply interpreter_correct_list_of_members bindings ?_ listEnv listSource listTarget listFinal _
              listRun listValid listAssumption listRelated listNotTypeError <;>
            intro child member <;>
            have memberWeight := expression_weight_lt_list_weight bindings child member <;>
            exact ih child (by simp only [ClosSem.expWeight] at measure; omega)
        · exact ih body (by simp only [ClosSem.expWeight] at measure; omega)
      | raise trace body =>
        exact interpreter_correct_raise trace body (ih body (by simp only [ClosSem.expWeight] at measure; omega))
          env source target sourceFinal result run valid assumption related notTypeError
      | handle trace body handler =>
        apply interpreter_correct_handle trace body handler ?_ ?_ env source target sourceFinal result run valid assumption related notTypeError
        · exact ih body (by simp only [ClosSem.expWeight] at measure; omega)
        · exact ih handler (by simp only [ClosSem.expWeight] at measure; omega)
      | tick trace body =>
        exact interpreter_correct_tick trace body (ih body (by simp only [ClosSem.expWeight] at measure; omega))
          env source target sourceFinal result run valid assumption related notTypeError
      | app trace location function args =>
        apply interpreter_correct_app trace location function args ?_ ?_ env source target sourceFinal result run valid assumption related notTypeError
        · intro child member
          have memberWeight := expression_weight_lt_list_weight args child member
          exact ih child (by simp only [ClosSem.expWeight] at measure; omega)
        · exact ih function (by simp only [ClosSem.expWeight] at measure; omega)
      | op trace op args =>
        apply interpreter_correct_op trace op args ?_ env source target sourceFinal result run valid assumption related notTypeError
        intro listEnv listSource listTarget listFinal listResult listRun listValid listAssumption listRelated listNotTypeError
        cases listResult <;>
          apply interpreter_correct_list_of_members args ?_ listEnv listSource listTarget listFinal _
            listRun listValid listAssumption listRelated listNotTypeError <;>
          intro child member <;>
          have memberWeight := expression_weight_lt_list_weight args child member <;>
          have parentWeight := ClosSem.opWeight_gt trace op args <;>
          exact ih child (by omega)
      | call | fn | letrec => simp [canInterpret] at valid
  constructor
  · intro expression env source target result sourceFinal sourceRun
    exact all (ClosSem.expWeight expression) expression rfl env source target sourceFinal result
      sourceRun.1 sourceRun.2.1 sourceRun.2.2.1 sourceRun.2.2.2.1 sourceRun.2.2.2.2
  · intro expressions env source target result sourceFinal sourceRun
    obtain ⟨run, valid, assumption, related, notTypeError⟩ := sourceRun
    obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
      interpreter_correct_list_of_members expressions
        (fun expression _ => all (ClosSem.expWeight expression) expression rfl)
        env source target sourceFinal result run valid assumption related notTypeError
    cases result with
    | err error => exact ⟨extra, targetFinal, .err error, targetRun, finalRel, rfl⟩
    | val values => exact ⟨extra, targetFinal, .val [ClosSem.listToValue values], targetRun, finalRel, rfl⟩

namespace OptInterpPort
/-- The closure state uses the canonical finite-support map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end OptInterpPort

/-- A selected interpreter replacement simulates its source expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "opt_interp_thm"
  (fmap_as_finite_support := [refs, code])]
theorem optInterp_correct {C F : Type} (expression replacement : ClosLang.Exp)
    (source : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (sourceFinal target : ClosSem.State C F)
    (sourceRun : optInterp expression = some replacement ∧ InterpAssum C F source.clock ∧
      ClosSem.evaluate [expression] [] source = (result, sourceFinal) ∧ StateRel source target ∧
      result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [replacement] [] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  obtain ⟨selected, assumption, run, related, notTypeError⟩ := sourceRun
  have valid : canInterpret expression = true := by
    cases h : canInterpret expression <;> simp [optInterp, h] at selected ⊢
  obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
    interpreter_correct.1 expression [] source target result sourceFinal ⟨run, valid, assumption, related, notTypeError⟩
  let enlarged := { target with clock := 3 + (extra + target.clock) }
  have enlargedRel : StateRel { source with clock := enlarged.clock } enlarged :=
    stateRel_withClock related enlarged.clock
  have enough : 3 ≤ enlarged.clock := by simp [enlarged]
  have clocks : ClosSem.decClock 3 enlarged = { target with clock := extra + target.clock } := by
    simp [ClosSem.decClock, enlarged]
  have reduction : ClosSem.evaluate [replacement] [] enlarged =
      ClosSem.evaluate [closInterpreterBody]
        [ClosSem.makeConst (toConstant expression), .block 0 [], .block 0 []]
        (ClosSem.decClock 3 enlarged) := by
    unfold optInterp at selected
    split at selected
    · simp only [Option.some.injEq] at selected
      subst replacement
      exact evaluate_interpreter_call { source with clock := enlarged.clock } enlarged enlargedRel []
        (.op .none (.blockOp (.cons 0)) []) (.op .none (.blockOp (.cons 0)) [])
        (.op .none (.blockOp (.constant (toConstant expression))) [])
        (.block 0 []) (.block 0 []) (ClosSem.makeConst (toConstant expression))
        (evaluate_cons_nil .none 0 [] enlarged) (evaluate_cons_nil .none 0 [] enlarged)
        (evaluate_constant .none (toConstant expression) [] enlarged) enough
    · contradiction
  rw [clocks] at reduction
  have targetRun' : ClosSem.evaluate [closInterpreterBody]
      [ClosSem.makeConst (toConstant expression), .block 0 [], .block 0 []]
      { target with clock := extra + target.clock } = (result, targetFinal) := by
    simpa [ClosSem.listToValue, BackendCommon.nilTag] using targetRun
  rw [targetRun'] at reduction
  refine ⟨3 + extra, targetFinal, ?_, finalRel⟩
  simpa [enlarged, Nat.add_assoc] using reduction

/-- Interpreter replacement with fallback simulates the original expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "opt_interp1_thm'"
  (fmap_as_finite_support := [refs, code])]
theorem optInterp1_correct {C F : Type} (expression : ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (sourceRun : InterpAssum C F source.clock ∧
      ClosSem.evaluate [expression] [] source = (result, sourceFinal) ∧ StateRel source target ∧
      result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [optInterp1 expression] [] { target with clock := target.clock + extra } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  obtain ⟨assumption, run, related, notTypeError⟩ := sourceRun
  unfold optInterp1
  cases selected : optInterp expression with
  | none =>
    simp only [Option.getD_none]
    obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
      assumption.1 [expression] source [] target result sourceFinal ⟨by omega, run, notTypeError⟩ related
    exact ⟨extra, targetFinal, by simpa only [Nat.add_comm] using targetRun, finalRel⟩
  | some replacement =>
    simp only [Option.getD_some]
    obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
      optInterp_correct expression replacement source result sourceFinal target
        ⟨selected, assumption, run, related, notTypeError⟩
    exact ⟨extra, targetFinal, by simpa only [Nat.add_comm] using targetRun, finalRel⟩

end Flapjack.Compiler.Backend.ClosInterp
