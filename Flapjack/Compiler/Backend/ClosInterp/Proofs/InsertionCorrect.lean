import Flapjack.Compiler.Backend.ClosInterp.Proofs.InterpreterCorrect

/-! Simulation of interpreter insertion for the proof-side evaluator. Its
semantics and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- A singleton simulation composes over mapped expression lists. -/
theorem evaluate_map_simulation {C F : Type} (transform : ClosLang.Exp → ClosLang.Exp)
    (single : ∀ (expression : ClosLang.Exp) (source target sourceFinal : ClosSem.State C F)
      (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [expression] [] source = (result, sourceFinal) →
      InterpAssum C F source.clock → StateRel source target → result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate [transform expression] [] { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (expressions : List ClosLang.Exp) (source target sourceFinal : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate expressions [] source = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (expressions.map transform) [] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  induction expressions generalizing source target sourceFinal result with
  | nil =>
    simp only [ClosSem.evaluate] at run
    cases run
    refine ⟨0, target, ?_, related⟩
    simp [ClosSem.evaluate]
  | cons head tail ih =>
    cases headRun : ClosSem.evaluate [head] [] source with
    | mk headResult sourceMid =>
      cases headResult with
      | err error =>
        have sourceError := ClosProps.evaluate_cons_error head tail [] source sourceMid error headRun
        rw [sourceError] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨extra, targetFinal, targetRun, finalRel⟩ :=
          single head source target sourceMid (.err error) headRun assumption related notTypeError
        refine ⟨extra, targetFinal, ?_, finalRel⟩
        simp only [List.map_cons]
        exact ClosProps.evaluate_cons_error (transform head) (tail.map transform) [] _ targetFinal error targetRun
      | val headValues =>
        obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head [] source sourceMid headValues headRun
        cases tailRun : ClosSem.evaluate tail [] sourceMid with
        | mk tailResult last =>
          have sourceSequence := ClosProps.evaluate_cons_value head tail [] source sourceMid value headRun
          rw [tailRun] at sourceSequence
          have tailNotTypeError : tailResult ≠ .err (.abort .typeError) := by
            intro bad
            subst tailResult
            simp at sourceSequence
            rw [sourceSequence] at run
            simp at run
            exact notTypeError run.1.symm
          obtain ⟨headExtra, targetMid, targetHead, midRel⟩ :=
            single head source target sourceMid (.val [value]) headRun assumption related (by simp)
          have sourceBound : sourceMid.clock ≤ source.clock := by
            have bound := ClosSem.evaluate_clock_le [head] [] source
            simpa [headRun] using bound
          obtain ⟨tailExtra, targetFinal, targetTail, finalRel⟩ :=
            ih sourceMid targetMid last tailResult tailRun (interpAssum_le assumption sourceBound) midRel tailNotTypeError
          have shiftedHead := ClosSem.evaluate_addClock.1 [transform head] []
            { target with clock := headExtra + target.clock } targetMid (.val [value]) tailExtra targetHead (by simp)
          let enlarged := { target with clock := (headExtra + target.clock) + tailExtra }
          let enlargedMid := { targetMid with clock := targetMid.clock + tailExtra }
          have headRun' : ClosSem.evaluate [transform head] [] enlarged = (.val [value], enlargedMid) := by
            simpa [enlarged, enlargedMid] using shiftedHead
          have tailRun' : ClosSem.evaluate (tail.map transform) [] enlargedMid = (tailResult, targetFinal) := by
            simpa [enlargedMid, Nat.add_comm] using targetTail
          have targetSequence := ClosProps.evaluate_cons_value (transform head) (tail.map transform) [] enlarged enlargedMid value headRun'
          rw [tailRun'] at targetSequence
          rw [sourceSequence] at run
          cases tailResult with
          | err error =>
            simp at run targetSequence
            rcases run with ⟨rfl, rfl⟩
            refine ⟨headExtra + tailExtra, targetFinal, ?_, finalRel⟩
            simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetSequence
          | val values =>
            simp at run targetSequence
            rcases run with ⟨rfl, rfl⟩
            refine ⟨headExtra + tailExtra, targetFinal, ?_, finalRel⟩
            simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetSequence

/-- Mapping the interpreter replacement fallback over a list preserves evaluation. -/
theorem optInterp1_list_correct {C F : Type} (expressions : List ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate expressions [] source = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (expressions.map optInterp1) [] { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal :=
  evaluate_map_simulation optInterp1 optInterp1_correct expressions source target sourceFinal result run assumption related notTypeError

/-- The insertion fallback for a let simulates the original bindings and body. -/
theorem insertInterp1_let_fallback_correct {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.let trace bindings body] [] source = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.let .none (bindings.map optInterp1) body] [] { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases bindingsRun : ClosSem.evaluate bindings [] source with
  | mk bindingResult sourceMid =>
    have bindingNotTypeError : bindingResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bindingResult
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨bindingsExtra, targetMid, targetBindings, midRel⟩ :=
      optInterp1_list_correct bindings source target sourceMid bindingResult bindingsRun assumption related bindingNotTypeError
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun] at run
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨bindingsExtra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBindings]
    | val values =>
      have sourceBound : sourceMid.clock ≤ source.clock := by
        have bound := ClosSem.evaluate_clock_le bindings [] source
        simpa [bindingsRun] using bound
      obtain ⟨bodyExtra, targetFinal, targetBody, finalRel⟩ :=
        assumption.1 [body] sourceMid (values ++ []) targetMid result sourceFinal sourceBound run notTypeError midRel
      have shiftedBindings := ClosSem.evaluate_addClock.1 (bindings.map optInterp1) []
        { target with clock := bindingsExtra + target.clock } targetMid (.val values) bodyExtra targetBindings (by simp)
      let enlarged := { target with clock := (bindingsExtra + target.clock) + bodyExtra }
      let enlargedMid := { targetMid with clock := targetMid.clock + bodyExtra }
      have bindingsRun' : ClosSem.evaluate (bindings.map optInterp1) [] enlarged = (.val values, enlargedMid) := by
        simpa [enlarged, enlargedMid] using shiftedBindings
      have bodyRun' : ClosSem.evaluate [body] (values ++ []) enlargedMid = (result, targetFinal) := by
        simpa [enlargedMid, Nat.add_comm] using targetBody
      refine ⟨bindingsExtra + bodyExtra, targetFinal, ?_, finalRel⟩
      have targetRun : ClosSem.evaluate [.let .none (bindings.map optInterp1) body] [] enlarged = (result, targetFinal) := by
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, bindingsRun']
        exact bodyRun'
      simpa [enlarged, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using targetRun

/-- One-level interpreter insertion preserves singleton evaluation. -/
theorem insertInterp1_correct {C F : Type} (expression : ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [expression] [] source = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [insertInterp1 expression] [] { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  cases selected : optInterp expression with
  | some replacement =>
    simpa [insertInterp1, selected] using
      optInterp_correct expression replacement source target sourceFinal result selected run assumption related notTypeError
  | none =>
    cases expression <;> simp only [insertInterp1, selected]
    case «let» trace bindings body =>
      exact insertInterp1_let_fallback_correct trace bindings body source target sourceFinal result run assumption related notTypeError
    all_goals
      exact assumption.1 [_] source [] target result sourceFinal (by omega) run notTypeError related

/-- Mapping interpreter insertion over a program preserves its evaluation. -/
theorem insertInterp_correct {C F : Type} (expressions : List ClosLang.Exp)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate expressions [] source = (result, sourceFinal))
    (assumption : InterpAssum C F source.clock) (related : StateRel source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate (insertInterp expressions) [] { target with clock := extra + target.clock } =
        (result, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  exact evaluate_map_simulation insertInterp1 insertInterp1_correct expressions source target sourceFinal result
    run assumption related notTypeError

end Flapjack.Compiler.Backend.ClosInterp
