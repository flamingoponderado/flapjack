module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Simulation

@[expose] public section

/-! Correctness of the compiled entry call. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace CompilePartCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end CompilePartCarrier

/-- A source entry call and its compiled DATA call have corresponding results
and final states, provided the source does not produce a type error. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_part_evaluate"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem compilePartEvaluate {C F : Type} (start : Nat) (s1 : BviSem.BviState C F)
    (res : BviSem.BviResult) (s2 : BviSem.BviState C F) (t1 : DataSem.State C F)
    (run : BviSem.evaluate [.call 0 (some start) [] none] [] s1 = (res, s2))
    (notType : res ≠ .err (.abort .typeError)) (related : stateRel s1 t1)
    (empty : sptIsEmpty t1.locals = true)
    (jump : ∀ x, res = .err (.raise x) → DataSem.jumpExc t1 ≠ none) :
    ∃ (r : Result (List DataSem.Value) DataSem.Value) (t2 : DataSem.State C F),
      DataSem.evaluate (.call none (some start) [] none) t1 = (some r, t2) ∧
      stateRel s2 t2 ∧ dataToBviResult r = res := by
  have emptyLocals : t1.locals = .ln := by
    cases h : t1.locals <;> simp_all [sptIsEmpty]
  have noReturn : ¬isReturn res := by
    rintro ⟨returned, eq⟩
    have no : (BviSem.evaluate [.call 0 (some start) [] none] [] s1).1 ≠
        .err (.raise (.ret returned)) := by
      rw [BviSem.evaluate]
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [BviSem.evaluate]
      simp only [BviSem.fixClock, Nat.min_self]
      cases found : BvlSem.findCode (some start) [] s1.code with
      | none => simp [BviSem.typeError]
      | some pair =>
        obtain ⟨args, body⟩ := pair
        by_cases zero : s1.clock < 0 + 1
        · simp [zero, BviSem.timeoutError]
        · simp only [zero, ↓reduceIte]
          cases called : BviSem.evaluate [body] args (BviSem.decClock (0 + 1) s1) with
          | mk result last =>
            cases result with
            | val values => simp
            | err error =>
              cases error with
              | abort reason => simp
              | raise raised => cases raised <;> simp [BviSem.typeError]
    rw [run, eq] at no
    exact no rfl
  obtain ⟨next, prog, pres, vs, nextVar, ls, compiled, targetRun, finalRel, outcome⟩ :=
    compileCorrect [.call 0 (some start) [] none] [] s1 res s2 t1 0 [] true []
      run notType (by constructor) (by simp) (by simp [emptyLocals]) related (by simp)
      (by rintro ⟨value, eq⟩; exact jump (.exn value) eq)
  have code : prog = .seq .skip (.call none (some start) [] none) := by
    simpa [compileSource, DataLang.mkTicks] using (congrArg Prod.fst compiled).symm
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    refine ⟨result, next, ?_, finalRel, outcome.1 noReturn⟩
    simpa [code, DataSem.evaluate, DataSem.fixClock] using targetRun

end Flapjack.Compiler.Backend.BviToData
