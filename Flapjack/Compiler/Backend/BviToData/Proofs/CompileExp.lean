module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Simulation

@[expose] public section

/-! Correctness of the optimized BVI-to-data expression compiler. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace CompileExpCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end CompileExpCarrier

/-- Optimized expression compilation preserves every non-type-error result
other than the internal return marker. The three independent inhabited types
model HOL's unused existentially quantified type variables. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem compileExpCorrect {C F P V N : Type} [Nonempty P] [Nonempty V] [Nonempty N]
    (exp : Bvi.Exp) (env : List BvlSem.Value) (s1 : BviSem.BviState C F)
    (res : BviSem.BviResult) (s2 : BviSem.BviState C F) (t1 : DataSem.State C F) (n : Nat)
    (run : BviSem.evaluate [exp] env s1 = (res, s2))
    (notType : res ≠ .err (.abort .typeError))
    (vars : DataProps.varCorr env (List.range n) (sptMap dataToBviValue t1.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k t1.locals = none)
    (related : stateRel s1 t1)
    (jump : ∀ value, res = .err (.raise (.exn value)) → DataSem.jumpExc t1 ≠ none)
    (notReturn : ∀ values, res ≠ .err (.raise (.ret values))) :
    ∃ (t2 : DataSem.State C F) (_prog : P) (_vs : V) (_next_var : N)
      (r : Result (List DataSem.Value) DataSem.Value),
      DataSem.evaluate (compileExp n exp) t1 = (some r, t2) ∧
      stateRel s2 t2 ∧ dataToBviResult r = res := by
  classical
  have notRet : ¬isReturn res := by
    rintro ⟨values, eq⟩
    exact notReturn values eq
  have jump' : isException res → DataSem.jumpExc t1 ≠ none := by
    rintro ⟨value, eq⟩
    exact jump value eq
  obtain ⟨next, prog, pres, vs, nextVar, ls, compiled, targetRun, finalRel, outcome⟩ :=
    compileCorrect [exp] env s1 res s2 t1 n (List.range n) true [] run notType vars
      (by simp) fresh related (by simp) jump'
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have projected := outcome.1 notRet
    have allowed : (DataSem.evaluate prog t1).1 ≠ some (.err (.abort .typeError)) := by
      rw [targetRun]
      intro bad
      have badResult : result = .err (.abort .typeError) := Option.some.inj bad
      rw [badResult] at projected
      exact notType (by simpa [dataToBviResult] using projected.symm)
    have stopped : (DataSem.evaluate prog t1).1 ≠ none := by simp [targetRun]
    obtain ⟨safe, peak, smx, lsz, optimized⟩ := optimise_correct prog t1 allowed stopped
    let final := {next with localsSize := lsz, safeForSpace := safe, peakHeapLength := peak, stackMax := smx}
    refine ⟨final, Classical.choice inferInstance, Classical.choice inferInstance,
      Classical.choice inferInstance, result, ?_, ?_, projected⟩
    · simpa [compileExp, compiled, targetRun, final] using optimized
    · exact (stateRel_peakSafe s2 next safe peak lsz smx).mp finalRel

end Flapjack.Compiler.Backend.BviToData
