module

public import Flapjack.Compiler.Backend.DataSimp
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Data simplification proof infrastructure. -/
namespace Flapjack.Compiler.Backend.DataSimp

/-- Sequencing with a continuation has the same result as `pSeq`. This is
untagged pending correspondence review of the data evaluator. -/
theorem evaluate_pSeq {C F : Type} (first continuation : DataLang.Prog)
    (state : DataSem.State C F) :
    DataSem.evaluate (pSeq first continuation) state = DataSem.evaluate (.seq first continuation) state := by
  cases continuation <;> simp [pSeq, DataSem.evaluate_seq_skip]

/-- Sequencing is associative under the clocked data evaluator. -/
theorem evaluate_seq_assoc {C F : Type} (first second third : DataLang.Prog)
    (state : DataSem.State C F) :
    DataSem.evaluate (.seq (.seq first second) third) state =
      DataSem.evaluate (.seq first (.seq second third)) state := by
  cases run : DataSem.evaluate first state with
  | mk result next =>
    have bound : next.clock ≤ state.clock := by
      simpa [run] using DataSem.evaluate_clock_le first state
    cases result with
    | some value => simp [DataSem.evaluate, DataSem.fixClock, run, Nat.min_eq_right bound]
    | none =>
      cases secondRun : DataSem.evaluate second next with
      | mk secondResult last =>
        have secondBound : last.clock ≤ next.clock := by
          simpa [secondRun] using DataSem.evaluate_clock_le second next
        have finalBound : last.clock ≤ state.clock := Nat.le_trans secondBound bound
        cases secondResult <;>
          simp [DataSem.evaluate, DataSem.fixClock, run, secondRun, Nat.min_eq_right bound,
            Nat.min_eq_right secondBound, Nat.min_eq_right finalBound]

/-- Replacing a call handler with an observationally equal program does not
change evaluation of the call. -/
theorem evaluate_call_handler_congr {C F : Type} (ret : Option (List Nat × Flapjack.NumSet))
    (dest : Option Nat) (names : List Nat) (name : Nat) (first second : DataLang.Prog)
    (same : ∀ state : DataSem.State C F, DataSem.evaluate first state = DataSem.evaluate second state)
    (state : DataSem.State C F) :
    DataSem.evaluate (.call ret dest names (some (name, first))) state =
      DataSem.evaluate (.call ret dest names (some (name, second))) state := by
  simp only [DataSem.evaluate]
  repeat' (split <;> try simp_all)

/-- Pointwise equivalent programs remain equivalent when sequenced. -/
theorem evaluate_seq_congr {C F : Type} (first first' second second' : DataLang.Prog)
    (hFirst : ∀ state : DataSem.State C F, DataSem.evaluate first state = DataSem.evaluate first' state)
    (hSecond : ∀ state : DataSem.State C F, DataSem.evaluate second state = DataSem.evaluate second' state)
    (state : DataSem.State C F) :
    DataSem.evaluate (.seq first second) state = DataSem.evaluate (.seq first' second') state := by
  simp only [DataSem.evaluate, hFirst, hSecond]

/-- Pointwise equivalent branches remain equivalent under a conditional. -/
theorem evaluate_if_congr {C F : Type} (name : Nat) (yes yes' no no' : DataLang.Prog)
    (hYes : ∀ state : DataSem.State C F, DataSem.evaluate yes state = DataSem.evaluate yes' state)
    (hNo : ∀ state : DataSem.State C F, DataSem.evaluate no state = DataSem.evaluate no' state)
    (state : DataSem.State C F) :
    DataSem.evaluate (.ifThenElse name yes no) state = DataSem.evaluate (.ifThenElse name yes' no') state := by
  simp only [DataSem.evaluate, hYes, hNo]

/-- Simplifying a program with a continuation preserves its evaluation. This
is untagged pending correspondence review of the data evaluator. -/
theorem evaluate_simp {C F : Type} (program continuation : DataLang.Prog) (state : DataSem.State C F) :
    DataSem.evaluate (simp program continuation) state = DataSem.evaluate (.seq program continuation) state := by
  cases program with
  | skip => simp [DataSimp.simp, DataSem.evaluate, DataSem.fixClock]
  | «return» names =>
    simp [DataSimp.simp, DataSem.evaluate, DataSem.fixClock, DataSem.flushState]
    split <;> simp
  | raise name =>
    cases read : DataSem.getVar name state.locals with
    | none => simp [DataSimp.simp, DataSem.evaluate, DataSem.fixClock, read]
    | some value =>
      cases jump : DataSem.jumpExc state with
      | none => simp [DataSimp.simp, DataSem.evaluate, DataSem.fixClock, read, jump]
      | some next =>
        have clock := DataSem.jumpExc_clock state next jump
        cases next
        simp_all [DataSimp.simp, DataSem.evaluate, DataSem.fixClock]
  | seq first second =>
    calc
      DataSem.evaluate (simp (.seq first second) continuation) state =
          DataSem.evaluate (.seq first (simp second continuation)) state := by
            simpa [DataSimp.simp] using evaluate_simp first (simp second continuation) state
      _ = DataSem.evaluate (.seq first (.seq second continuation)) state := by
        apply evaluate_seq_congr first first (simp second continuation) (.seq second continuation)
        · intro state; rfl
        · intro state; exact evaluate_simp second continuation state
      _ = DataSem.evaluate (.seq (.seq first second) continuation) state :=
        (evaluate_seq_assoc first second continuation state).symm
  | ifThenElse name yes no =>
    rw [DataSimp.simp, evaluate_pSeq]
    apply evaluate_seq_congr _ _ continuation continuation
    · intro state
      apply evaluate_if_congr
      · intro state; simpa [DataSem.evaluate_seq_skip] using evaluate_simp yes .skip state
      · intro state; simpa [DataSem.evaluate_seq_skip] using evaluate_simp no .skip state
    · intro state; rfl
  | call ret dest names handler =>
    cases handler with
    | none => simp [DataSimp.simp, evaluate_pSeq]
    | some pair =>
      obtain ⟨name, handler⟩ := pair
      rw [DataSimp.simp, evaluate_pSeq]
      apply evaluate_seq_congr _ _ continuation continuation
      · intro state
        apply evaluate_call_handler_congr
        intro state
        simpa [DataSem.evaluate_seq_skip] using evaluate_simp handler .skip state
      · intro state; rfl
  | move dest src => simp [DataSimp.simp, evaluate_pSeq]
  | assign dest op names live => simp [DataSimp.simp, evaluate_pSeq]
  | makeSpace amount names => simp [DataSimp.simp, evaluate_pSeq]
  | tick => simp [DataSimp.simp, evaluate_pSeq]
  | force ret label src => simp [DataSimp.simp, evaluate_pSeq]
termination_by sizeOf program
decreasing_by all_goals (simp_wf; omega)

/-- Simplifying with a trailing skip preserves the program's evaluation. -/
theorem simp_correct {C F : Type} (program : DataLang.Prog) (state : DataSem.State C F) :
    DataSem.evaluate (simp program .skip) state = DataSem.evaluate program state := by
  simpa [DataSem.evaluate_seq_skip] using evaluate_simp program .skip state

end Flapjack.Compiler.Backend.DataSimp
