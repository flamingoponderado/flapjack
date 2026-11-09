import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultCall
import Flapjack.Misc.ClockWeightInduction

/-! General result-sensitive control invariant for the data evaluator. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Evaluation preserves entry control for continuing and value-returning
results, and raised exceptions agree with the entry exception jump. Abort
results are unrestricted, so this is weaker than HOL's full evaluator stack
theorem and is not tagged as that theorem. -/
theorem evaluate_stackResult {C F : Type} (program : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate program state = (result, next)) : stackResult state result next := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => ∀ next result,
      evaluate program state = (result, next) → stackResult state result next) ?_
    program state next result run
  intro program state exprIH₀ smaller₀
  have exprIH := fun (program' : DataLang.Prog) (s next : State C F)
      (result : Option (Result (List Value) Value)) h1 h2 run =>
    exprIH₀ program' s h1 h2 next result run
  have smaller := fun (program' : DataLang.Prog) (s next : State C F)
      (result : Option (Result (List Value) Value)) h1 run =>
    smaller₀ program' s h1 next result run
  intro next result run
  cases program with
  | skip => exact evaluate_skip_stackResult state next result run
  | move dest src => exact evaluate_move_stackResult dest src state next result run
  | assign dest op names live => exact evaluate_assign_stackResult dest op names live state next
                                   result run
  | tick => exact evaluate_tick_stackResult state next result run
  | makeSpace amount names => exact evaluate_makeSpace_stackResult amount names state next result
                                run
  | raise name => exact evaluate_raise_stackResult name state next result run
  | «return» names => exact evaluate_return_stackResult names state next result run
  | seq first second =>
    apply evaluate_seq_stackResult first second state next result
    · intro after outcome firstRun
      apply exprIH first state after outcome (by omega)
      · simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
        omega
      · exact firstRun
    · intro before after outcome bound secondRun
      apply exprIH second before after outcome (by omega)
      · simp only [DataLang.Prog.seq.sizeOf_spec] at ⊢
        omega
      · exact secondRun
    · exact run
  | ifThenElse name yes no =>
    apply evaluate_if_stackResult name yes no state next result
    · intro after outcome branchRun
      apply exprIH yes state after outcome (by omega)
      · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
        omega
      · exact branchRun
    · intro after outcome branchRun
      apply exprIH no state after outcome (by omega)
      · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at ⊢
        omega
      · exact branchRun
    · exact run
  | force ret label src =>
    apply evaluate_force_stackResult ret label src state next result
    · intro body entered finished outcome bound bodyRun
      exact smaller body entered finished outcome (by omega) bodyRun
    · exact run
  | call ret dest names handler =>
    apply evaluate_call_stackResult ret dest names handler state next result
    · intro body entered finished outcome bound bodyRun
      exact smaller body entered finished outcome (by omega) bodyRun
    · exact run

end Flapjack.Compiler.Backend.DataSem
