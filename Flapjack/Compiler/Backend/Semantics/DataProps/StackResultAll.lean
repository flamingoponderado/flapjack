import Flapjack.Compiler.Backend.Semantics.DataProps.StackResultCall

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
  have allRanks : ∀ clock weight : Nat, ∀ (program : DataLang.Prog) (state next : State C F)
      (result : Option (Result (List Value) Value)), state.clock = clock → sizeOf program = weight →
      evaluate program state = (result, next) → stackResult state result next := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (program : DataLang.Prog) (state next : State C F)
            (result : Option (Result (List Value) Value)), state.clock ≤ clock → sizeOf program < weight →
            evaluate program state = (result, next) → stackResult state result next := by
          intro program state next result clockLe weightLt run
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (sizeOf program) program state next result rfl rfl run
          · exact weightIH (sizeOf program) weightLt program state next result clockEq rfl run
        have smaller : ∀ (program : DataLang.Prog) (state next : State C F)
            (result : Option (Result (List Value) Value)), state.clock < clock →
            evaluate program state = (result, next) → stackResult state result next := by
          intro program state next result clockLt run
          exact clockIH state.clock clockLt (sizeOf program) program state next result rfl rfl run
        intro program state next result stateClock measure run
        cases program with
        | skip => exact evaluate_skip_stackResult state next result run
        | move dest src => exact evaluate_move_stackResult dest src state next result run
        | assign dest op names live => exact evaluate_assign_stackResult dest op names live state next result run
        | tick => exact evaluate_tick_stackResult state next result run
        | makeSpace amount names => exact evaluate_makeSpace_stackResult amount names state next result run
        | raise name => exact evaluate_raise_stackResult name state next result run
        | «return» names => exact evaluate_return_stackResult names state next result run
        | seq first second =>
          apply evaluate_seq_stackResult first second state next result
          · intro after outcome firstRun
            apply exprIH first state after outcome (by omega)
            · simp only [DataLang.Prog.seq.sizeOf_spec] at measure
              omega
            · exact firstRun
          · intro before after outcome bound secondRun
            apply exprIH second before after outcome (by omega)
            · simp only [DataLang.Prog.seq.sizeOf_spec] at measure
              omega
            · exact secondRun
          · exact run
        | ifThenElse name yes no =>
          apply evaluate_if_stackResult name yes no state next result
          · intro after outcome branchRun
            apply exprIH yes state after outcome (by omega)
            · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
              omega
            · exact branchRun
          · intro after outcome branchRun
            apply exprIH no state after outcome (by omega)
            · simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
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
  exact allRanks state.clock (sizeOf program) program state next result rfl rfl run

end Flapjack.Compiler.Backend.DataSem
