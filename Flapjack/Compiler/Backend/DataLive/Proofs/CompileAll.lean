import Flapjack.Compiler.Backend.DataLive.Proofs.EvaluatorAll

/-! Assembly of the data liveness simulation cases. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- The data liveness simulation for every program and live set. This is
untagged pending source evaluator, carrier, and full HOL statement review. -/
theorem simulationFor_all {C F : Type} (program : DataLang.Prog) (live : NumSet) :
    simulationFor (C := C) (F := F) program live := by
  have allSizes : ∀ weight : Nat, ∀ (program : DataLang.Prog) (live : NumSet),
      sizeOf program = weight → simulationFor (C := C) (F := F) program live := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program live measure
      cases program with
      | skip => exact simulationFor_skip live
      | move dest src => exact simulationFor_move dest src live
      | assign dest op args names => exact simulationFor_assign dest op args names live
      | tick => exact simulationFor_tick live
      | makeSpace amount names => exact simulationFor_makeSpace amount names live
      | raise name => exact simulationFor_raise name live
      | «return» names => exact simulationFor_return names live
      | seq first second =>
        apply simulationFor_seq first second live
        · apply ih (sizeOf first) ?_ first (compile second live).2 rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf second) ?_ second live rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
      | ifThenElse name yes no =>
        apply simulationFor_if name yes no live
        · apply ih (sizeOf yes) ?_ yes live rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf no) ?_ no live rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
      | force ret label src =>
        intro source target result sourceNext run related notType exception
        apply force_correct_at ret label src live source target sourceNext result run related exception notType
        intro body source target sourceNext result _ related sameLocals exception notType run
        exact evaluatorSimulation_all body source target sourceNext result related sameLocals exception notType run
      | call ret dest arguments handler =>
        intro source target result sourceNext run related notType exception
        apply call_correct_at ret dest arguments handler live source target sourceNext result run related exception notType
        · intro body source target sourceNext result _ related sameLocals exception notType run
          exact evaluatorSimulation_all body source target sourceNext result related sameLocals exception notType run
        · intro name body handlerEq
          subst handler
          apply ih (sizeOf body) ?_ body live rfl
          simp only [DataLang.Prog.call.sizeOf_spec, Option.some.sizeOf_spec, Prod.mk.sizeOf_spec] at measure
          omega
  exact allSizes (sizeOf program) program live rfl

end Flapjack.Compiler.Backend.DataLive
