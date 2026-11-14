module

public import Flapjack.Compiler.Backend.DataLive.Proofs.EvaluatorAll

@[expose] public section

/-! Assembly of the data liveness simulation cases. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Internal induction packaging for the data liveness simulation. The
source-shaped HOL theorem is stated below as `evaluate_compile`. -/
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

/-- The original local simulation theorem, with the compiler output and
exception-jump correspondence stated explicitly. The evaluator inherits the
real-model assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_liveProofScript.sml" "evaluate_compile"]
theorem evaluate_compile {C F : Type} (program : DataLang.Prog)
    (source : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (sourceNext : State C F) (live : NumSet) (target : State C F)
    (liveBefore : NumSet) (compiled : DataLang.Prog)
    (premises : DataSem.evaluate program source = (result, sourceNext) ∧
      stateRel source target liveBefore ∧ compile program live = (compiled, liveBefore) ∧
      result ≠ some (.err (.abort .typeError)) ∧
      (∀ sourceJump, jumpExc source = some sourceJump →
        ∃ targetJump, jumpExc target = some targetJump ∧ stateRel sourceJump targetJump .ln ∧
          targetJump.handler = sourceJump.handler ∧ targetJump.stack.length = sourceJump.stack.length)) :
    ∃ targetNext, DataSem.evaluate compiled target = (result, targetNext) ∧
      stateRel sourceNext targetNext (match result with | none => live | some _ => .ln) := by
  obtain ⟨run, related, compilation, notType, exception⟩ := premises
  have sim := simulationFor_all (C := C) (F := F) program live
  unfold simulationFor at sim
  have output := sim source target result sourceNext run (by simpa [compilation] using related)
    notType exception
  cases result <;> simpa [compilation, postLive] using output

end Flapjack.Compiler.Backend.DataLive
