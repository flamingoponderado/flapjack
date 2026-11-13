module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Program
public import Flapjack.Compiler.Backend.BviToData.Proofs.CompilePart

@[expose] public section

/-! Correctness of entry-call evaluation from initial compiler states. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/- The canonical BVI reference carrier and its broad view roundtrip. -/
namespace ProgramEvaluateCarrier

theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ state : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad state).toBroad = state) ∧
    (∀ state : BviSem.BviState C F, BviSem.BviState.ofBroad state.toBroad = state) :=
  BviSem.holFmapAsFiniteSupportWitness

end ProgramEvaluateCarrier

/-- Compiling the initial code preserves every entry-call evaluation that
produces neither a type error nor an uncaught raise. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "compile_prog_evaluate"
  (fmap_as_finite_support_relation := [BviState.refs])]
theorem compileProgEvaluate {C F : Type} (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C)
    (compiler : DataSem.Compiler C) (clock start : Nat) (limits : DataSem.Limits)
    (sizes : Spt Nat) (res : BviSem.BviResult) (s : BviSem.BviState C F)
    (run : BviSem.evaluate [.call 0 (some start) [] none] []
      (BviSem.initialState ffi (sptFromAList program) oracle
        (fun cfg code => compiler cfg (compileProg code)) clock) = (res, s))
    (notType : res ≠ .err (.abort .typeError))
    (notRaise : ∀ x, res ≠ .err (.raise x)) :
    ∃ (r2 : Result (List DataSem.Value) DataSem.Value) (s2 : DataSem.State C F),
      DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState ffi (sptFromAList (compileProg program))
          (fun n => let (cfg, code) := oracle n; (cfg, compileProg code))
          compiler true limits sizes clock) = (some r2, s2) ∧
      stateRel s s2 ∧ dataToBviResult r2 = res := by
  apply compilePartEvaluate start _ res s _ run notType
    (initialState_related ffi program oracle compiler true limits sizes clock)
  · rfl
  · intro x eq
    exact False.elim (notRaise x eq)

end Flapjack.Compiler.Backend.BviToData
