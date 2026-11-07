import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationOpGlobal
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationInstallDispatch

/-! Complete operation induction case for known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Op
open ClosSem ClosProps Relations Relations.StateRelation

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Operation case of the original optimizer simulation, with the evaluator's
argument, installed-program, and forced-body induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct0"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrect0Op {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (env : List Value) (s0 : ClosSem.State (Spt ValApprox × C) F)
    (installIH : ∀ (argResult : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
      (middle : ClosSem.State (Spt ValApprox × C) F) (values : List Value)
      (installResult : Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value)
      (installed : ClosSem.State (Spt ValApprox × C) F) (program : List ClosLang.Exp),
      evaluate xs env s0 = (argResult, middle) ∧ argResult = .val values ∧ op = .install ∧
      doInstall values.reverse middle = (installResult, installed) ∧ installResult = .val program →
      KnownSimulationAt program [] installed)
    (forceIH : ∀ (argResult : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
      (middle : ClosSem.State (Spt ValApprox × C) F) (values : List Value)
      (mode : AstHOL.ThunkMode) (value : Value),
      evaluate xs env s0 = (argResult, middle) ∧ argResult = .val values ∧
      op ≠ .install ∧ op = .thunkOp .forceThunk ∧
      destThunk values middle.refs = .isThunk mode value ∧ mode = .notEvaluated →
      KnownSimulationAt [appUnit (.var .none 0)] [value] middle)
    (argsIH : KnownSimulationAt xs env s0) : KnownSimulationAt [.op trace op xs] env s0 := by
  cases op with
  | label label => exact Ordinary.knownCorrect0OpLabel trace label xs env s0 argsIH
  | ffi name => exact Ordinary.knownCorrect0OpFfi trace name xs env s0 argsIH
  | intOp operation => exact Ordinary.knownCorrect0OpInt trace operation xs env s0 argsIH
  | wordOp operation => exact Ordinary.knownCorrect0OpWord trace operation xs env s0 argsIH
  | blockOp operation => exact Ordinary.knownCorrect0OpBlock trace operation xs env s0 argsIH
  | memOp operation => exact Ordinary.knownCorrect0OpMemory trace operation xs env s0 argsIH
  | globOp operation =>
    cases operation with
    | global index => exact Global.knownCorrect0OpGlobal trace index xs env s0 argsIH
    | setGlobal index => exact SetGlobal.knownCorrect0OpSetGlobal trace index xs env s0 argsIH
    | allocGlobal => exact Ordinary.knownCorrect0OpAllocGlobal trace xs env s0 argsIH
    | globalsPtr => exact Ordinary.knownCorrect0OpGlobalsPtr trace xs env s0 argsIH
    | setGlobalsPtr => exact Ordinary.knownCorrect0OpSetGlobalsPtr trace xs env s0 argsIH
  | install =>
    apply Install.knownCorrect0OpInstall trace xs env s0 ?_ argsIH
    intro args middle program installed run install
    exact installIH (.val args) middle args (.val program) installed program ⟨run, rfl, rfl, install, rfl⟩
  | thunkOp operation =>
    cases operation with
    | allocThunk mode => exact Ordinary.knownCorrect0OpAllocThunk trace mode xs env s0 argsIH
    | updateThunk mode => exact Ordinary.knownCorrect0OpUpdateThunk trace mode xs env s0 argsIH
    | forceThunk =>
      apply Force.knownCorrect0OpForce trace xs env s0 ?_ argsIH
      intro args middle value run found
      exact forceIH (.val args) middle args .notEvaluated value ⟨run, rfl, by simp, rfl, found, rfl⟩

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Op
