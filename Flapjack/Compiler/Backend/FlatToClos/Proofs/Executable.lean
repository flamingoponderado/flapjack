import Flapjack.Compiler.Backend.FlatToClos.Proofs.Correctness
import Flapjack.Compiler.Backend.FlatPattern.Proofs.NoMat
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat
import Flapjack.Compiler.Backend.FlatToClos.Proofs.InstallPipeline

/-! Connecting the proof-side declaration simulation to the initializer used
by the executed flat-to-closure compilation. This is Flapjack infrastructure;
the semantic carriers and HOL correspondence remain under review. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The compiled initializer allocates global zero and installs the expected
interpreter closure or unit, without changing the remaining state. -/
theorem evaluate_compileInit {C F : Type} (interpreter : Bool) (ffi : Flapjack.HolFfiState F)
    (maxApp clock : Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (positive : 0 < maxApp) :
    ClosSem.evaluate [ClosInterp.compileInit interpreter] []
      (ClosSem.initialState ffi maxApp code oracle compiler clock) =
    (.val [ClosSem.unitValue], initialStateProofSide interpreter ffi maxApp code oracle compiler clock) := by
  change ClosSem.evaluate
    [.let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
      if interpreter then .fn (ofString "clos_interpreter") none none 1 ClosInterp.closInterpreter
      else .op .none (.blockOp (.cons 0)) []]
      (.op .none (.globOp (.setGlobal 0)) [.var .none 1])]
    [] (ClosSem.initialState ffi maxApp code oracle compiler clock) = _
  have enough : 1 ≤ maxApp := positive
  cases interpreter <;>
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.initialState, initialStateProofSide,
      ClosSem.doApp, ClosSem.applyGlobal, ClosSem.applyNumeric, ClosSem.doIntApp,
      ClosSem.applyBlock, ClosSem.getGlobal, ClosSem.unitValue, enough]

/-- Compiling declarations with the executable initializer simulates their
flat evaluation at the same clock. The initial unit is retained in successful
closure results; errors and the final related state are preserved. The
installation relation uses `incCompileDecsProofSide`, which does not yet
establish correspondence with the optimized incremental compiler. -/
theorem compileProg_evaluate_related {C F : Type}
    (ffi : Flapjack.HolFfiState F) (maxApp clock : Nat) (config : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (declarations : List FlatLang.Exp)
    (positive : 0 < maxApp) (install : installConfigRel config oracle compiler)
    (safe : FlatProps.noMatDecs declarations = true)
    (notTypeError : (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations).2 ≠
      some (.abort .typeError)) :
    ∃ result finalTarget,
      DecResultRel (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations).2 result ∧
      StateRel (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config) declarations).1 finalTarget ∧
      ClosSem.evaluate (compileProg declarations) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) =
        (match result with
         | .val values => (.val (ClosSem.unitValue :: values), finalTarget)
         | .err error => (.err error, finalTarget)) := by
  let interpreter := ClosLang.hasInstallList (compileDecs declarations)
  let initial := initialStateProofSide interpreter ffi maxApp HolFiniteMapExact.empty oracle compiler clock
  have initialRel := initialStates_related interpreter ffi maxApp clock config oracle compiler positive install
  have simulated := evaluate_decs_simulation (FlatSem.initialState ffi clock config) initial declarations
    initialRel safe notTypeError
  have initRun := evaluate_compileInit interpreter ffi maxApp clock HolFiniteMapExact.empty oracle compiler positive
  cases closRun : ClosSem.evaluate (compileDecs declarations) [] initial with
  | mk result finalTarget =>
    simp only [DecSim, closRun] at simulated
    refine ⟨result, finalTarget, simulated.2, simulated.1, ?_⟩
    unfold compileProg ClosInterp.attachInterpreter
    change ClosSem.evaluate (ClosInterp.compileInit interpreter :: compileDecs declarations) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) = _
    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ initRun]
    simp [initial, closRun]
    cases result <;> rfl


/-- Pattern-compiled declarations satisfy the match-freedom prerequisite of
the executable flat-to-closure initializer. The installation correspondence
still uses the proof-side incremental compiler. -/
theorem compilePatternProg_evaluate_related {C F : Type}
    (patternConfig : FlatPattern.Config)
    (ffi : Flapjack.HolFfiState F) (maxApp clock : Nat) (config : FlatSem.InstallConfig C)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (declarations : List FlatLang.Exp)
    (positive : 0 < maxApp) (install : installConfigRel config oracle compiler)
    (notTypeError : (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config)
      (declarations.map (FlatPattern.compileDec patternConfig))).2 ≠ some (.abort .typeError)) :
    ∃ result finalTarget,
      DecResultRel (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config)
        (declarations.map (FlatPattern.compileDec patternConfig))).2 result ∧
      StateRel (FlatSem.evaluateDecs (FlatSem.initialState ffi clock config)
        (declarations.map (FlatPattern.compileDec patternConfig))).1 finalTarget ∧
      ClosSem.evaluate (compileProg (declarations.map (FlatPattern.compileDec patternConfig))) []
        (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle compiler clock) =
        (match result with
         | .val values => (.val (ClosSem.unitValue :: values), finalTarget)
         | .err error => (.err error, finalTarget)) := by
  exact compileProg_evaluate_related ffi maxApp clock config oracle compiler _ positive install
    (FlatPattern.noMat_compileDecs patternConfig declarations) notTypeError

/-- A non-failing source program yields a related closure evaluation after
the complete source-to-flat pass. This composes the factored source semantics
and the proof-side flat-to-closure initialization relation; neither is yet a
reviewed cross-language correctness theorem. -/
theorem sourceCompileProg_evaluate_related {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (oracle : ClosSem.CompileOracle C)
    (compiler : ClosSem.Compiler C) (declarations : List AstHOL.Dec) (maxApp clock : Nat)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig flatConfig declarations)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp) (install : installConfigRel flatConfig oracle compiler) :
    ∃ result finalTarget,
      DecResultRel (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock flatConfig)
        (SourceToFlat.compileTotal sourceConfig declarations).2).2 result ∧
      StateRel (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock flatConfig)
        (SourceToFlat.compileTotal sourceConfig declarations).2).1 finalTarget ∧
      ClosSem.evaluate (compileProg (SourceToFlat.compileTotal sourceConfig declarations).2) []
        (ClosSem.initialState source.ffi maxApp HolFiniteMapExact.empty oracle compiler clock) =
        (match result with
         | .val values => (.val (ClosSem.unitValue :: values), finalTarget)
         | .err error => (.err error, finalTarget)) := by
  have sourceSem := SourceToFlat.factoredCompile_semantics interp transform source sourceEnv sourceConfig
    flatConfig declarations precondition safe
  have noFail : FlatSem.semantics flatConfig source.ffi (SourceToFlat.compileTotal sourceConfig declarations).2 ≠ .fail := by
    intro fail
    rw [fail] at sourceSem
    exact safe sourceSem
  have noTypeError : (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock flatConfig)
      (SourceToFlat.compileTotal sourceConfig declarations).2).2 ≠ some (.abort .typeError) := by
    intro error
    apply noFail
    simp [FlatSem.semantics, show ∃ k,
      (FlatSem.evaluateDecs (FlatSem.initialState source.ffi k flatConfig)
        (SourceToFlat.compileTotal sourceConfig declarations).2).2 = some (.abort .typeError) from ⟨clock, error⟩]
  exact compileProg_evaluate_related source.ffi maxApp clock flatConfig oracle compiler _ positive install
    (SourceToFlat.noMat_compileTotal sourceConfig declarations) noTypeError

/-- The pattern configuration ensures that every dynamically compiled flat
program is match-free, as required by the subsequent closure pass. -/
theorem sourcePrecondition_oracle_noMat {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (declarations : List AstHOL.Dec)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig flatConfig declarations)
    (index : Nat) : FlatProps.noMatDecs (flatConfig.compileOracle index).2 = true := by
  obtain ⟨middle, _, relation⟩ := precondition
  have oracle := congrFun relation.1 index
  have output := congrArg Prod.snd oracle
  simpa [Function.comp_def, BackendProps.snd_pureCo] using
    output ▸ FlatPattern.noMat_compileDecs sourceConfig.patternCfg (middle.compileOracle index).2

/-- The per-clock source-to-closure simulation can be initialized using the
actual incremental callback after factoring out interpreter insertion. The
remaining interpreter-insertion semantics are still a separate obligation. -/
theorem sourceCompileProg_production_evaluate_related {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (SourceToFlat.Config × C)))
    (transform : List AstHOL.Dec → List AstHOL.Dec)
    (source : State F) (sourceEnv : SemEnv Value) (sourceConfig : SourceToFlat.Config)
    (flatConfig : FlatSem.InstallConfig C) (compiler : ClosSem.Compiler C)
    (declarations : List AstHOL.Dec) (maxApp clock : Nat)
    (precondition : SourceToFlat.FactoredPrecondition interp transform source sourceEnv sourceConfig flatConfig declarations)
    (safe : ¬ Flapjack.SemanticsHOL.semanticsProg source sourceEnv declarations .fail)
    (positive : 0 < maxApp)
    (production : flatConfig.compile = BackendProps.pureCc incCompileDecs compiler) :
    ∃ result finalTarget,
      DecResultRel (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock flatConfig)
        (SourceToFlat.compileTotal sourceConfig declarations).2).2 result ∧
      StateRel (FlatSem.evaluateDecs (FlatSem.initialState source.ffi clock flatConfig)
        (SourceToFlat.compileTotal sourceConfig declarations).2).1 finalTarget ∧
      ClosSem.evaluate (compileProg (SourceToFlat.compileTotal sourceConfig declarations).2) []
        (ClosSem.initialState source.ffi maxApp HolFiniteMapExact.empty
          (BackendProps.pureCo incCompileDecsProofSide ∘ flatConfig.compileOracle)
          (BackendProps.pureCc ClosInterp.insertProgram compiler) clock) =
        (match result with
         | .val values => (.val (ClosSem.unitValue :: values), finalTarget)
         | .err error => (.err error, finalTarget)) := by
  apply sourceCompileProg_evaluate_related interp transform source sourceEnv sourceConfig flatConfig _ _
    declarations maxApp clock precondition safe positive
  exact production_installConfigRel flatConfig compiler
    (sourcePrecondition_oracle_noMat interp transform source sourceEnv sourceConfig flatConfig declarations precondition)
    production

end Flapjack.Compiler.Backend.FlatToClos
