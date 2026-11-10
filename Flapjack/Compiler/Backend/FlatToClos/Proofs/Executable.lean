module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Correctness
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.NoMat
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileSemantics
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.NoMat
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.InstallPipeline
public import Flapjack.Compiler.Backend.ClosInterp.Proofs.AttachSemantics
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.NoMti
public import Flapjack.Compiler.Backend.ClosMti.Proofs.Semantics
public import Flapjack.FiniteMap.EmptyExact

@[expose] public section


/-! Connecting the proof-side declaration simulation to the initializer used
by the executed flat-to-closure compilation. This is Flapjack infrastructure. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The compiled initializer allocates global zero and installs the expected
interpreter closure or unit, without changing the remaining state. -/
private theorem evaluate_compileInit {C F : Type} (interpreter : Bool) (ffi : Flapjack.HolFfiState F)
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

/-- The initializer prepends unit to successful declaration evaluation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_compile_prog_initial_state"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem evaluateCompileProgInitialState {C F : Type}
    (maxApp : Nat) (declarations : List FlatLang.Exp) (ffi : Flapjack.HolFfiState F)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (clock : Nat) :
    0 < maxApp →
    ClosSem.evaluate (compileProg declarations) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock) =
    match ClosSem.evaluate (compileDecs declarations) []
      (initialStateProofSide (ClosLang.hasInstallList (compileDecs declarations))
        ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock) with
    | (.val values, state) => (.val (ClosSem.unitValue :: values), state)
    | (.err error, state) => (.err error, state) := by
  intro positive
  let interpreter := ClosLang.hasInstallList (compileDecs declarations)
  have initRun := evaluate_compileInit interpreter ffi maxApp clock
    HolFiniteMapExact.holEmpty oracle compiler positive
  unfold compileProg ClosInterp.attachInterpreter
  change ClosSem.evaluate (ClosInterp.compileInit interpreter :: compileDecs declarations) []
    (ClosSem.initialState ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock) = _
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ initRun]
  cases run : ClosSem.evaluate (compileDecs declarations) []
      (initialStateProofSide interpreter ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock) with
  | mk result state => cases result <;> rfl

/-- The initializer preserves exactly the declaration evaluation errors. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_compile_prog_initial_state_FST_Err"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem evaluateCompileProgInitialState_fstErr {C F : Type}
    (maxApp : Nat) (declarations : List FlatLang.Exp) (ffi : Flapjack.HolFfiState F)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C) (clock : Nat)
    (error : ErrorResult ClosSem.Value) :
    0 < maxApp →
    ((ClosSem.evaluate (compileProg declarations) []
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock)).1 = .err error ↔
     (ClosSem.evaluate (compileDecs declarations) []
      (initialStateProofSide (ClosLang.hasInstallList (compileDecs declarations))
        ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock)).1 = .err error) := by
  intro positive
  rw [evaluateCompileProgInitialState maxApp declarations ffi oracle compiler clock positive]
  cases run : ClosSem.evaluate (compileDecs declarations) []
      (initialStateProofSide (ClosLang.hasInstallList (compileDecs declarations))
        ffi maxApp HolFiniteMapExact.holEmpty oracle compiler clock) with
  | mk result state => cases result <;> simp

/-- Compiling declarations with the executable initializer simulates their
flat evaluation at the same clock. The initial unit is retained in successful
closure results; errors and the final related state are preserved. The
installation relation uses `incCompileDecsProofSide`; the production semantics
theorem composes this simulation with interpreter attachment. -/
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
  have initialRel := initialStates_related maxApp config oracle compiler ffi clock interpreter ⟨positive, install⟩
  have simulated := evaluate_decs_simulation (FlatSem.initialState ffi clock config) initial declarations
    initialRel safe notTypeError
  cases closRun : ClosSem.evaluate (compileDecs declarations) [] initial with
  | mk result finalTarget =>
    simp only [DecSim, closRun] at simulated
    refine ⟨result, finalTarget, simulated.2, simulated.1, ?_⟩
    have program := evaluateCompileProgInitialState maxApp declarations ffi oracle compiler clock positive
    cases result <;> simpa [HolFiniteMapExact.holEmpty, initial, interpreter, closRun] using program


end Flapjack.Compiler.Backend.FlatToClos
