import Flapjack.Compiler.Backend.ClosInterp.Proofs.InsertionCorrect

/-! Primitive noninterference for the proof-side interpreter simulation.
The evaluator and state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Replace compiler fields in an optional successful primitive result. -/
def replaceCompilerOption {C F : Type} (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C)
    (result : Option (ClosSem.Value × ClosSem.State C F)) : Option (ClosSem.Value × ClosSem.State C F) :=
  result.map fun (value, state) => (value, { state with compile := compiler, compileOracle := oracle })

/-- Global primitives do not inspect or change compiler fields. -/
theorem applyGlobal_replaceCompiler {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C) :
    ClosSem.applyGlobal op args { state with compile := compiler, compileOracle := oracle } =
      replaceCompilerOption compiler oracle (ClosSem.applyGlobal op args state) := by
  unfold ClosSem.applyGlobal replaceCompilerOption
  repeat' split
  all_goals simp_all [Function.comp_def]

/-- Block primitives do not inspect or change compiler fields. -/
theorem applyBlock_replaceCompiler {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C) :
    ClosSem.applyBlock op args { state with compile := compiler, compileOracle := oracle } =
      replaceCompilerOption compiler oracle (ClosSem.applyBlock op args state) := by
  unfold ClosSem.applyBlock replaceCompilerOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]

/-- Numeric primitives do not inspect or change compiler fields. -/
theorem applyNumeric_replaceCompiler {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C) :
    ClosSem.applyNumeric op args { state with compile := compiler, compileOracle := oracle } =
      replaceCompilerOption compiler oracle (ClosSem.applyNumeric op args state) := by
  cases op <;> simp [ClosSem.applyNumeric, replaceCompilerOption, Option.map_map, Function.comp_def]

/-- Memory primitives do not inspect or change compiler fields. -/
theorem applyMemory_replaceCompiler {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C) :
    ClosSem.applyMemory op args { state with compile := compiler, compileOracle := oracle } =
      replaceCompilerOption compiler oracle (ClosSem.applyMemory op args state) := by
  unfold ClosSem.applyMemory replaceCompilerOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind, Function.comp_def]))

/-- Replace compiler fields in a successful primitive result. -/
def replaceCompilerResult {C F : Type} (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C)
    (result : Result (ClosSem.Value × ClosSem.State C F) ClosSem.Value) :
    Result (ClosSem.Value × ClosSem.State C F) ClosSem.Value :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, { state with compile := compiler, compileOracle := oracle })

/-- Ordinary primitive applications do not inspect or change compiler fields. -/
theorem doApp_replaceCompiler {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state : ClosSem.State C F) (compiler : ClosSem.Compiler C) (oracle : ClosSem.CompileOracle C) :
    ClosSem.doApp op args { state with compile := compiler, compileOracle := oracle } =
      replaceCompilerResult compiler oracle (ClosSem.doApp op args state) := by
  cases op with
  | globOp operation =>
    cases found : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, applyGlobal_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, applyGlobal_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
  | blockOp operation =>
    cases found : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, applyBlock_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, applyBlock_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
  | memOp operation =>
    cases found : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, applyMemory_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, applyMemory_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
  | intOp operation =>
    cases found : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, applyNumeric_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, applyNumeric_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
  | wordOp operation =>
    cases found : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, applyNumeric_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [ClosSem.doApp, applyNumeric_replaceCompiler, found, replaceCompilerOption, replaceCompilerResult]
  | label | install => rfl
  | ffi | thunkOp =>
    simp only [ClosSem.doApp, replaceCompilerResult]
    repeat' split
    all_goals simp_all
    all_goals aesop

/-- Fields used to relate the compilation configurations survive an ordinary primitive. -/
def CompilerFieldsPreserved {C F : Type} (before after : ClosSem.State C F) : Prop :=
  after.compile = before.compile ∧ after.compileOracle = before.compileOracle ∧
  after.code = before.code ∧ after.maxApp = before.maxApp

/-- Successful global primitives preserve compiler configuration fields. -/
theorem applyGlobal_compilerFields {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyGlobal op args state = some (value, next)) : CompilerFieldsPreserved state next := by
  unfold ClosSem.applyGlobal at run
  unfold CompilerFieldsPreserved
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successful block primitives preserve compiler configuration fields. -/
theorem applyBlock_compilerFields {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyBlock op args state = some (value, next)) : CompilerFieldsPreserved state next := by
  unfold ClosSem.applyBlock at run
  unfold CompilerFieldsPreserved
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful numeric primitives preserve compiler configuration fields. -/
theorem applyNumeric_compilerFields {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyNumeric op args state = some (value, next)) : CompilerFieldsPreserved state next := by
  unfold ClosSem.applyNumeric at run
  unfold CompilerFieldsPreserved
  repeat' split at run
  all_goals simp_all

/-- Successful memory primitives preserve compiler configuration fields. -/
theorem applyMemory_compilerFields {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyMemory op args state = some (value, next)) : CompilerFieldsPreserved state next := by
  unfold ClosSem.applyMemory at run
  unfold CompilerFieldsPreserved
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- Successful ordinary primitives preserve compiler configuration fields. -/
theorem doApp_compilerFields {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp op args state = .val (value, next)) : CompilerFieldsPreserved state next := by
  cases op with
  | globOp operation =>
    cases h : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyGlobal_compilerFields operation args state next value h
  | blockOp operation =>
    cases h : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyBlock_compilerFields operation args state next value h
  | memOp operation =>
    cases h : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyMemory_compilerFields operation args state next value h
  | intOp operation =>
    cases h : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyNumeric_compilerFields (.intOp operation) args state next value h
  | wordOp operation =>
    cases h : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyNumeric_compilerFields (.wordOp operation) args state next value h
  | ffi | thunkOp =>
    simp only [ClosSem.doApp] at run
    unfold CompilerFieldsPreserved
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | install => simp [ClosSem.doApp] at run

/-- An initialized first global remains initialized after a global primitive. -/
theorem applyGlobal_firstGlobal {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value installed : ClosSem.Value)
    (present : state.globals.head? = some (some installed))
    (run : ClosSem.applyGlobal op args state = some (value, next)) :
    next.globals.head? = some (some installed) := by
  unfold ClosSem.applyGlobal at run
  repeat' split at run
  all_goals simp_all [ClosSem.getGlobal]
  all_goals try (solve | aesop)
  all_goals
    rename_i index value x heq
    cases globalsEq : state.globals with
    | nil => simp [globalsEq] at present
    | cons first rest =>
      cases index with
      | zero => simp_all
      | succ index =>
        rcases run with ⟨_, rfl⟩
        simpa [globalsEq] using present

/-- Block primitives do not change globals. -/
theorem applyBlock_globals {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyBlock op args state = some (value, next)) : next.globals = state.globals := by
  unfold ClosSem.applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Numeric primitives do not change globals. -/
theorem applyNumeric_globals {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyNumeric op args state = some (value, next)) : next.globals = state.globals := by
  unfold ClosSem.applyNumeric at run
  repeat' split at run
  all_goals simp_all

/-- Memory primitives do not change globals. -/
theorem applyMemory_globals {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyMemory op args state = some (value, next)) : next.globals = state.globals := by
  unfold ClosSem.applyMemory at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff])
  all_goals try (rcases h with ⟨entry, _, h⟩; cases entry <;> simp_all [Option.bind_eq_some_iff] <;> aesop)
  all_goals aesop

/-- An ordinary successful primitive preserves an initialized first global. -/
theorem doApp_firstGlobal {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value installed : ClosSem.Value)
    (present : state.globals.head? = some (some installed))
    (run : ClosSem.doApp op args state = .val (value, next)) :
    next.globals.head? = some (some installed) := by
  cases op with
  | globOp operation =>
    cases h : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      exact applyGlobal_firstGlobal operation args state next value installed present h
  | blockOp operation =>
    cases h : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      rw [applyBlock_globals operation args state next value h]
      exact present
  | memOp operation =>
    cases h : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      rw [applyMemory_globals operation args state next value h]
      exact present
  | intOp operation =>
    cases h : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      rw [applyNumeric_globals (.intOp operation) args state next value h]
      exact present
  | wordOp operation =>
    cases h : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, h] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, h] using run
      subst pair
      rw [applyNumeric_globals (.wordOp operation) args state next value h]
      exact present
  | ffi | thunkOp =>
    simp only [ClosSem.doApp] at run
    repeat' split at run
    all_goals simp_all
    all_goals aesop
  | label | install => simp [ClosSem.doApp] at run

/-- Related states differ only in the compiler callback and oracle. -/
theorem stateRel_replaceCompiler {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel source target) :
    source = { target with compile := source.compile, compileOracle := source.compileOracle } := by
  rcases related.1 with ⟨_, sourceCode, targetCode, maxEq, _, clockEq, ffiEq, globalsEq, refsEq, _, _⟩
  cases source
  cases target
  simp_all

/-- A successful ordinary primitive preserves the interpreter state relation. -/
theorem doApp_stateRel {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (value : ClosSem.Value)
    (related : StateRel source target) (run : ClosSem.doApp op args source = .val (value, sourceFinal)) :
    ∃ targetFinal, ClosSem.doApp op args target = .val (value, targetFinal) ∧ StateRel sourceFinal targetFinal := by
  have sourceEq := stateRel_replaceCompiler source target related
  rw [sourceEq, doApp_replaceCompiler] at run
  cases targetRun : ClosSem.doApp op args target with
  | err error => simp [targetRun, replaceCompilerResult] at run
  | val pair =>
    rcases pair with ⟨targetValue, targetFinal⟩
    simp [targetRun, replaceCompilerResult] at run
    rcases run with ⟨rfl, rfl⟩
    have fields := doApp_compilerFields op args target targetFinal targetValue targetRun
    have slot := doApp_firstGlobal op args target targetFinal targetValue
      (.closure none [] [] 1 closInterpreter) (by
        rw [← related.1.2.2.2.2.2.2.2.1]
        exact related.2) targetRun
    rcases fields with ⟨compileEq, oracleEq, codeEq, maxEq⟩
    rcases related with ⟨⟨safe, sourceCode, targetCode, oldMaxEq, positive, clockEq,
      ffiEq, globalsEq, refsEq, compilerEq, oracleRel⟩, installed⟩
    refine ⟨targetFinal, rfl, ?_⟩
    refine ⟨?_, slot⟩
    refine ⟨safe, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simpa only using codeEq.trans targetCode
    · simpa only using codeEq.trans targetCode
    · rw [maxEq, oldMaxEq]
      exact positive
    · simpa only [compileEq] using compilerEq
    · simpa only [oracleEq] using oracleRel

/-- Ordinary primitive errors agree in related states. -/
theorem doApp_error_stateRel {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (source target : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (related : StateRel source target) (run : ClosSem.doApp op args source = .err error) :
    ClosSem.doApp op args target = .err error := by
  have sourceEq := stateRel_replaceCompiler source target related
  rw [sourceEq, doApp_replaceCompiler] at run
  cases targetRun : ClosSem.doApp op args target with
  | err targetError =>
    simp [targetRun, replaceCompilerResult] at run
    cases run
    rfl
  | val pair =>
    rcases pair with ⟨value, next⟩
    simp [targetRun, replaceCompilerResult] at run

/-- Ordinary-operator simulation from the argument-list induction hypothesis. -/
theorem evaluate_ordinaryOp_simulation_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (target sourceFinal : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (result, sourceFinal) → StateRel source target →
      result ≠ .err (.abort .typeError) →
      ∃ extra targetFinal,
        ClosSem.evaluate args env { target with clock := extra + target.clock } = (result, targetFinal) ∧
        StateRel sourceFinal targetFinal)
    (related : StateRel source target)
    (run : ClosSem.evaluate [.op trace op args] env source = (result, sourceFinal))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ extra targetFinal,
      ClosSem.evaluate [.op trace op args] env { target with clock := extra + target.clock } = (result, targetFinal) ∧
      StateRel sourceFinal targetFinal := by
  rw [ClosSem.evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : ClosSem.evaluate args env source with
  | mk argsResult sourceMid =>
    rw [argsRun] at run
    have argsNotTypeError : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      simp at run
      exact notTypeError run.1.symm
    obtain ⟨extra, targetMid, targetArgs, midRel⟩ := argsIH target sourceMid argsResult argsRun related argsNotTypeError
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨extra, targetMid, ?_, midRel⟩
      rw [ClosSem.evaluate_ordinaryOp_eq trace op args env _ notInstall notForce, targetArgs]
    | val values =>
      cases appRun : ClosSem.doApp op values.reverse sourceMid with
      | err error =>
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        have targetApp := doApp_error_stateRel op values.reverse sourceMid targetMid error midRel appRun
        refine ⟨extra, targetMid, ?_, midRel⟩
        rw [ClosSem.evaluate_ordinaryOp_eq trace op args env _ notInstall notForce, targetArgs]
        simp [targetApp]
      | val pair =>
        rcases pair with ⟨value, next⟩
        simp [appRun] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetFinal, targetApp, finalRel⟩ := doApp_stateRel op values.reverse sourceMid targetMid next value midRel appRun
        refine ⟨extra, targetFinal, ?_, finalRel⟩
        rw [ClosSem.evaluate_ordinaryOp_eq trace op args env _ notInstall notForce, targetArgs]
        simp [targetApp]

end Flapjack.Compiler.Backend.ClosInterp
