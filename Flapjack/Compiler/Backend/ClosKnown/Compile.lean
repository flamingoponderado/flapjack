module

public import Flapjack.Compiler.Backend.ClosKnown.Total
public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.ClosTicks.Source
public import Flapjack.Compiler.Backend.ClosLetop.Source

@[expose] public section

/-! Executable known-function pass. The whole-pass correctness proof remains
unported. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The checked interface uses the total traversal for all inline factors. -/
def knownListBounded (_fuel : Nat) (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Option (List (Exp × ValApprox) × Spt ValApprox) :=
  some (knownListTotal c xs env globals)

/-- Run the incremental known-function traversal, retaining the auxiliary
program component unchanged. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "compile_inc_def"]
def compileInc {α : Type} (c : Config) (g : Spt ValApprox) (program : List Exp × α) :
    Spt ValApprox × List Exp × α :=
  let (eas, next) := knownListTotal (resetInlineFactor c) program.1 [] g
  (next, eas.map Prod.fst, program.2)

/-- Apply the original source closure optimizer, including its disabled case. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "compile_def"]
noncomputable def compileSource : Option Config → List Exp → Option Config × List Exp
  | none, es => (none, es)
  | some c, es =>
      let (eas, globals) := knownListTotal c (ClosFvs.compileSource es) [] .ln
      (some { c with valApproxSpt := globals },
        ClosLetop.compileSource (ClosTicks.removeSource (eas.map Prod.fst)))

/-- The executable closure optimizer uses the equivalent total traversals. -/
def compile : Option Config → List Exp → Option Config × List Exp
  | none, es => (none, es)
  | some c, es =>
      let (eas, globals) := knownListTotal c (ClosFvs.compile es) [] .ln
      (some { c with valApproxSpt := globals },
        ClosLetop.compileList (ClosTicks.removeList (eas.map Prod.fst)))

/-- The executed closure optimizer agrees with the original source pass. -/
@[simp] theorem compileSource_eq_compile (config : Option Config) (es : List Exp) :
    compileSource config es = compile config es := by
  cases config <;> simp [compileSource, compile]

/-- Prepare the static settings for incremental known-function optimization. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_static_conf_def"]
def knownStaticConf : Option Config → Option Config
  | none => none
  | some c => some { resetInlineFactor c with valApproxSpt := .ln }

/-- The original incremental optimizer threads its approximation tree. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "known_compile_inc_def"]
noncomputable def knownCompileIncSource {α : Type} (config : Option Config) (globals : Spt ValApprox)
    (program : List Exp × List α) : Spt ValApprox × (List Exp × List α) :=
  match config with
  | none => (globals, program)
  | some c =>
      let p : List Exp × List (Nat × Nat × Exp) := ClosFvs.compileIncSource program
      let (globals, es, aux) := compileInc c globals p
      let p : List Exp × List (Nat × Nat × Exp) := ClosTicks.compileIncSource (es, aux)
      let p : List Exp × List α := ClosLetop.compileIncSource p
      (globals, p)

/-- The executable incremental optimizer uses equivalent total traversals. -/
def knownCompileInc {α : Type} (config : Option Config) (globals : Spt ValApprox)
    (program : List Exp × List α) : Spt ValApprox × (List Exp × List α) :=
  match config with
  | none => (globals, program)
  | some c =>
      let p : List Exp × List (Nat × Nat × Exp) := ClosFvs.compileInc program
      let (globals, es, aux) := compileInc c globals p
      let p : List Exp × List (Nat × Nat × Exp) := ClosTicks.compileInc (es, aux)
      let p : List Exp × List α := ClosLetop.compileInc p
      (globals, p)

/-- Source and executable incremental optimization agree. -/
@[simp] theorem knownCompileIncSource_eq {α : Type} (config : Option Config)
    (globals : Spt ValApprox) (program : List Exp × List α) :
    knownCompileIncSource config globals program = knownCompileInc config globals program := by
  cases config <;> simp [knownCompileIncSource, knownCompileInc]

/-- Apply free-variable cleanup, approximation, tick removal and let-op cleanup. -/
def compileFuel (fuel : Nat) (config : Option Config) (es : List Exp) : Option (Option Config × List Exp) := do
  match config with
  | none => pure (none, es)
  | some c =>
      let es ← es.mapM (ClosFvs.removeBounded fuel 0)
      let (es, globals) ← knownListBounded fuel c es [] .ln
      let es ← es.mapM fun (e, _) => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e
      pure (some { c with valApproxSpt := globals }, es)

/-- Incremental known-function optimization retains the incoming global
approximations, resets the inline factor, and discards incoming auxiliary
code when enabled. The traversal is total; HOL correspondence of the complete pass remains to
be proved. -/
def compileIncFuel (fuel : Nat) (config : Option Config)
    (program : List Exp × List (Nat × Nat × Exp)) :
    Option (Option Config × (List Exp × List (Nat × Nat × Exp))) := do
  let previousGlobals := optionValApproxSpt config
  match config with
  | none => pure (none, program)
  | some c =>
      let es ← program.1.mapM (ClosFvs.removeBounded fuel 0)
      let static := { resetInlineFactor c with valApproxSpt := .ln }
      let (globals, es, _) := compileInc static previousGlobals (es, program.2)
      let es ← es.mapM fun e => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e
      pure (optionUpdValSpt globals config, (es, []))

end Flapjack.Compiler.Backend.ClosKnown
