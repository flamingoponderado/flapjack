import Flapjack.Compiler.Backend.ClosKnown.Total

/-! Executable known-function pass. The whole-pass correctness proof remains
unported. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

/-- The checked interface uses the total traversal for all inline factors. -/
def knownListBounded (_fuel : Nat) (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Option (List (Exp × ValApprox) × Spt ValApprox) :=
  some (knownListTotal c xs env globals)

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
      let (es, globals) ← knownListBounded fuel static es [] previousGlobals
      let es ← es.mapM fun (e, _) => do
        let e ← ClosTicks.removeBounded fuel e
        ClosLetop.compileBounded fuel e
      pure (optionUpdValSpt globals config, (es, []))

end Flapjack.Compiler.Backend.ClosKnown
