import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.ClosToBvl.Compile
import Flapjack.Compiler.Backend.ClosToBvl.Names
import Flapjack.Compiler.Backend.ClosToBvl.Sort
import Flapjack.Compiler.Backend.ClosToBvl.Stubs
import Flapjack.Compiler.Backend.ClosAnnotate.Shift
import Flapjack.Compiler.Backend.ClosNumber
import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Compiler.Backend.ClosCall

/-! Checked closure-to-BVL assembly after closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString

/-- Assemble a prepared closure program with its application, force and
initialization stubs. The caller supplies the result of HOL's `compile_common`;
that preprocessing and the success of checked expression lowering remain
unproved, so this is not the full HOL `compile` definition. -/
def compilePrepared? (original current : Config) (es : List ClosLang.Exp)
    (prog : List (Nat × Nat × ClosLang.Exp)) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let n := numStubs current.maxApp
  let initial := (sptToAList (initCode current.maxApp)).map fun (loc, arity, code) => (loc, arity, code)
  let compiled ← compileProg? current.maxApp prog
  let all := initial ++ [(n - 2, 2, forceThunkCode), (n - 1, 0, initGlobals current.maxApp (n + current.start))] ++ compiled
  let names := makeNameAlist (all.map (fun (loc, _, _) => loc)) prog n original.nextLoc es.length
  pure ({ current with start := n - 1 }, codeSort all, names)

/-- Checked source-shaped closure preprocessing when all three optional
optimizations are disabled. Other configurations fail explicitly; this is not
the unrestricted HOL `compile_common`. -/
def compileCommonNoOpts? (c : Config) (es : List ClosLang.Exp) :
    Option (Config × List (Nat × Nat × ClosLang.Exp)) := do
  if c.doMti || c.doCall then none else
  match c.knownConf with
  | some _ => none
  | none =>
      let next := c.nextLoc + max 1 es.length
      let aligned := if next % 2 = 0 then next else next + 1
      let (next, es) := ClosNumber.renumberList aligned es
      let prog := ClosAnnotate.compile (chainExps c.nextLoc es)
      some ({ c with start := c.nextLoc, nextLoc := next, knownConf := none, callState := (.ln, []) }, prog)

/-- Checked whole closure-to-BVL compilation in the explicitly disabled
optimization configuration. Other configurations are rejected. -/
def compileNoOpts? (c : Config) (es : List ClosLang.Exp) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let (current, prog) ← compileCommonNoOpts? c es
  compilePrepared? c current es prog

/-- Checked closure compilation with multi-argument introduction enabled or
disabled. Known-function and call optimizations are still rejected, and the
multi-argument traversal can fail when its explicit fuel is exhausted. -/
def compileMtiOnlyFuel? (fuel : Nat) (c : Config) (es : List ClosLang.Exp) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let es' ← ClosMti.compileFuel fuel c.doMti c.maxApp es
  let (current, prog) ← compileCommonNoOpts? { c with doMti := false } es'
  compilePrepared? c { current with doMti := c.doMti } es' prog

/-- Checked closure compilation with multi-argument introduction and direct
call conversion. Known-function optimization is still rejected. -/
def compileCallMtiFuel? (fuel : Nat) (c : Config) (es : List ClosLang.Exp) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  if c.knownConf.isSome then failure
  let transformed ← ClosMti.compileFuel fuel c.doMti c.maxApp es
  let next := c.nextLoc + max 1 transformed.length
  let aligned := if next % 2 = 0 then next else next + 1
  let (next, transformed) := ClosNumber.renumberList aligned transformed
  let (transformed, callState) ← ClosCall.compileFuel fuel c.doCall transformed
  let prog := ClosAnnotate.compile (chainExps c.nextLoc transformed ++ callState.2)
  let current := { c with start := c.nextLoc, nextLoc := next, knownConf := none, callState := callState }
  compilePrepared? c current es prog

end Flapjack.Compiler.Backend.ClosToBvl
