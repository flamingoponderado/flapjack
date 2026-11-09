module

public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.ClosToBvl.Compile
public import Flapjack.Compiler.Backend.ClosToBvl.Names
public import Flapjack.Compiler.Backend.ClosToBvl.Sort
public import Flapjack.Compiler.Backend.ClosToBvl.Stubs
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Compiler.Backend.ClosCall
public import Flapjack.Compiler.Backend.ClosKnown.Compile

@[expose] public section

/-! Checked closure-to-BVL assembly after closure preprocessing. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Basis.Pure.MlString

/-- Assemble a prepared closure program with its application, force and
initialization stubs. The caller supplies the result of HOL's `compile_common`;
checked expression lowering succeeds by `Proofs/Total.lean`, but correspondence
of preprocessing remains unproved, so this is not the full HOL `compile` definition. -/
def compilePrepared? (original current : Config) (es : List ClosLang.Exp)
    (prog : List (Nat × Nat × ClosLang.Exp)) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let n := numStubs current.maxApp
  let initial := (sptToAList (initCode current.maxApp)).map fun (loc, arity, code) => (loc, arity, code)
  let compiled ← compileProg? current.maxApp prog
  let all := initial ++ [(n - 2, 2, forceThunkCode), (n - 1, 0, initGlobals current.maxApp (n + current.start))] ++ compiled
  let names := makeNameAlist (all.map (fun (loc, _, _) => loc)) prog n original.nextLoc es.length
  pure ({ current with start := n - 1 }, codeSort all, names)

/-- Checked closure compilation with multi-argument introduction,
known-function optimization and direct-call conversion. -/
def compileCallMtiFuel? (fuel : Nat) (c : Config) (es : List ClosLang.Exp) :
    Option (Config × List (Nat × Nat × Bvl.Exp) × Spt MlString) := do
  let transformed ← ClosMti.compileFuel fuel c.doMti c.maxApp es
  let next := c.nextLoc + max 1 transformed.length
  let aligned := if next % 2 = 0 then next else next + 1
  let (next, transformed) := ClosNumber.renumberList aligned transformed
  let (known, transformed) ← ClosKnown.compileFuel fuel c.knownConf transformed
  let (transformed, callState) ← ClosCall.compileFuel fuel c.doCall transformed
  let prog := ClosAnnotate.compile (chainExps c.nextLoc transformed ++ callState.2)
  let current := { c with start := c.nextLoc, nextLoc := next, knownConf := known, callState := callState }
  compilePrepared? c current es prog

end Flapjack.Compiler.Backend.ClosToBvl
