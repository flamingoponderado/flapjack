module

public import Flapjack.Compiler.Backend.ClosToBvl.Config
public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosAnnotate.Original

@[expose] public section

/-! Source closure preprocessing before conversion to BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Apply the original whole-program closure preprocessing passes. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_common_def"]
noncomputable def compileCommon (config : Config) (expressions : List ClosLang.Exp) :
    Config × List (Nat × Nat × ClosLang.Exp) :=
  let expressions := ClosMti.compile config.doMti config.maxApp expressions
  let loc := config.nextLoc + max 1 expressions.length
  let loc := if loc % 2 = 0 then loc else loc + 1
  let (next, expressions) := ClosNumber.renumberList loc expressions
  let (known, expressions) := ClosKnown.compileSource config.knownConf expressions
  let (expressions, (globals, auxiliary)) := ClosCall.compile config.doCall expressions
  let program := chainExps config.nextLoc expressions ++ auxiliary
  ({ config with start := config.nextLoc, nextLoc := next, knownConf := known, callState := (globals, auxiliary) },
    ClosAnnotate.compileSource program)

end Flapjack.Compiler.Backend.ClosToBvl
