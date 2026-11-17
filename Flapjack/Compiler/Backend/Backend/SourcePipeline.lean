module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
public import Flapjack.Compiler.Backend.SourceToFlat.ToClos
public import Flapjack.Compiler.Backend.SourceToSource
public import Flapjack.Compiler.Backend.FlatToClos.Compile
public import Flapjack.Compiler.Backend.ClosToBvl.WholeProgram
public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline
public import Flapjack.Compiler.Backend.BviToData.CompileSource
public import Flapjack.Compiler.Backend.DataToWord.Names
public import Flapjack.Compiler.Backend.WordToStack.StubNames
public import Flapjack.Compiler.Backend.StackAlloc.StubNames
public import Flapjack.Compiler.Backend.StackRemove.StubNames

@[expose] public section

-- The existing `Backend.Backend` namespace mirrors the HOL backend theory.
set_option linter.dupNamespace false

/-! The source compiler's backend pipeline up to data language. -/
namespace Flapjack.Compiler.Backend.Backend
open Flapjack Flapjack.Basis.Pure.MlString

/-- Run source let-lifting and source-to-flat compilation. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_flat_def"]
def toFlat (c : Config) (p : List AstHOL.Dec) : Config × List FlatLang.Exp :=
  let p := SourceToSource.compile p
  let (sourceConf, p) := SourceToFlat.compileTotal c.sourceConf p
  ({ c with sourceConf }, p)

/-- Continue source compilation through closure conversion. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_clos_def"]
def toClos (c : Config) (p : List AstHOL.Dec) : Config × List ClosLang.Exp :=
  let (c, p) := toFlat c p
  (c, FlatToClos.compileProg p)

/-- The executable source-to-closure entry point returns this pipeline's
    closure program and updated source configuration. This is a Flapjack
    connection lemma; it is not a separate HOL theorem. -/
theorem toClos_executable (fuel : Nat) (c : Config) (p : List AstHOL.Dec) :
    SourceToFlat.compileCakeToClosFuel fuel c.sourceConf p =
      some ((toClos c p).1.sourceConf, (toClos c p).2) := by
  simp [SourceToFlat.compileCakeToClosFuel, SourceToFlat.compileToClosFuel, toClos, toFlat]

/-- Continue through closure optimization and BVL code generation. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_bvl_def"]
noncomputable def toBvl (c : Config) (p : List AstHOL.Dec) :
    Config × List (Nat × Nat × Bvl.Exp) × Spt MlString :=
  let (c, p) := toClos c p
  let (closConf, p, names) := ClosToBvl.compileSource c.closConf p
  ({ c with closConf }, p, names)

/-- Continue through BVI generation and add the backend stub names. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_bvi_def"]
noncomputable def toBvi (c : Config) (p : List AstHOL.Dec) :
    Config × List (Nat × Nat × Bvi.Exp) × Spt MlString :=
  let (c, p, names) := toBvl c p
  let (start, p, inlines, bviInlines, n1, n2, n3, names) :=
    BvlToBvi.compileSource c.closConf.start c.bvlConf names p
  let names := sptUnion (sptFromAList (DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ())) names
  let c := { c with closConf := { c.closConf with start } }
  let c := { c with bvlConf := { c.bvlConf with
    inlines, bviInlines, nextName1 := n1, nextName2 := n2, nextName3 := n3 } }
  (c, p, names)

/-- Continue through BVI-to-data lowering. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_data_def"]
noncomputable def toData (c : Config) (p : List AstHOL.Dec) :
    Config × List (Nat × Nat × DataLang.Prog) × Spt MlString :=
  let (c, p, names) := toBvi c p
  (c, BviToData.compileProg p, names)

end Flapjack.Compiler.Backend.Backend
