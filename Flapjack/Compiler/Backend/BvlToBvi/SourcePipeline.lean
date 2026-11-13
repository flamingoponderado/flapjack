module

public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BvlToBvi.Names
public import Flapjack.Compiler.Backend.BvlToBvi.Config
public import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviInline.Source

@[expose] public section

/-! Source-shaped composition of the complete BVL-to-BVI compiler. -/
namespace Flapjack.Compiler.Backend.BvlToBvi
open Flapjack.Basis.Pure.MlString

/-- Run the original whole-program BVL-to-BVI pipeline. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "compile_def"]
def compileSource (start : Nat) (c : Config) (names : Spt MlString)
    (prog : List (Nat × Nat × Bvl.Exp)) :
    Nat × List (Nat × Nat × Bvi.Exp) × Spt (Nat × Bvl.Exp) × Spt (Nat × Bvi.Exp) ×
      Nat × Nat × Nat × Spt MlString :=
  let (inlines, prog) := BvlInline.compileProg c.inlineSizeLimit c.splitMainAtSeq c.expCut prog
  let (loc, code, n1) := compileProgSource start 0 prog
  let (n2, code) := BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) code
  let (n3, code) := BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) code
  let (bviInlines, code) := BviInline.compileProgSource code
  (loc, code, inlines, bviInlines, n1, n2, n3, getNames (code.map Prod.fst) names)


end Flapjack.Compiler.Backend.BvlToBvi
