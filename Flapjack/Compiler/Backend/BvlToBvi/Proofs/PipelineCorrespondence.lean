module

public import Flapjack.Compiler.Backend.BvlToBvi.SourcePipeline
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialStateRel
public import Flapjack.Compiler.Backend.BviInline.Proofs.SourceCorrespondence

@[expose] public section

/-! The former bounded composition executes the original total pipeline. -/
namespace Flapjack.Compiler.Backend.BvlToBvi
open Flapjack.Basis.Pure.MlString

/-- All constituent bounded interfaces return the source pipeline result for every fuel. -/
theorem compileFuelPipeline_eq_source (fuel start : Nat) (c : Config) (names : Spt MlString)
    (prog : List (Nat × Nat × Bvl.Exp)) :
    (do
      let (inlines, prog) ← BvlInline.compileProgFuel fuel c.inlineSizeLimit c.expCut c.splitMainAtSeq prog
      let (loc, code, n1) ← compileProgFuel fuel fuel start 0 prog
      let (n2, code) ← BviTailrec.compileProgFuel fuel c.doTailrec (bvlNumStubs + 2) code
      let (n3, code) ← BviTmc.compileProgFuel fuel c.doTmc (bvlNumStubs + 3) code
      let (bviInlines, code) ← BviInline.compileProgFuel fuel code
      pure (loc, code, inlines, bviInlines, n1, n2, n3, getNames (code.map Prod.fst) names)) =
    some (compileSource start c names prog) := by
  simp [compileSource, compileProgSource, compileIncSource, ← allocGlobCount_eq_globalCountList.2, BvlInline.compileProgFuel_eq_compileProg,
    Proofs.compileProgFuel_eq_source, BviInline.compileProgSource, BviTailrec.compileProgFuel_eq_source,
    BviTmc.compileProgFuel_eq_source, BviInline.compileProgFuel_eq_source]

end Flapjack.Compiler.Backend.BvlToBvi
