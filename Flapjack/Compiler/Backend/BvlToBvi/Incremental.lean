import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BvlInline
import Flapjack.Compiler.Backend.BviTailrec.Rewrite
import Flapjack.Compiler.Backend.BviTmc
import Flapjack.Compiler.Backend.BviInline

/-! Checked incremental BVL-to-BVI optimization pipeline. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Run all incremental BVL/BVI passes, threading both inline caches and all
three fresh-name counters. The component traversals may exhaust fuel and
their correspondence to the HOL incremental pipeline remains open. -/
def compileIncAllFuel (fuel : Nat) (config : Config) (program : List (Nat × Nat × Bvl.Exp)) :
    Option (Config × List (Nat × Nat × Bvi.Exp)) := do
  let (inlines, program) ← BvlInline.compileIncFuel fuel config.inlineSizeLimit config.expCut
    config.splitMainAtSeq config.inlines program
  let (next1, program) ← compileIncFuel fuel fuel config.nextName1 program
  let (next2, program) ← BviTailrec.compileProgFuel fuel config.doTailrec config.nextName2 program
  let (next3, program) ← BviTmc.compileProgFuel fuel config.doTmc config.nextName3 program
  let (bviInlines, program) ← BviInline.compileIncFuel fuel config.bviInlines program
  let updated := { config with inlines := inlines, nextName1 := next1, nextName2 := next2, nextName3 := next3, bviInlines := bviInlines }
  pure (updated, program)

end Flapjack.Compiler.Backend.BvlToBvi
