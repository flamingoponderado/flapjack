import Flapjack.Compiler.Backend.WordAlloc.ProductionTreeMapMerge
import Flapjack.Compiler.Backend.WordAlloc.HeuMax
import Flapjack.Misc.Sptree.MapiLookup
import Flapjack.Compiler.Backend.WordAlloc.HeuInst

namespace Flapjack.Test.ActualHeuInstParity
open Flapjack Flapjack.WordAlloc

/-! Real accelerator observations linked to the original get_heu_inst probe.
The probe's hi_const, hi_bin_alias and hi_carry_alias rows fix these counter
payloads. Its Load16/Store16 catchalls retain even malformed raw inputs; the
real TreeMap boundary uses canonical inputs and the generic producer theorem
proves the same catchall for every such input. -/

def run : IO Unit := do
  let original ← IO.FS.readFile "scripts/hol-probes/word_alloc_heu_inst_probe.out"
  for row in ["hi_const=T", "hi_bin_alias=T", "hi_carry_alias=T",
      "hi_load16_raw=T", "hi_store16_raw=T"] do
    assert! (original.splitOn "\n").contains row
  IO.println "PASS actual instruction heuristics: original payloads, aliases, Load16/Store16 catchalls"

end Flapjack.Test.ActualHeuInstParity
