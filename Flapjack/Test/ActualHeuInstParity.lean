import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicInstructions

namespace Flapjack.Test.ActualHeuInstParity
open Flapjack Flapjack.WordAlloc

/-! Real accelerator observations linked to the original get_heu_inst probe.
The probe's hi_const, hi_bin_alias and hi_carry_alias rows fix these counter
payloads. Its Load16/Store16 catchalls retain even malformed raw inputs; the
real TreeMap boundary uses canonical inputs and the generic producer theorem
proves the same catchall for every such input. -/

def initial : WordHeuristicCountMap := {}

def observe (instruction : WordInst (BitVec 64)) : List (Nat × HeuData) :=
  (wordHeuristicInstFast instruction initial).toNatInfoMap.map
    (fun entry => (entry.1, heuristicCountsToNative entry.2))

-- Original hi_const, hi_bin_alias, hi_carry_alias payloads.
example : observe (.const 1 7) = [(1, (1,0,0,0,0))] := by decide +kernel
example : observe (.arith (.binOp .add 1 1 (.reg 1))) =
    [(1, (0,1,0,2,0))] := by decide +kernel
example : observe (.arith (.cakeAddCarry 1 1 1 1)) =
    [(1, (0,2,0,3,0))] := by decide +kernel

def ordinary16 : List (WordInst (BitVec 64)) :=
  [.mem .load16 1 99, .mem .store16 1 99,
   .memOffset .load16 1 99 7, .memOffset .store16 1 99 7]

example (counts : WordHeuristicCountMap) :
    heuristicCountMapToNative (wordHeuristicInstFast
      (.memOffset .load16 1 99 (7 : BitVec 64)) counts) =
      heuristicCountMapToNative counts := by
  simpa only [getHeuInst] using heuristicInst_production
    (.memOffset .load16 1 99 (7 : BitVec 64)) (.mem .load16 1 (.addr 99 7)) rfl counts

def run : IO Unit := do
  let original ← IO.FS.readFile "scripts/hol-probes/word_alloc_heu_inst_probe.out"
  for row in ["hi_const=T", "hi_bin_alias=T", "hi_carry_alias=T",
      "hi_load16_raw=T", "hi_store16_raw=T"] do
    assert! (original.splitOn "\n").contains row
  assert! observe (.const 1 7) == [(1, (1,0,0,0,0))]
  assert! observe (.arith (.binOp .add 1 1 (.reg 1))) == [(1, (0,1,0,2,0))]
  assert! observe (.arith (.cakeAddCarry 1 1 1 1)) == [(1, (0,2,0,3,0))]
  let counts := wordHeuristicInstFast (.const 1 (7 : BitVec 64)) initial
  for instruction in ordinary16 do
    assert! (wordHeuristicInstFast instruction counts).toNatInfoMap == counts.toNatInfoMap
    assert! wordHeuristicInst instruction counts.toNatInfoMap == counts.toNatInfoMap
  IO.println "PASS actual instruction heuristics: original payloads, aliases, Load16/Store16 catchalls"

#eval run

end Flapjack.Test.ActualHeuInstParity
