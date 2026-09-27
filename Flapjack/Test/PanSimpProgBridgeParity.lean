/-
Parity between the exact-to-production `pan_simp` codec bridges in
`Flapjack/Pancake/Proofs/PanSimp/ProgOfHOL.lean` and the checked-in direct
original-HOL EVAL rows:

* `scripts/hol-probes/pan_simp_compile_probe.out` (`pan_simp$compile`)
* `scripts/hol-probes/seq_assoc_probe.out` (`pan_simp$seq_assoc`)
* `scripts/hol-probes/ret_to_tail_probe.out` (`pan_simp$ret_to_tail`)

The expected production values are exactly the oracle rows: `Skip`, `Tick`,
`Seq Tick Tick`, and `Skip` for `ret_to_tail`. Because the executed pipeline
(`Flapjack/Pipeline.lean`, `Flapjack/PerfFrontMain.lean`) runs the production
`panSimpDecls`, these bridge rows connect the tagged exact HOL `pan_simp`
definitions to the executed pass.
-/
import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL

namespace Flapjack.Test.PanSimpProgBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

/-- HOL oracle `skip=Skip` (`pan_simp_compile_probe.out`). -/
theorem compile_skip :
    progOfHOL (panSimpCompileHOL (.skip : ProgHOL 8)) = (.skip : Prog (BitVec 8)) := by
  rw [progOfHOL_panSimpCompileHOL]
  simp [progOfHOL, panSimpProg, seqAssoc, retToTail]

/-- HOL oracle `seq_skip_tick=Tick` (`pan_simp_compile_probe.out`). -/
theorem compile_seq_skip_tick :
    progOfHOL (panSimpCompileHOL (.seq (.skip : ProgHOL 8) .tick)) =
      (.tick : Prog (BitVec 8)) := by
  rw [progOfHOL_panSimpCompileHOL]
  simp [progOfHOL, panSimpProg, seqAssoc, retToTail]

/-- HOL oracle `skip_skip=Skip` (`seq_assoc_probe.out`). -/
theorem seqAssoc_skip_skip :
    progOfHOL (seqAssocHOL (.skip : ProgHOL 8) .skip) = (.skip : Prog (BitVec 8)) := by
  rw [progOfHOL_seqAssocHOL]
  simp [progOfHOL, seqAssoc]

/-- HOL oracle `tick_skip=Tick` (`seq_assoc_probe.out`). -/
theorem seqAssoc_tick_skip :
    progOfHOL (seqAssocHOL (.tick : ProgHOL 8) .skip) = (.tick : Prog (BitVec 8)) := by
  rw [progOfHOL_seqAssocHOL]
  simp [progOfHOL, seqAssoc]

/-- HOL oracle `tick_seq_skip_tick=Seq Tick Tick` (`seq_assoc_probe.out`). -/
theorem seqAssoc_tick_seq_skip_tick :
    progOfHOL (seqAssocHOL (.tick : ProgHOL 8) (.seq .skip .tick)) =
      (.seq .tick .tick : Prog (BitVec 8)) := by
  rw [progOfHOL_seqAssocHOL]
  simp [progOfHOL, seqAssoc, smartSeq]

/-- HOL oracle `skip=Skip` (`ret_to_tail_probe.out`). -/
theorem retToTail_skip :
    progOfHOL (retToTailHOL (.skip : ProgHOL 8)) = (.skip : Prog (BitVec 8)) := by
  rw [progOfHOL_retToTailHOL]
  simp [progOfHOL, retToTail]

def runChecks : IO Bool := do
  IO.println "PASS pan_simp exact-to-production bridge rows vs pan_simp compile/seq_assoc/ret_to_tail oracles"
  pure true

end Flapjack.Test.PanSimpProgBridgeParity
