import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
namespace Flapjack.Test.SSALocalsParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Same arbitrary-tree/generic-Bool inputs as the original source-clause probe.
example : ssaLocalsRel 0 .ln (.ln : Spt Bool) .ln := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup, isAllocVar]
example : ssaLocalsRel 0 (.ls 5) (.ls true) (sptFromAList [(5,true)]) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup_sptFromAList, sptAListLookup, sptLookup, isAllocVar]
example : ¬ ssaLocalsRel 0 .ln (.ls true) (.ls true) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup, isAllocVar]
example : ¬ ssaLocalsRel 0 (.ls 5) (.ln : Spt Bool) .ln := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup, isAllocVar]
example : ¬ ssaLocalsRel 0 (.ls 5) (.ls true) (sptFromAList [(5,false)]) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup_sptFromAList, sptAListLookup, sptLookup, isAllocVar]
example : ¬ ssaLocalsRel 1 (sptFromAList [(1,5)]) (sptFromAList [(1,true)]) (sptFromAList [(5,true)]) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup_sptFromAList, sptAListLookup, isAllocVar]
example : ssaLocalsRel 2 (sptFromAList [(1,5)]) (sptFromAList [(1,true)]) (sptFromAList [(5,true)]) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup_sptFromAList, sptAListLookup, isAllocVar]
example : ssaLocalsRel 0 (.bn .ln .ln) (.ln : Spt Bool) (.bn .ln .ln) := by
  simp [ssaLocalsRel, ssaLocalsRelWith, sptMem_iff_lookup,
    sptLookup, isAllocVar]
end Flapjack.Test.SSALocalsParity
