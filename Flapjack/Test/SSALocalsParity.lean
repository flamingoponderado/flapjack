import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
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
example {α : Type} (next nextOut : Nat) (ssa : Spt Nat) (source target : Spt α)
    (h : ssaLocalsRel next ssa source target) (bound : next ≤ nextOut) :
    ssaLocalsRel nextOut ssa source target :=
  ssaLocalsRelMore next ssa source target nextOut ⟨h, bound⟩
end Flapjack.Test.SSALocalsParity
