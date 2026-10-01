import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert

namespace Flapjack.Test.SSALocalsInsertParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

example {α : Type} (next : Nat) (ssa : Spt Nat) (source target : Spt α)
    (name : Nat) (value : α)
    (h : ssaLocalsRel next ssa source target ∧ ssaMapOK next ssa ∧ name < next) :
    ssaLocalsRel (next + 4) (sptInsert name next ssa)
      (sptInsert name value source) (sptInsert next value target) :=
  ssaLocalsRelInsert next ssa source target name value h

example : ssaLocalsRel 5 (sptInsert 0 1 .ln)
    (sptInsert 0 false .ln) (sptInsert 1 false .ln) := by
  apply ssaLocalsRelInsert 1 .ln .ln .ln 0 false
  simp [ssaLocalsRel, ssaLocalsRelWith, ssaMapOK, sptLookup]

example : ssaLocalsRel 12 (sptInsert 0 8 (sptFromAList [(1, 5)]))
    (sptInsert 0 false (sptFromAList [(1, true)]))
    (sptInsert 8 false (sptFromAList [(5, true)])) := by
  apply ssaLocalsRelInsert 8 _ _ _ 0 false
  simp [ssaLocalsRel, ssaLocalsRelWith, ssaMapOK, sptMem_iff_lookup,
    sptLookup_sptFromAList, sptAListLookup, isAllocVar, isPhyVar]

end Flapjack.Test.SSALocalsInsertParity
