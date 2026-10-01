import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsPhysicalInsert
namespace Flapjack.Test.SSALocalsPhysicalInsertParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- Fixture infrastructure discharging the original relation on a singleton source.
private theorem leafPremise {α : Type} (next reg v : Nat) (value : α) (target : Spt α)
    (hm : ¬ isPhyVar reg ∧ reg < next) (ht : sptLookup reg target = some value)
    (hv : isPhyVar v) :
    ssaMapOK next (.ls reg) ∧ ssaLocalsRel next (.ls reg) (.ls value) target ∧ isPhyVar v := by
  refine ⟨?_, ?_, hv⟩
  · intro key val h
    simp only [sptLookup] at h
    split at h
    · cases h; exact hm
    · contradiction
  · change ssaLocalsRelWith (fun o => o.getD 0) next (.ls reg) (.ls value) target
    constructor
    · intro key val h
      simp only [sptLookup] at h
      split at h
      · cases h
        exact (sptMem_iff_lookup reg target).mpr ⟨value, ht⟩
      · contradiction
    · intro key val h
      simp only [sptLookup] at h
      split at h
      · subst key
        cases h
        exact ⟨(sptMem_iff_lookup 0 (.ls reg)).mpr ⟨reg, rfl⟩, by simpa [sptLookup] using ht, by simp [isAllocVar]⟩
      · contradiction
-- Original pi_empty=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ln) (.ln : Spt Bool) (sptInsert 0 true (.ln)) :=
  ssaLocalsRelIgnoreInsert 8 (.ln) (.ln) (.ln) 0 true (by simp [ssaMapOK, ssaLocalsRel, ssaLocalsRelWith, sptLookup, isPhyVar])
-- Original pi_empty_existing=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ln) (.ln : Spt Bool) (sptInsert 2 false (.ls true)) :=
  ssaLocalsRelIgnoreInsert 8 (.ln) (.ln) (.ls true) 2 false (by simp [ssaMapOK, ssaLocalsRel, ssaLocalsRelWith, sptLookup, isPhyVar])
-- Original pi_live=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ls 1) (.ls true : Spt Bool) (sptInsert 0 false (.bn .ln (.ls true))) :=
  ssaLocalsRelIgnoreInsert 8 (.ls 1) (.ls true) (.bn .ln (.ls true)) 0 false (leafPremise 8 1 0 _ (.bn .ln (.ls true)) (by decide) rfl (by decide))
-- Original pi_overwrite=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ls 1) (.ls true : Spt Bool) (sptInsert 0 true (.bs .ln false (.ls true))) :=
  ssaLocalsRelIgnoreInsert 8 (.ls 1) (.ls true) (.bs .ln false (.ls true)) 0 true (leafPremise 8 1 0 _ (.bs .ln false (.ls true)) (by decide) rfl (by decide))
-- Original pi_branch=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ls 1) (.ls true : Spt Bool) (sptInsert 2 true (.bs (.ls false) false (.ls true))) :=
  ssaLocalsRelIgnoreInsert 8 (.ls 1) (.ls true) (.bs (.ls false) false (.ls true)) 2 true (leafPremise 8 1 2 _ (.bs (.ls false) false (.ls true)) (by decide) rfl (by decide))
-- Original pi_invalid=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.bn .ln .ln) (.bn .ln .ln : Spt Bool) (sptInsert 0 true (.bn .ln .ln)) :=
  ssaLocalsRelIgnoreInsert 8 (.bn .ln .ln) (.bn .ln .ln) (.bn .ln .ln) 0 true (by simp [ssaMapOK, ssaLocalsRel, ssaLocalsRelWith, sptLookup, isPhyVar])
-- Original pi_huge=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ls 1) (.ls true : Spt Bool) (sptInsert 1000000000000000000000000000000 false (.bn .ln (.ls true))) :=
  ssaLocalsRelIgnoreInsert 8 (.ls 1) (.ls true) (.bn .ln (.ls true)) 1000000000000000000000000000000 false (leafPremise 8 1 1000000000000000000000000000000 _ (.bn .ln (.ls true)) (by decide) rfl (by decide))
-- Original pi_generic_nat=T; actual full generic theorem application.
example : ssaLocalsRel 8 (.ls 1) (.ls 99 : Spt Nat) (sptInsert 0 777 (.bn .ln (.ls 99))) :=
  ssaLocalsRelIgnoreInsert 8 (.ls 1) (.ls 99) (.bn .ln (.ls 99)) 0 777 (leafPremise 8 1 0 _ (.bn .ln (.ls 99)) (by decide) rfl (by decide))
example : ¬ isPhyVar 1 := by decide
example : ¬ ssaMapOK 8 (.ls 0) := by
  intro h
  exact (h 0 0 rfl).1 (by decide)
end Flapjack.Test.SSALocalsPhysicalInsertParity
