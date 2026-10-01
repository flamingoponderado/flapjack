import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMap

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Physical target registers cannot occur in the image of an SSA map satisfying
its original bound predicate. The payload type remains fully generic. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_ignore_insert"]
theorem ssaLocalsRelIgnoreInsert {α : Type} (next : Nat) (ssa : Spt Nat)
    (source target : Spt α) (v : Nat) (a : α)
    (h : ssaMapOK next ssa ∧ ssaLocalsRel next ssa source target ∧ isPhyVar v) :
    ssaLocalsRel next ssa source (sptInsert v a target) := by
  rcases h with ⟨hm, hr, hv⟩
  change ssaLocalsRelWith (fun value => value.getD 0) next ssa source target at hr
  change ssaLocalsRelWith (fun value => value.getD 0) next ssa source (sptInsert v a target)
  refine ⟨?_, ?_⟩
  · intro x y hx
    have hne : y ≠ v := by
      intro he
      subst y
      exact (hm x v hx).1 hv
    obtain ⟨value, hvalue⟩ := (sptMem_iff_lookup y target).mp (hr.1 x y hx)
    apply (sptMem_iff_lookup y (sptInsert v a target)).mpr
    exact ⟨value, by simpa only [sptLookup_sptInsert_ne _ _ _ _ hne] using hvalue⟩
  · intro x value hx
    rcases hr.2 x value hx with ⟨hd, ht, hn⟩
    obtain ⟨reg, hreg⟩ := (sptMem_iff_lookup x ssa).mp hd
    have hne : reg ≠ v := by
      intro he
      subst reg
      exact (hm x v hreg).1 hv
    refine ⟨hd, ?_, hn⟩
    simpa only [hreg, Option.getD_some, sptLookup_sptInsert_ne _ _ _ _ hne] using ht

end Flapjack.Compiler.Backend.WordAlloc
