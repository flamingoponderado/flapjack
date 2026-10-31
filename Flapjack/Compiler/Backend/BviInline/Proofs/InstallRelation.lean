import Flapjack.Compiler.Backend.BviInline.Proofs.StateRelation
import Flapjack.Compiler.Backend.BviInline.Proofs.ProgramRelation

/-! State invariants for dynamically installed BVI code. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem BackendProps

/-- Flapjack infrastructure: installing fresh, distinctly labelled code and
advancing the oracle preserves the inliner state relation. The next cache is
the one produced by the compiler, as required by successful installation. -/
theorem inStateRel_after_install {C F : Type}
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F) (target : BviState C F)
    (related : InStateRel source target)
    (distinct : ((source.compileOracle 0).2.map Prod.fst).Nodup)
    (fresh : ∀ name, sptDomain source.code name → name ∉ (source.compileOracle 0).2.map Prod.fst)
    (nextCache : (source.compileOracle 1).1.1 =
      (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).1) :
    InStateRel
      { source with
        code := sptUnion source.code (sptFromAList (source.compileOracle 0).2)
        compileOracle := fun n => source.compileOracle (n + 1) }
      { target with
        code := sptUnion target.code
          (sptFromAList (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  rcases related with ⟨refs, clock, global, ffi, oracle, cache, compiler, domains, codeRel⟩
  have targetFresh : ∀ name, sptMem name target.code → name ∉ (source.compileOracle 0).2.map Prod.fst := by
    intro name present
    apply fresh name
    rwa [← domains]
  have range := inlineAllSource_cache_subspt (source.compileOracle 0).2
    (source.compileOracle 0).1.1 target.code distinct cache targetFresh
  have codes := inlineAllSource_union_related (source.compileOracle 0).2
    (source.compileOracle 0).1.1 source.code target.code distinct cache targetFresh codeRel
  have newDomains : sptDomain (sptUnion target.code
      (sptFromAList (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)) =
      sptDomain (sptUnion source.code (sptFromAList (source.compileOracle 0).2)) := by
    rw [sptDomain_sptUnion, sptDomain_sptUnion, domains]
    funext name
    apply propext
    change sptDomain source.code name ∨ sptMem name (sptFromAList
      (inlineAllSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2) ↔
      sptDomain source.code name ∨ sptMem name (sptFromAList (source.compileOracle 0).2)
    rw [BviTailrec.sptFromAList_mem_iff, BviTailrec.sptFromAList_mem_iff, inlineAllSource_names]
  refine ⟨refs, clock, global, ffi, ?_, ?_, compiler, newDomains, codes⟩
  · funext n
    exact congrFun oracle (n + 1)
  · simpa [nextCache] using range

end Flapjack.Compiler.Backend.BviInline
