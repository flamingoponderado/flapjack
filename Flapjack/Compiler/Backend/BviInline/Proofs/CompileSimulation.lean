import Flapjack.Compiler.Backend.BviInline.Proofs.EvaluateInduction

/-! Initial-state and whole-program BVI inlining simulation. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BackendProps

/-- Flapjack infrastructure: starting with an empty inlining cache produces
related initial states when the oracle begins with the resulting cache and
program labels are distinct. HOL carrier review remains pending. -/
theorem inline_initial_state_rel {C F : Type} (program output : List (Nat × Nat × Bvi.Exp))
    (cache : Spt (Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (ffi : HolFfiState F) (compiler : BviSem.Compiler C) (clock : Nat)
    (run : inlineAllSource .ln program = (cache, output))
    (oracleCache : (oracle 0).1.1 = cache) (distinct : (program.map Prod.fst).Nodup) :
    InStateRel (initialState ffi (sptFromAList program) oracle (inCc compiler) clock)
      (initialState ffi (sptFromAList output) (inCo oracle) compiler clock) := by
  have emptySubset : sptSubspt (.ln : Spt (Nat × Bvi.Exp)) .ln := by
    rw [sptSubsptLookup]
    simp [sptLookup]
  have disjoint : ∀ key, sptMem key (.ln : Spt (Nat × Bvi.Exp)) → key ∉ program.map Prod.fst := by
    intro key present
    simp [sptMem, sptDomain, sptLookup] at present
  have range := inlineAllSource_cache_subspt program .ln .ln distinct emptySubset disjoint
  have names := inlineAllSource_names program .ln
  have codeRelation := inlineAllSource_related program .ln .ln distinct emptySubset disjoint
  have outputNames : output.map Prod.fst = program.map Prod.fst := by simpa [run] using names
  have cacheSub : sptSubspt cache (sptFromAList output) := by simpa [run, sptUnion] using range
  have domains : sptDomain (sptFromAList output) = sptDomain (sptFromAList program) := by
    funext key
    apply propext
    change sptMem key (sptFromAList output) ↔ sptMem key (sptFromAList program)
    rw [BviTailrec.sptFromAList_mem_iff, BviTailrec.sptFromAList_mem_iff, outputNames]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, domains, ?_⟩
  · simpa [initialState, oracleCache] using cacheSub
  · intro name arity body found
    have association : sptAListLookup name program = some (arity, body) := by
      simpa [initialState, sptLookup_sptFromAList] using found
    obtain ⟨transformed, outputFound, relation⟩ := codeRelation name arity body association
    refine ⟨transformed, ?_, ?_⟩
    · simpa [initialState, sptLookup_sptFromAList, run] using outputFound
    · simpa [initialState, sptUnion, run] using relation

/-- Flapjack infrastructure: running the initial call after the inlining
stage preserves its non-type-error result and produces related states. This
does not yet include the subsequent tick-removal stage. -/
theorem evaluate_inline_compile {C F : Type} (program output : List (Nat × Nat × Bvi.Exp))
    (cache : Spt (Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (ffi : HolFfiState F) (compiler : BviSem.Compiler C) (clock start : Nat)
    (result : BviResult) (sourceNext : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (run : inlineAllSource .ln program = (cache, output))
    (oracleCache : (oracle 0).1.1 = cache) (distinct : (program.map Prod.fst).Nodup)
    (evaluation : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (inCc compiler) clock) = (result, sourceNext))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList output) (inCo oracle) compiler clock) = (result, targetNext) ∧
      InStateRel sourceNext targetNext := by
  apply EvaluateCases.evaluate_inline_result _ _ _ _ sourceNext _ result
    (inline_initial_state_rel program output cache oracle ffi compiler clock run oracleCache distinct)
    _ evaluation notType
  exact .cons (expRel_refl _ _) .nil

/-- Flapjack infrastructure: the production fuelled inlining stage has the
same initial-call simulation, for any supplied fuel. The later tick cleanup
still requires its separate semantics proof. -/
theorem evaluate_inlineFuel_compile {C F : Type} (fuel : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (cache : Spt (Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle (Spt (Nat × Bvi.Exp) × C))
    (ffi : HolFfiState F) (compiler : BviSem.Compiler C) (clock start : Nat)
    (result : BviResult) (sourceNext : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (run : inlineAllFuel fuel .ln program = some (cache, output))
    (oracleCache : (oracle 0).1.1 = cache) (distinct : (program.map Prod.fst).Nodup)
    (evaluation : evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList program) oracle (inCc compiler) clock) = (result, sourceNext))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ targetNext, evaluate [.call 0 (some start) [] none] []
      (initialState ffi (sptFromAList output) (inCo oracle) compiler clock) = (result, targetNext) ∧
      InStateRel sourceNext targetNext := by
  have sourceRun : inlineAllSource .ln program = (cache, output) := by
    have equality := inlineAllFuel_eq_source fuel .ln program
    rw [run] at equality
    exact (Option.some.inj equality).symm
  exact evaluate_inline_compile program output cache oracle ffi compiler clock start result sourceNext
    sourceRun oracleCache distinct evaluation notType

end Flapjack.Compiler.Backend.BviInline
