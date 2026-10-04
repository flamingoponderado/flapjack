import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.Semantics.WordSem.State

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full state-shaped SSA map replacement. Original inferred types are
`st : (α, β, γ) state` and `cst : (α, δ, ε) state`: only the word
dimension is shared. The four code/FFI carrier types stay independent.
No finite-map state field is traversed by this relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaEqRelSwap {width : Nat} [NeZero width]
    {C₁ F₁ C₂ F₂ : Type} (next : Nat) (ssaLeft ssaRight : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) :
    ssaLocalsRel next ssaRight source.locals target.locals ∧
      sptDomain ssaLeft = sptDomain ssaRight ∧
      (∀ key, sptLookup key ssaLeft = sptLookup key ssaRight) →
    ssaLocalsRel next ssaLeft source.locals target.locals := by
  rintro ⟨relation, domains, lookups⟩
  rcases relation with ⟨mapped, matching⟩
  refine ⟨?_, ?_⟩
  · intro key value found
    exact mapped key value ((lookups key).symm.trans found)
  · intro key value found
    rcases matching key value found with ⟨domain, lookup, bound⟩
    refine ⟨?_, ?_, bound⟩
    · change sptDomain ssaLeft key
      rw [domains]
      exact domain
    · simpa only [lookups key] using lookup

end Flapjack.Compiler.Backend.WordAlloc
