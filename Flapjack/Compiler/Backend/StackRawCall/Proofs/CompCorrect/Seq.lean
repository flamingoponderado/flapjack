import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Optimized
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape

namespace Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase

/-- Canonical roundtrip of the actual imported evaluator state. Representation
infrastructure, with no separate HOL declaration or duplicate state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Seq case175-282. Both original existential simulations retain
the three source premises and only the genuine evaluate_ind hypotheses: first
at the fixed source, second after the actual first NONE run. The compiler's
fallback and every equal/less/greater-frame optimization are covered, including
zero clock, allocation failure, bad function returns and arbitrary body outcomes.
The optimized target Call execution is derived from the second IH; no extra
callee IH, target-run law, successful optimization or final relation is assumed.
The original timeout/Halt Word2 stackspace exceptions remain unchanged.
Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info (.seq first second)) info target post result ∧
    SimulationResult (comp info (.seq first second)) info target post result := by
  have standard := simulateStandardSeq first second info source target post result
    firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change SimulationResult (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
          simpa only [compSeq, destCase, frame] using
            simulateOptimizedSeq released allocated dest info source target post result
              frame secondIH hypothesis

end Flapjack.Compiler.Backend.StackRawCall.SeqCase
