import Flapjack.Compiler.Backend.WordCse.Join
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Misc.BalancedMap.InsertCorrect

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Misc.BalancedMap

/-- Invariant-only induction for the literal accumulator traversal. This is
Flapjack proof infrastructure, not the original accumulator theorem, whose
additional arbitrary semantic-key lookup conclusion remains separate work. -/
private theorem accumulatorInvariant {α : Type} [DecidableEq α]
    (second first accumulator : Map (List Nat) α)
    (firstValid : invariant listCmp first)
    (accumulatorValid : invariant listCmp accumulator) :
    invariant listCmp (bmInterEqAcc second first accumulator) := by
  induction first generalizing accumulator with
  | tip => exact accumulatorValid
  | bin size key value left right leftIH rightIH =>
      have leftValid := firstValid.2.2.2.2.1
      have rightValid := firstValid.2.2.2.2.2
      have insertedValid : invariant listCmp
          (if lookup listCmp key second = some value then
            insert listCmp key value accumulator else accumulator) := by
        split
        · exact (insertThm listCmp key value accumulator
            ⟨goodCmpListCmp, accumulatorValid⟩).1
        · exact accumulatorValid
      exact leftIH _ leftValid (rightIH _ rightValid insertedValid)

/-- Full original intersection invariant for arbitrary fact payloads and
native trees. Exactly the two input invariants imply the output invariant;
there are no lookup, output-relation, successful-run or fixed-value premises. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "invariant_bm_inter_eq"]
theorem invariantBmInterEq {α : Type} [DecidableEq α]
    (first second : Map (List Nat) α)
    (valid : invariant listCmp first ∧ invariant listCmp second) :
    invariant listCmp (bmInterEq first second) :=
  accumulatorInvariant second first empty valid.1 (by simp [empty, invariant])

end Flapjack.Compiler.Backend.WordCse
