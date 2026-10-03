import Flapjack.Compiler.Backend.WordCse.Knowledge
import Flapjack.RiscV.WordCse
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Complete five-field lookup relation for native and executed knowledge.
The store observation uses the actual fixed-width store codec and executed
store key. Fact maps use the original reviewed list comparator. This is
Flapjack representation infrastructure without an independent HOL original;
later balanced-map structural/invariant and producer obligations are separate.
No output relation or evaluator result is assumed by this definition. -/
def KnowledgeRel (width : Nat) [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge) : Prop :=
  (∀ register, sptLookup register native.toCanonical = executed.toCanonical[register]?) ∧
  (∀ register, sptLookup register native.toLatest = executed.toLatest[register]?) ∧
  (∀ store, native.getsMem.lookup store =
    executed.getsMem[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]?) ∧
  (∀ key, Misc.BalancedMap.lookup listCmp key native.instrsMem = executed.instrsMem[key]?) ∧
  (∀ key, Misc.BalancedMap.lookup listCmp key native.loadsMem = executed.loadsMem[key]?)

/-- Non-vacuous initial instance of the complete knowledge relation. -/
theorem emptyKnowledgeRel (width : Nat) [NeZero width] :
    KnowledgeRel width emptyData wordCseEmpty := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro key <;> rfl

/-- Actual keep-data test has the original result on related input carriers. -/
theorem keepData_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (register : Nat) :
    keepData native.toCanonical register = wordCseKeepData executed register := by
  simp only [keepData, wordCseKeepData, related.1 register]

/-- Either original invalidation branch establishes all five output fields;
no output relation is a premise. -/
theorem invalidateData_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (register : Nat) :
    KnowledgeRel width (invalidateData native register) (wordCseInvalidate executed register) := by
  unfold invalidateData wordCseInvalidate
  rw [keepData_transport native executed related register]
  split
  · exact related
  · exact emptyKnowledgeRel width

/-- Executed scan on the empty knowledge is absorbing. This is a property of
the actual optimized implementation, not an assumed native equivalence. -/
private theorem scanEmpty (registers : List Nat) :
    wordCseInvalidateRegs wordCseEmpty registers = wordCseEmpty := by
  simp [wordCseInvalidateRegs, wordCseEmpty]

/-- The actual any-scan satisfies the original recursive step on arbitrary
executed input. Once a tracked register is written, every later step remains
empty. This establishes the optimization's behavior instead of assuming it. -/
private theorem scanCons (executed : WordCseKnowledge) (register : Nat)
    (registers : List Nat) :
    wordCseInvalidateRegs executed (register :: registers) =
      wordCseInvalidateRegs (wordCseInvalidate executed register) registers := by
  cases found : executed.toCanonical[register]? with
  | none =>
      have unchanged : wordCseInvalidate executed register = executed := by
        simp [wordCseInvalidate, wordCseKeepData, found]
      rw [unchanged]
      simp only [wordCseInvalidateRegs, List.any_cons, found, Option.isSome_none,
        Bool.false_or]
  | some value =>
      have discarded : wordCseInvalidate executed register = wordCseEmpty := by
        simp [wordCseInvalidate, wordCseKeepData, found]
      rw [discarded, scanEmpty]
      simp only [wordCseInvalidateRegs, List.any_cons, found, Option.isSome_some,
        Bool.true_or, if_true]

/-- Whole original recursive invalidation is preserved by the executed
absorbing any-scan, for arbitrary lists and all five related knowledge fields.
This is Flapjack API transport, not full CSE evaluation or production routing. -/
theorem invalidateRegs_transport {width : Nat} [NeZero width]
    (native : Knowledge) (executed : WordCseKnowledge)
    (related : KnowledgeRel width native executed) (registers : List Nat) :
    KnowledgeRel width (invalidateRegs native registers)
      (wordCseInvalidateRegs executed registers) := by
  induction registers generalizing native executed with
  | nil => simpa [invalidateRegs, wordCseInvalidateRegs] using related
  | cons register registers ih =>
      rw [invalidateRegs, scanCons]
      exact ih _ _ (invalidateData_transport native executed related register)

end Flapjack.Compiler.Backend.WordCse
