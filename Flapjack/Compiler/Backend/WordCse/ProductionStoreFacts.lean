import Flapjack.Compiler.Backend.WordCse.ProductionKnowledge
import Std.Data.TreeMap.Lemmas

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Actual store keys are collision-free on the complete original carrier.
The phantom machine-word width does not change the fixed five-bit Temp payload.
Flapjack codec infrastructure, not an independently declared HOL theorem. -/
theorem storeCode_injective {width : Nat} [NeZero width] :
    Function.Injective (fun store : WordStoreHOL =>
      wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))) := by
  intro first second same
  cases first <;> cases second <;>
    simp [wordStoreFromHOL, wordCseStoreCode, WordCseHash.hash, wordToNum] at same ⊢
  all_goals first
    | omega
    | exact BitVec.eq_of_toNat_eq same

/-- Original association-list cons and actual ordered-map insertion have the
same lookup observations, including repeated-store overwrite. Only the input
observation is assumed; the output correspondence is derived. -/
theorem storeFacts_insert_transport {width : Nat} [NeZero width]
    (native : List (WordStoreHOL × Nat)) (executed : WordCseRegMap)
    (related : ∀ store, native.lookup store =
      executed[wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))]?)
    (store : WordStoreHOL) (value : Nat) :
    ∀ observed, ((store, value) :: native).lookup observed =
      (executed.insert
        (wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width))) value)[wordCseStoreCode (wordStoreFromHOL observed : WordStore (BitVec width))]? := by
  intro observed
  by_cases same : store = observed
  · subst observed
    simp [List.lookup]
  · have keysDifferent :
        wordCseStoreCode (wordStoreFromHOL store : WordStore (BitVec width)) ≠
        wordCseStoreCode (wordStoreFromHOL observed : WordStore (BitVec width)) :=
      fun equal => same (storeCode_injective equal)
    simp only [Std.TreeMap.getElem?_insert, Nat.compare_eq_eq, keysDifferent, if_false]
    have different : (observed == store) = false := by
      exact beq_eq_false_iff_ne.mpr (Ne.symm same)
    simpa [List.lookup, different] using related observed

end Flapjack.Compiler.Backend.WordCse
