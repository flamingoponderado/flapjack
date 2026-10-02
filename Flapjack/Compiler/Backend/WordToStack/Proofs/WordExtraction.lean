import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Misc.Option

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Flapjack factoring for the anonymous successful-Word projection in HOL's
guarded theorem. No separate HOL declaration exists. The other constructors
use the already reviewed option THE; no new default is introduced. The success
guard below proves every projected input is SOME Word, so those branches are
unreachable and no cross-language claim about their default value is needed. -/
noncomputable def successfulWordProjection {width : Nat} [NeZero width]
    (value : Option (WordLocW width)) : BitVec width :=
  holThe (match value with
    | some (.word word) => some word
    | _ => none)

/-- Full source result: every member of a successfully extracted list is a
SOME Word. No bounds, payload equality instance or target premise is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "the_words_EVERY_IS_SOME_Word" (words_as_type_indexed_bitvec)]
theorem theWordsEveryIsSomeWord {width : Nat} [NeZero width]
    (values : List (Option (WordLocW width))) (words : List (BitVec width))
    (success : theWords values = some words) :
    ∀ value, value ∈ values → ∃ word, value = some (.word word) := by
  induction values generalizing words with
  | nil => simp
  | cons value values ih =>
    cases value with
    | none => simp [theWords] at success
    | some value =>
      cases value with
      | loc first second => simp [theWords] at success
      | word word =>
        cases tail : theWords values with
        | none => simp [theWords,tail] at success
        | some rest =>
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨word,rfl⟩
          · exact ih rest tail value member

/-- Full source list equality. The anonymous case expression's elided branches
are immaterial under exactly the original successful extraction premise;
theWordsEveryIsSomeWord proves the required constructor fact for every input. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "the_words_SOME_eq" (words_as_type_indexed_bitvec)]
theorem theWordsSomeEq {width : Nat} [NeZero width]
    (values : List (Option (WordLocW width))) (words : List (BitVec width))
    (success : theWords values = some words) :
    words = values.map successfulWordProjection := by
  induction values generalizing words with
  | nil => simpa [theWords] using success.symm
  | cons value values ih =>
    cases value with
    | none => simp [theWords] at success
    | some value =>
      cases value with
      | loc first second => simp [theWords] at success
      | word word =>
        cases tail : theWords values with
        | none => simp [theWords,tail] at success
        | some rest =>
          simp only [theWords,tail,Option.some.injEq] at success
          rw [← success]
          simp only [List.map_cons,successfulWordProjection,holThe,ih rest tail]

/-- Full mapped-source witness, retaining the independent source carrier and
arbitrary mapping function. Membership and successful extraction are the only
source premises. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "the_words_MAP_exists" (words_as_type_indexed_bitvec)]
theorem theWordsMapExists {width : Nat} [NeZero width] {α : Type}
    (values : List α) (words : List (BitVec width)) (value : α)
    (mapValue : α → Option (WordLocW width))
    (success : theWords (values.map mapValue) = some words ∧ value ∈ values) :
    ∃ word, mapValue value = some (.word word) :=
  theWordsEveryIsSomeWord _ words success.1 _ (List.mem_map_of_mem success.2)

end Flapjack.WordToStackProofs
