import Flapjack.Compiler.Backend.WordSimp
import Flapjack.RiscV.WordSimp
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Mathlib.Data.List.Defs

namespace Flapjack.Compiler.Backend.WordSimp

open RiscV

/-- Complete actual encoder correspondence for production SmartSeq. Both input
encodings identify the carrier image; no output encoding is assumed. This
Flapjack infrastructure has no separate HOL declaration. Executed adoption or
a measured performance exception remains a separate inventory obligation. -/
theorem smartSeq_production {width : Nat} [NeZero width]
    (first second : WordProg (BitVec width))
    (nativeFirst nativeSecond : WordLangProgHOL (BitVec width))
    (encodedFirst : wordLangProgToHOL first = some nativeFirst)
    (encodedSecond : wordLangProgToHOL second = some nativeSecond) :
    wordLangProgToHOL (wordSimpSmartSeq first second) =
      some (smartSeqHOL nativeFirst nativeSecond) := by
  by_cases skipped : first = .skip
  · subst first
    simp only [wordLangProgToHOL, Option.some.injEq] at encodedFirst
    subst nativeFirst
    simpa only [wordSimpSmartSeq, smartSeqHOL] using encodedSecond
  · have nativeNotSkip : nativeFirst ≠ .skip := by
      intro same
      subst nativeFirst
      cases first <;>
        simp_all [wordLangProgToHOL, Option.bind_eq_some_iff]
      case call returns target arguments handler =>
        rcases returns with _ | ⟨values, sets, body, label1, label2⟩ <;>
          rcases handler with _ | ⟨exception, continuation, h1, h2⟩ <;>
          simp_all [wordLangProgToHOL, Option.bind_eq_some_iff]
    have production : wordSimpSmartSeq first second = .seq first second := by
      cases first <;> simp_all [wordSimpSmartSeq]
    have native : smartSeqHOL nativeFirst nativeSecond = .seq nativeFirst nativeSecond := by
      cases nativeFirst <;> simp_all [smartSeqHOL]
    simp [production, native, wordLangProgToHOL, encodedFirst, encodedSecond]

/-- The complete production/native prefix folds correspond for every represented
statement list and represented initial accumulator. This is carrier
infrastructure, not a HOL port or an assumed output relation. -/
theorem smartSeqFold_production {width : Nat} [NeZero width]
    (statements : List (WordProg (BitVec width)))
    (nativeStatements : List (WordLangProgHOL (BitVec width)))
    (actualStart : WordProg (BitVec width))
    (nativeStart : WordLangProgHOL (BitVec width))
    (encoded : List.Forall₂ (fun actual native => wordLangProgToHOL actual = some native)
      statements nativeStatements)
    (startEncoded : wordLangProgToHOL actualStart = some nativeStart) :
    wordLangProgToHOL (statements.foldl wordSimpSmartSeq actualStart) =
      some (nativeStatements.foldl smartSeqHOL nativeStart) := by
  induction encoded generalizing actualStart nativeStart with
  | nil => simpa only [List.foldl_nil] using startEncoded
  | cons head rest ih =>
      simp only [List.foldl_cons]
      exact ih _ _ (smartSeq_production _ _ _ _ startEncoded head)

/-- The actual left-sequence builder is the complete reviewed native SmartSeq
fold on its input codec image. Empty and all-Skip inputs are included. No
output-codec, desired fold equality or successful target is assumed. This
Flapjack production correspondence has no separate HOL declaration. -/
theorem smartSeqLeftSeq_production {width : Nat} [NeZero width]
    (statements : List (WordProg (BitVec width)))
    (nativeStatements : List (WordLangProgHOL (BitVec width)))
    (encoded : List.Forall₂ (fun actual native => wordLangProgToHOL actual = some native)
      statements nativeStatements) :
    wordLangProgToHOL (wordSimpLeftSeq statements) =
      some (nativeStatements.foldl smartSeqHOL .skip) := by
  have actual : wordSimpLeftSeq statements = statements.foldl wordSimpSmartSeq .skip := by
    cases statements <;> rfl
  rw [actual]
  exact smartSeqFold_production _ _ _ _ encoded rfl

end Flapjack.Compiler.Backend.WordSimp
