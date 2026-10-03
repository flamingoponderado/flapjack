import Flapjack.Compiler.Backend.WordToStack.Proofs.FrameOffsets
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSuffix
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux

namespace Flapjack.WordToStackProofs

/-- Flapjack list arithmetic for the original suffix-abstraction induction:
a suffix within a dropped tail is the same suffix of the entire word stack.
This auxiliary equation has no separate HOL declaration. -/
theorem lastNDropWithin {α : Type} (xs : List α) (dropCount suffixCount : Nat)
    (within : suffixCount ≤ (xs.drop dropCount).length) :
    wordSemLastN suffixCount (xs.drop dropCount) = wordSemLastN suffixCount xs := by
  rw [lastNDrop2, lastNDrop2, List.drop_drop]
  simp only [List.length_drop] at within ⊢
  have bound : dropCount ≤ xs.length ∨ suffixCount = 0 := by omega
  rcases bound with bound | zero
  · congr 1
    omega
  · subst suffixCount
    simp only [Nat.sub_zero]
    rw [List.drop_eq_nil_of_le (by omega), List.drop_length]

/-- Flapjack infrastructure exposing the tail clause of the actual auxiliary
relation. No separate HOL theorem is claimed. -/
theorem stackRelAuxDrop {locWidth width frameWidth : Nat}
    [NeZero locWidth] [NeZero width] [NeZero frameWidth]
    (k len : Nat) (source : List (WordSemStackFrame frameWidth))
    (target : List (Option (WordLocW locWidth × WordLocW width) × List Bool × List (WordLocW frameWidth)))
    (n : Nat) (related : stackRelAux k len source target) :
    stackRelAux k len (source.drop n) (target.drop n) := by
  induction n generalizing source target with
  | zero => simpa using related
  | succ n ih =>
      cases source with
      | nil => cases target <;> simp_all [stackRelAux]
      | cons frame source =>
          cases target with
          | nil => cases frame; simp_all [stackRelAux]
          | cons entry target =>
              cases frame with
              | stackFrame size nonGc gc handler =>
                  rcases entry with ⟨targetHandler, bits, words⟩
                  cases handler <;> cases targetHandler <;> simp only [stackRelAux] at related
                  all_goals
                    try contradiction
                    simp only [List.drop_succ_cons]
                    apply ih
                    first | exact related.2.2.2 | exact related.2.2.2.2.2

/-- Flapjack suffix arithmetic for dropping a preceding decoder header. -/
theorem lastNConsWithin {α : Type} (x : α) (xs : List α) (n : Nat)
    (within : n ≤ xs.length) : wordSemLastN n (x :: xs) = wordSemLastN n xs := by
  rw [lastNDrop2, lastNDrop2]
  have index : (x :: xs).length - n = (xs.length - n) + 1 := by simp; omega
  rw [index, List.drop_succ_cons]

/-- Flapjack successful decoder suffix infrastructure; the complete original
port also retains its source suffix equation and auxiliary relation. -/
theorem absStackSuffix {width frameWidth : Nat} [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (frames : List (WordSemStackFrame frameWidth))
    (words : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : Nat) (bound : h ≤ frames.length)
    (decoded : absStack bs frames words lens = some stack) :
    absStack bs (wordSemLastN h frames)
      (wordSemLastN (handlerVal (wordSemLastN h stack)) words)
      (wordSemLastN h lens) = some (wordSemLastN h stack) := by
  induction frames generalizing words lens stack with
  | nil =>
      have zero : h = 0 := by simp at bound; exact bound
      subst h
      cases lens <;> simp only [absStack] at decoded
      all_goals
        try contradiction
        try split at decoded <;> simp_all [wordSemLastN, handlerVal, absStack]
  | cons frame frames ih =>
      have sizes := absStackImpLength bs (frame :: frames) words lens stack decoded
      by_cases whole : h = (frame :: frames).length
      · have rawSize := absStackToStackLength bs (frame :: frames) words lens stack decoded
        have stackWhole : wordSemLastN h stack = stack := lastNMore _ _ (by omega)
        have lensWhole : wordSemLastN h lens = lens := lastNMore _ _ (by omega)
        rw [stackWhole, lensWhole, whole]
        rw [lastNMore _ _ (by omega), rawSize, lastNMore _ _ (by omega)]
        exact decoded
      · have tailBound : h ≤ frames.length := by simp only [List.length_cons] at bound whole; omega
        cases frame with
        | stackFrame size nonGc gc handler =>
          cases words with
          | nil => cases lens <;> simp [absStack] at decoded
          | cons header words =>
            cases lens with
            | nil => simp [absStack] at decoded
            | cons len lens =>
              cases handler with
              | none =>
                cases bitmap : StackSem.fullReadBitmap bs header with
                | none => simp [absStack, bitmap] at decoded
                | some bits =>
                  simp only [absStack, bitmap] at decoded
                  try split at decoded <;> simp_all
                  cases tail : absStack bs frames (words.drop len) lens with
                  | none => simp [tail] at decoded
                  | some rest =>
                    simp only [tail, Option.some.injEq] at decoded
                    obtain ⟨_, eq⟩ := decoded
                    subst stack
                    have restLength := (absStackImpLength bs frames _ lens rest tail).1
                    have rawBound := absStackLen bs frames _ lens rest h tail
                    have dropSuffix := lastNDropWithin words len (handlerVal (wordSemLastN h rest)) rawBound
                    have headerSuffix := lastNConsWithin header words (handlerVal (wordSemLastN h rest)) (by simp only [List.length_drop] at rawBound; omega)
                    rw [lastNConsWithin _ _ h tailBound, lastNConsWithin _ _ h (by omega), lastNConsWithin _ _ h (by omega)]
                    rw [headerSuffix, ← dropSuffix]
                    exact ih _ lens rest tail
              | some handler =>
                cases words with
                | nil => simp [absStack] at decoded
                | cons loc words =>
                  cases words with
                  | nil => simp [absStack] at decoded
                  | cons hv words =>
                    cases words with
                    | nil => simp [absStack] at decoded
                    | cons bitmapHeader words =>
                      cases bitmap : StackSem.fullReadBitmap bs bitmapHeader with
                      | none => simp [absStack, bitmap] at decoded
                      | some bits =>
                        simp only [absStack, bitmap] at decoded
                        try split at decoded <;> simp_all
                        cases tail : absStack bs frames (words.drop len) lens with
                        | none => simp [tail] at decoded
                        | some rest =>
                          simp only [tail, Option.some.injEq] at decoded
                          obtain ⟨_, _, eq⟩ := decoded
                          subst stack
                          have restLength := (absStackImpLength bs frames _ lens rest tail).1
                          have lensLength := (absStackImpLength bs frames _ lens rest tail).2
                          have rawBound := absStackLen bs frames _ lens rest h tail
                          rw [lastNConsWithin _ _ h tailBound, lastNConsWithin _ _ h (by omega), lastNConsWithin _ _ h (by omega)]
                          rw [lastNConsWithin (WordLocW.word (BitVec.ofNat width 1)) (loc :: hv :: bitmapHeader :: words) (handlerVal (wordSemLastN h rest)) (by simp only [List.length_cons, List.length_drop] at rawBound ⊢; omega),
                            lastNConsWithin loc (hv :: bitmapHeader :: words) (handlerVal (wordSemLastN h rest)) (by simp only [List.length_cons, List.length_drop] at rawBound ⊢; omega),
                            lastNConsWithin hv (bitmapHeader :: words) (handlerVal (wordSemLastN h rest)) (by simp only [List.length_cons, List.length_drop] at rawBound ⊢; omega),
                            lastNConsWithin bitmapHeader words (handlerVal (wordSemLastN h rest)) (by simp only [List.length_drop] at rawBound ⊢; omega),
                            ← lastNDropWithin words len _ rawBound]
                          exact ih _ lens rest tail

/-- Full original suffix decoder and auxiliary relation theorem. The decoder
and auxiliary relation together unify the source-frame and raw-stack word
dimension; all four original premises and both conclusions are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "abs_stack_prefix_drop"
  (words_as_type_indexed_bitvec)]
theorem absStackPrefixDrop {width : Nat} [NeZero width]
    (bs : List (BitVec width)) (frames : List (WordSemStackFrame width))
    (words : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (h : Nat) (sourceSuffix : List (WordSemStackFrame width)) (k len : Nat)
    (bound : h ≤ frames.length) (suffix : wordSemLastN h frames = sourceSuffix)
    (decoded : absStack bs frames words lens = some stack)
    (related : stackRelAux k len frames stack) :
    let rest := wordSemLastN h stack
    let lrest := wordSemLastN h lens
    let srest := wordSemLastN (handlerVal rest) words
    absStack bs sourceSuffix srest lrest = some rest ∧
      stackRelAux k len sourceSuffix rest := by
  subst sourceSuffix
  refine ⟨absStackSuffix bs frames words lens stack h bound decoded, ?_⟩
  have lengths := (absStackImpLength bs frames words lens stack decoded).1
  simp only [lastNDrop2]
  rw [lengths]
  exact stackRelAuxDrop k len frames stack (frames.length - h) related

end Flapjack.WordToStackProofs
