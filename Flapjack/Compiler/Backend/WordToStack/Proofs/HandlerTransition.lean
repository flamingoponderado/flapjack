import Flapjack.Compiler.Backend.WordToStack.Proofs.EnvironmentIdentity
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedAList
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionSuffix
import Flapjack.Compiler.Backend.WordToStack.Proofs.InterUnionLeft

namespace Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.WordToStack

/-- Inhabitation only; it does not choose HOL’s unspecified empty EL value. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) :=
  ⟨.word (BitVec.ofNat width 0)⟩
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Flapjack representation identity for two adjacent-key SORTED encodings;
no stronger all-pairs ordering premise is introduced. -/
theorem descendingKeysIffHolSorted {α : Type} (xs : List (Nat × α)) :
    descendingKeys xs ↔ holSorted (fun x y => x.1 > y.1) xs := by
  induction xs with
  | nil => simp [descendingKeys, holSorted]
  | cons x xs ih =>
    cases xs with
    | nil => simp [descendingKeys, holSorted]
    | cons y ys =>
      simpa [descendingKeys, holSorted] using (and_congr_right (fun (_ : x.1 > y.1) => ih))

/-- Flapjack proof support for the actual handler transition: identity-oracle
serialization of a strictly sorted association list returns exactly that list.
The equality is derived from source operations, never supplied as a premise. -/
theorem sortedEnvironmentIdentity {width : Nat} [NeZero width]
    (entries : List (Nat × WordLocW width)) (sorted : descendingKeys entries) :
    (wordSemEnvToList (sptFromAList entries) (fun _ => id)).1 = entries := by
  have result := envToListIdentityImp (sptFromAList entries) _ _ rfl
  apply sortedFstPermImpAListEq entries _ sorted
  · exact (descendingKeysIffHolSorted _).mpr result.1
  · exact (holPerm_iff _ _).mp result.2.2

/-- Flapjack decoder infrastructure for the original Raise transition:
removing the three handler words changes only the abstract handler marker.
The actual decoding premise supplies the header and complete payload. -/
theorem absStackRemoveHandler {width frameWidth : Nat}
    [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW frameWidth)) (saved : Nat × Nat × Nat)
    (sourceTail : List (WordSemStackFrame frameWidth))
    (words : List (WordLocW width)) (lens : List Nat)
    (ex : WordLocW width × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (decoded : absStack bs (.stackFrame size nonGc gc (some saved) :: sourceTail) words lens =
      some ((some ex, bits, payload) :: tail)) :
    absStack bs (.stackFrame size nonGc gc none :: sourceTail) (words.drop 3) lens =
      some ((none, bits, payload) :: tail) := by
  cases lens with
  | nil => cases words <;> simp [absStack] at decoded
  | cons len lens =>
    cases words with
    | nil => simp [absStack] at decoded
    | cons marker words =>
      cases words with
      | nil => simp [absStack] at decoded
      | cons loc words =>
        cases words with
        | nil => simp [absStack] at decoded
        | cons hv words =>
          cases words with
          | nil => simp [absStack] at decoded
          | cons bitmap words =>
            cases read : StackSem.fullReadBitmap bs bitmap with
            | none => simp [absStack, read] at decoded
            | some readBits =>
              simp only [absStack, read] at decoded
              split at decoded <;> simp_all
              cases recurse : absStack bs sourceTail (words.drop len) lens with
              | none => simp [recurse] at decoded
              | some rest =>
                simp only [recurse, Option.some.injEq, List.cons.injEq, Prod.mk.injEq] at decoded
                rcases decoded with ⟨lengthEq, bound, ⟨_, rfl, rfl⟩, rfl⟩
                simp [absStack, read, recurse, lengthEq, bound]

/-- Flapjack infrastructure: clearing the handler marker retains the complete
normal-frame auxiliary relation; saved-header obligations are discharged by
the original handler relation rather than introduced as new premises. -/
theorem stackRelAuxRemoveHandler {locWidth width frameWidth : Nat}
    [NeZero locWidth] [NeZero width] [NeZero frameWidth]
    (k len : Nat) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW frameWidth)) (saved : Nat × Nat × Nat)
    (sourceTail : List (WordSemStackFrame frameWidth))
    (ex : WordLocW locWidth × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW frameWidth))
    (tail : List (Option (WordLocW locWidth × WordLocW width) × List Bool × List (WordLocW frameWidth)))
    (related : stackRelAux k len (.stackFrame size nonGc gc (some saved) :: sourceTail)
      ((some ex, bits, payload) :: tail)) :
    stackRelAux k len (.stackFrame size nonGc gc none :: sourceTail)
      ((none, bits, payload) :: tail) := by
  simp only [stackRelAux] at related ⊢
  exact related.2.2

/-- Flapjack extraction of the real decoder header. Actual successful handler
decoding supplies every word and the bitmap/body decomposition. -/
theorem absStackHandlerWords {width frameWidth : Nat}
    [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW frameWidth)) (saved : Nat × Nat × Nat)
    (sourceTail : List (WordSemStackFrame frameWidth))
    (words : List (WordLocW width)) (lens : List Nat)
    (ex : WordLocW width × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (decoded : absStack bs (.stackFrame size nonGc gc (some saved) :: sourceTail) words lens =
      some ((some ex, bits, payload) :: tail)) :
    ∃ bitmap body, words = .word (BitVec.ofNat width 1) :: ex.1 :: ex.2 :: bitmap :: body := by
  cases lens with
  | nil => cases words <;> simp [absStack] at decoded
  | cons len lens =>
    cases words with
    | nil => simp [absStack] at decoded
    | cons marker words =>
      cases words with
      | nil => simp [absStack] at decoded
      | cons loc words =>
        cases words with
        | nil => simp [absStack] at decoded
        | cons hv words =>
          cases words with
          | nil => simp [absStack] at decoded
          | cons bitmap words =>
            cases read : StackSem.fullReadBitmap bs bitmap with
            | none => simp [absStack, read] at decoded
            | some readBits =>
              simp only [absStack, read] at decoded
              split at decoded <;> simp_all
              cases recurse : absStack bs sourceTail (words.drop len) lens with
              | none => simp [recurse] at decoded
              | some rest =>
                simp only [recurse, Option.some.injEq, List.cons.injEq, Prod.mk.injEq] at decoded
                rcases decoded with ⟨_, _, ⟨rfl, _, _⟩, _⟩
                exact ⟨rfl, rfl⟩

/-- Flapjack total-index arithmetic used to transport decoded header words to
the original full raw stack. Unspecified out-of-range EL remains unchanged. -/
theorem holElDrop {α : Type} [Nonempty α] (xs : List α) (dropCount index : Nat) :
    holEl index (xs.drop dropCount) = holEl (dropCount + index) xs := by
  induction dropCount generalizing xs with
  | zero => simp
  | succ count ih =>
    cases xs with
    | nil =>
      simp only [List.drop_nil]
      rw [holEl_of_length_le index [] (by simp), holEl_of_length_le (count + 1 + index) [] (by simp)]
    | cons x xs =>
      simp only [List.drop_succ_cons]
      rw [ih]
      have sum : count + 1 + index = (count + index) + 1 := by omega
      rw [sum, holEl_cons_succ]

/-- Flapjack full handler-suffix extraction for the original Raise proof.
The existential handler and payload are derived from actual suffix decoding
and the original relation, rather than passed as target-state premises. -/
theorem handlerSuffixExtract {width : Nat} [NeZero width]
    (bs : List (BitVec width)) (source : List (WordSemStackFrame width))
    (words : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (n handler k : Nat) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (saved : Nat × Nat × Nat)
    (rest : List (WordSemStackFrame width))
    (bound : handler + 1 ≤ source.length)
    (suffix : wordSemLastN (handler + 1) source = .stackFrame size nonGc gc (some saved) :: rest)
    (decoded : absStack bs source (words.drop n) lens = some stack)
    (related : stackRelAux k words.length source stack) :
    ∃ ex bits payload,
      wordSemLastN (handler + 1) stack =
        (some ex, bits, payload) :: wordSemLastN handler stack ∧
      absStack bs (.stackFrame size nonGc gc (some saved) :: rest)
        (wordSemLastN (handlerVal (wordSemLastN (handler + 1) stack)) (words.drop n))
        (wordSemLastN (handler + 1) lens) =
          some ((some ex, bits, payload) :: wordSemLastN handler stack) ∧
      stackRelAux k words.length (.stackFrame size nonGc gc (some saved) :: rest)
        ((some ex, bits, payload) :: wordSemLastN handler stack) := by
  have extracted := absStackPrefixDrop bs source (words.drop n) lens stack
    (handler + 1) _ k words.length bound suffix decoded related
  dsimp only at extracted
  have lengthEq := (absStackImpLength bs source _ lens stack decoded).1
  have targetBound : handler + 1 ≤ stack.length := by omega
  cases shape : wordSemLastN (handler + 1) stack with
  | nil => simp only [shape, stackRelAux] at extracted; exact False.elim extracted.2
  | cons entry tail =>
    rcases entry with ⟨targetHandler, bits, payload⟩
    cases targetHandler with
    | none => simp only [shape, stackRelAux] at extracted; exact False.elim extracted.2
    | some ex =>
      have tailEq := lastNLess stack handler (some ex, bits, payload) tail targetBound shape
      subst tail
      rw [shape] at extracted
      exact ⟨ex, bits, payload, rfl, extracted.1, extracted.2⟩

/-- Flapjack arithmetic exposing the original absolute raw-stack suffix from
actual successful abstraction; its length bound is derived by the decoder. -/
theorem decodedSuffixAbsolute {width frameWidth : Nat}
    [NeZero width] [NeZero frameWidth]
    (bs : List (BitVec width)) (source : List (WordSemStackFrame frameWidth))
    (words : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (n h : Nat) (decoded : absStack bs source (words.drop n) lens = some stack) :
    wordSemLastN (handlerVal (wordSemLastN h stack)) (words.drop n) =
      words.drop (words.length - handlerVal (wordSemLastN h stack)) := by
  rw [lastNDropWithin words n _ (absStackLen bs source _ lens stack h decoded), lastNDrop2]

/-- Flapjack header-index transport from actual successful suffix decoding.
Both absolute word reads and the raw-stack length bound are derived. -/
theorem decodedHandlerAbsoluteWords {width : Nat} [NeZero width]
    (bs : List (BitVec width)) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (saved : Nat × Nat × Nat)
    (rest : List (WordSemStackFrame width)) (words : List (WordLocW width))
    (lens : List Nat) (offset : Nat)
    (ex : WordLocW width × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (decoded : absStack bs (.stackFrame size nonGc gc (some saved) :: rest)
      (words.drop offset) lens = some ((some ex, bits, payload) :: tail)) :
    3 ≤ words.length ∧ holEl (offset + 1) words = ex.1 ∧ holEl (offset + 2) words = ex.2 := by
  obtain ⟨bitmap, body, layout⟩ := absStackHandlerWords bs size nonGc gc saved rest _ lens
    ex bits payload tail decoded
  have lengths := congrArg List.length layout
  simp only [List.length_drop, List.length_cons] at lengths
  refine ⟨by omega, ?_, ?_⟩
  · rw [← holElDrop words offset 1, layout]
    rfl
  · rw [← holElDrop words offset 2, layout]
    rfl

/-- Flapjack assembly of the original header-value obligations from actual
suffix decoder success and its complete auxiliary relation. -/
theorem decodedRelatedHandlerWords {width : Nat} [NeZero width]
    (bs : List (BitVec width)) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (h1 l3 l4 k : Nat)
    (rest : List (WordSemStackFrame width)) (words : List (WordLocW width))
    (lens : List Nat) (offset : Nat)
    (ex : WordLocW width × WordLocW width) (bits : List Bool)
    (payload : List (WordLocW width))
    (tail : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (decoded : absStack bs (.stackFrame size nonGc gc (some (h1,l3,l4)) :: rest)
      (words.drop offset) lens = some ((some ex, bits, payload) :: tail))
    (related : stackRelAux k words.length (.stackFrame size nonGc gc (some (h1,l3,l4)) :: rest)
      ((some ex, bits, payload) :: tail)) :
    3 ≤ words.length ∧ holEl (offset + 1) words = .loc l3 l4 ∧
      (h1 < rest.length → isHandlerFrame (holEl (rest.length - (h1 + 1)) rest) = true →
        holEl (offset + 2) words = .word (BitVec.ofNat width
          (words.length - handlerVal (wordSemLastN (h1 + 1) ((some ex, bits, payload) :: tail))))) := by
  have headers := decodedHandlerAbsoluteWords bs size nonGc gc (h1,l3,l4) rest words lens offset
    ex bits payload tail decoded
  have lengths := (absStackImpLength bs _ _ lens _ decoded).1
  simp only [List.length_cons] at lengths
  simp only [stackRelAux] at related
  refine ⟨headers.1, headers.2.1.trans related.2.1, ?_⟩
  intro bound active
  have targetBound : h1 < tail.length := by omega
  rw [headers.2.2, lastNConsWithin _ tail (h1 + 1) (by omega), lastNDrop2]
  have tailLength : tail.length = rest.length := by omega
  exact related.1 targetBound (by simpa only [tailLength] using active)

/-- Full original handler-frame transition used by comp_correct Raise.
All original bounds, sorted source environment, source suffix, decoding and
auxiliary-relation premises are retained; every target payload/header and
unwound decoder/relation conclusion is derived. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "stack_rel_raise"
  (words_as_type_indexed_bitvec)]
theorem stackRelRaise {width : Nat} [NeZero width]
    (bs : List (BitVec width)) (source : List (WordSemStackFrame width))
    (words : List (WordLocW width)) (lens : List Nat)
    (stack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
    (n handler k : Nat) (size : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (h1 l3 l4 : Nat)
    (rest : List (WordSemStackFrame width))
    (_rawBound : n ≤ words.length) (bound : handler + 1 ≤ source.length)
    (sorted : holSorted (fun x y => x.1 > y.1) gc)
    (suffix : wordSemLastN (handler + 1) source = .stackFrame size nonGc gc (some (h1,l3,l4)) :: rest)
    (decoded : absStack bs source (words.drop n) lens = some stack)
    (related : stackRelAux k words.length source stack) :
    ∃ ex payload,
      wordSemLastN (handler + 1) stack = (some ex, payload) :: wordSemLastN handler stack ∧
      3 ≤ words.length ∧ 3 ≤ handlerVal (wordSemLastN (handler + 1) stack) ∧
      holEl (words.length - handlerVal (wordSemLastN (handler + 1) stack) + 1) words = .loc l3 l4 ∧
      (h1 < rest.length ∧ isHandlerFrame (holEl (rest.length - (h1 + 1)) rest) = true →
        holEl (words.length - handlerVal (wordSemLastN (handler + 1) stack) + 2) words =
          .word (BitVec.ofNat width (words.length - handlerVal
            (wordSemLastN (h1 + 1) (wordSemLastN (handler + 1) stack))))) ∧
      stackRelAux k words.length
        (.stackFrame size nonGc (wordSemEnvToList (sptFromAList gc) (fun _ => id)).1 none :: rest)
        ((none, payload) :: wordSemLastN handler stack) ∧
      absStack bs
        (.stackFrame size nonGc (wordSemEnvToList (sptFromAList gc) (fun _ => id)).1 none :: rest)
        (words.drop (words.length - handlerVal (wordSemLastN (handler + 1) stack) + 3))
        (wordSemLastN (handler + 1) lens) = some ((none, payload) :: wordSemLastN handler stack) := by
  obtain ⟨ex, bits, payload, shape, suffixDecoded, suffixRelated⟩ :=
    handlerSuffixExtract bs source words lens stack n handler k size nonGc gc (h1,l3,l4)
      rest bound suffix decoded related
  rw [decodedSuffixAbsolute bs source words lens stack n (handler + 1) decoded] at suffixDecoded
  have headers := decodedRelatedHandlerWords bs size nonGc gc h1 l3 l4 k rest words
    (wordSemLastN (handler + 1) lens)
    (words.length - handlerVal (wordSemLastN (handler + 1) stack)) ex bits payload
    (wordSemLastN handler stack) suffixDecoded suffixRelated
  have cleared := stackRelAuxRemoveHandler k words.length size nonGc gc (h1,l3,l4) rest
    ex bits payload (wordSemLastN handler stack) suffixRelated
  have unwound := absStackRemoveHandler bs size nonGc gc (h1,l3,l4) rest _
    (wordSemLastN (handler + 1) lens) ex bits payload (wordSemLastN handler stack) suffixDecoded
  have envEq := sortedEnvironmentIdentity gc ((descendingKeysIffHolSorted _).mpr sorted)
  refine ⟨ex, (bits,payload), shape, headers.1, ?_, headers.2.1, ?_, ?_, ?_⟩
  · rw [shape]
    simp only [handlerVal]
    omega
  · intro active
    simpa only [shape] using headers.2.2 active.1 active.2
  · rw [envEq]
    exact cleared
  · rw [envEq]
    simpa only [List.drop_drop] using unwound

end Flapjack.WordToStackProofs
