module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackLists
@[expose] public section

/-! Stack-key facts used by data-to-word GC proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStackEq

/-- Related stack keys imply equal stack lengths. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "s_key_eq_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem sKeyEq_length {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) (h : sKeyEq xs ys) : xs.length = ys.length :=
  sKeyEqLength xs ys h

/-- Taking the last frames preserves the stack-key relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "s_key_eq_LASTN"
  (words_as_type_indexed_bitvec)]
theorem sKeyEq_lastN {width : Nat} [NeZero width]
    (xs ys : List (WordSemStackFrame width)) (n : Nat) (h : sKeyEq xs ys) :
    sKeyEq (wordSemLastN n xs) (wordSemLastN n ys) :=
  sKeyEqLastN xs ys n h
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
