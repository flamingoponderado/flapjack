module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- The concrete header and payload for a bignum cell. This Flapjack helper
supplies the bignum case of the source memory-allocation proof. -/
theorem wordElBignumEq {width : Nat} [NeZero width] (c : DataToWord.Config)
    (addr : BitVec width) (ws : List (BitVec width)) (negative : Bool) (hd : BitVec width)
    (encoded : encodeHeader c (((if negative then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat ws.length = some hd)
    (configBound : c.lenSize + 5 < width) (good : goodDimindex width) :
    wordEl addr (.dataElement [] ws.length (.numTag negative, ws.map .word)) c =
      Misc.wordList addr (.word hd :: ws.map .word) := by
  cases negative <;>
    rcases good with width32 | width64 <;> subst width <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at encoded ⊢
  all_goals
    have decoded := encodeHeaderImp c _ ws.length hd encoded configBound (by simp [goodDimindex])
    have header := encoded
    simp only [encodeHeader] at header
    split at header
    · have header := Option.some.inj header
      simp only [show (((0 : BitVec 32) <<< 2) ||| 3).toNat = 3 by decide,
        show (((0 : BitVec 64) <<< 2) ||| 3).toNat = 3 by decide,
        show (((1 : BitVec 32) <<< 2) ||| 3).toNat = 7 by decide,
        show (((1 : BitVec 64) <<< 2) ||| 3).toNat = 7 by decide] at header encoded
      funext heap
      apply propext
      simp only [wordEl, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map]
      simp [header, encoded, decoded.1, decoded.2, StackRemove.WordListExists.starCond]
    · simp at header
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
