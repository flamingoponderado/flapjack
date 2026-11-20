module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- A valid Word64 cell has the concrete header-and-payload word list. This
Flapjack helper supplies the Word64 case of the source memory allocation proof. -/
theorem wordElWord64Eq {width : Nat} [NeZero width] (c : DataToWord.Config)
    (addr : BitVec width) (ws : List (WordLocW width)) (hd : BitVec width)
    (encoded : encodeHeader c 3 ws.length = some hd)
    (configBound : c.lenSize + 5 < width) (good : goodDimindex width) :
    wordEl addr (.dataElement [] ws.length (.word64Tag, ws)) c = Misc.wordList addr (.word hd :: ws) := by
  have header : makeHeader c 3 ws.length = hd := by
    have h := encoded
    simp only [encodeHeader] at h
    split at h
    · exact Option.some.inj h
    · simp at h
  have decoded := encodeHeaderImp c 3 ws.length hd encoded configBound good
  funext heap
  apply propext
  simp only [wordEl, wordPayload, List.isEmpty_nil, Bool.true_and]
  rw [header]
  simp [encoded, decoded.1, decoded.2, StackRemove.WordListExists.starCond]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
