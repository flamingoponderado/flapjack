import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality

/-! Original CakeML/HOL EVAL results are captured in
`scripts/hol-probes/data_to_word_memory_repr_probe.out` under the
`word_eq_*64` labels. -/
namespace Flapjack.Test.DataToWordWordEqualityParity
open Flapjack Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private def config : Config := ⟨0, 0, 0, 4, false, false, false, false, false, false, .none⟩
private def store : HolFiniteMapExact WordStoreHOL (WordLocW 64) := HolFiniteMapExact.empty
private def allDomain (_ : BitVec 64) : Bool := true
private def fourMemory (_ : BitVec 64) : WordLocW 64 := .word 4

#guard wordEq config store allDomain fourMemory 7 5 8 8 = some (1, 7, 5)
#guard wordEq config store allDomain fourMemory 7 5 8 12 = some (0, 7, 5)
#guard wordEqList config store allDomain fourMemory 3 2 0 16 24 = some (1, 3, 2)
#guard wordEqList config store allDomain fourMemory 3 2 1 16 24 = some (1, 1, 2)
#guard wordEqList config store allDomain fourMemory 3 0 1 16 24 = none

end Flapjack.Test.DataToWordWordEqualityParity
