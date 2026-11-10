module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality

@[expose] public section

/-! Mixed-width results captured by the HOL memory representation probe. -/
namespace Flapjack.Test.DataToWordWordMemoryEqualityParity
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private def allDomain (_ : BitVec 32) : Bool := true
private def noDomain (_ : BitVec 32) : Bool := false
private def wordMemory (_ : BitVec 32) : WordLocW 64 := .word 5
private def locationMemory (_ : BitVec 32) : WordLocW 64 := .loc 0 0

example : wordMemEq 0 [5, 5] allDomain wordMemory = some true := by
  simp [wordMemEq, allDomain, wordMemory]

example : wordMemEq 0 [5, 6] allDomain wordMemory = some false := by
  simp [wordMemEq, allDomain, wordMemory]

example : wordMemEq 0 [5] noDomain wordMemory = none := by
  simp [wordMemEq, noDomain]

example : wordMemEq 0 [5] allDomain locationMemory = none := by
  simp [wordMemEq, allDomain, locationMemory]

end Flapjack.Test.DataToWordWordMemoryEqualityParity
