import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Representation

/-! Original HOL observations for pointer-tag and heap representation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

private def config : Config := ⟨1, 2, 0, 4, false, false, false, false, false, false, .none⟩

example : getLowerBits config (.word (255 : BitVec 8)) = 15 := by decide

example : getLowerBits { config with lenBits := 20 } (.word (254 : BitVec 8)) = 255 := by decide

example : wordAddr config (.data (.loc 7 9) : HeapAddress (WordLocW 8)) = .loc 7 0 := by rfl

example : wordAddr config (.data (.word (255 : BitVec 8))) = .word 254 := by decide

example : wordAddr config (.pointer 2 (.word (255 : BitVec 8))) = .word 79 := by decide

example : (blockNil 2 : BitVec 8) = 34 := by decide

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
