import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.CodeSafety

namespace Flapjack.Test.LabToTargetCodeSafetyTransportParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps

example {width : Nat} [NeZero width] (code target : LabProgHOL width)
    (h : codeSimilar code target ∧ noShareMemInst code) : noShareMemInst target :=
  codeSimilar_noShareMem code target h

example {width : Nat} [NeZero width] (code target : LabProgHOL width)
    (h : codeSimilar code target) (safe : noShareMemInst target) : noShareMemInst code :=
  codeSimilar_noShareMem target code ⟨codeSimilar_sym code target h, safe⟩

def skipCode (width : Nat) [NeZero width] (bytes : List (BitVec 8)) (len : Nat) :
    LabProgHOL width := [⟨0, [.asm (.asmi (.inst .skip)) bytes len]⟩]

example {width : Nat} [NeZero width] (bytes1 bytes2 : List (BitVec 8)) (len1 len2 : Nat) :
    noShareMemInst (skipCode width bytes2 len2) := by
  have hs : codeSimilar (skipCode width bytes1 len1) (skipCode width bytes2 len2) :=
    ⟨trivial, .cons rfl .nil, rfl⟩
  have safe : noShareMemInst (skipCode width bytes1 len1) := by
    intro p op re address bytes len hfetch
    by_cases hp : p = 0 <;>
      simp [skipCode, asmFetchAux, isLabelHOL, hp] at hfetch
  exact codeSimilar_noShareMem _ _ ⟨hs, safe⟩

example {width : Nat} [NeZero width]
    (bytes : List (BitVec 8)) (len : Nat) (op : Flapjack.Compiler.Encoders.Asm.HolMemop)
    (reg : Nat) (address : Flapjack.Compiler.Encoders.Asm.HolAddr width) :
    ¬ codeSimilar (skipCode width bytes len)
      [⟨0, [.asm (.shareMem op reg address) bytes len]⟩] := by
  intro h
  have hr := codeSimilar_asmFetchAux 0 _ _ h
  simp [skipCode, asmFetchAux, isLabelHOL, lineSimilar] at hr

end Flapjack.Test.LabToTargetCodeSafetyTransportParity
