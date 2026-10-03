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

example {width : Nat} [NeZero width] (code target : LabProgHOL width)
    (names : List HolFfiName) (h : codeSimilar code target ∧ noInstallOrNoShareMem code names) :
    noInstallOrNoShareMem target names := codeSimilar_noInstallOrNoShareMem code target names h

example {width : Nat} [NeZero width] (code target : LabProgHOL width)
    (names : List HolFfiName) (h : codeSimilar code target)
    (safe : noInstallOrNoShareMem target names) : noInstallOrNoShareMem code names :=
  codeSimilar_noInstallOrNoShareMem target code names ⟨codeSimilar_sym code target h, safe⟩

def installCode (width : Nat) [NeZero width] (pos : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat) : LabProgHOL width :=
  [⟨0, [.labAsm .install pos bytes len]⟩]

-- Install is genuinely allowed by the shared-memory-free/external-name branch.
example {width : Nat} [NeZero width] (p1 p2 : BitVec width)
    (bytes1 bytes2 : List (BitVec 8)) (len1 len2 : Nat) :
    noInstallOrNoShareMem (installCode width p2 bytes2 len2) [] := by
  have hs : codeSimilar (installCode width p1 bytes1 len1)
      (installCode width p2 bytes2 len2) := ⟨trivial, .cons rfl .nil, rfl⟩
  have safe : noShareMemInst (installCode width p1 bytes1 len1) := by
    intro p op re address bytes len hfetch
    by_cases hp : p = 0 <;>
      simp [installCode, asmFetchAux, isLabelHOL, hp] at hfetch
  exact codeSimilar_noInstallOrNoShareMem _ _ [] ⟨hs, Or.inl ⟨safe, by simp⟩⟩

-- Every FFI-name list is allowed by the independent no-Install branch.
example {width : Nat} [NeZero width] (bytes1 bytes2 : List (BitVec 8))
    (len1 len2 : Nat) (names : List HolFfiName) :
    noInstallOrNoShareMem (skipCode width bytes2 len2) names := by
  have hs : codeSimilar (skipCode width bytes1 len1) (skipCode width bytes2 len2) :=
    ⟨trivial, .cons rfl .nil, rfl⟩
  have safe : noInstall (skipCode width bytes1 len1) := by
    intro p w bytes len hfetch
    by_cases hp : p = 0 <;>
      simp [skipCode, asmFetchAux, isLabelHOL, hp] at hfetch
  exact codeSimilar_noInstallOrNoShareMem _ _ names ⟨hs, Or.inr safe⟩

-- A shared-memory FFI name makes the Install branch's safety fail.
example {width : Nat} [NeZero width] (pos : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat) :
    ¬ noInstallOrNoShareMem (installCode width pos bytes len) [.sharedMem .mappedRead] := by
  intro h
  rcases h with ⟨_, hn⟩ | hi
  · have hh := hn (.sharedMem .mappedRead) (by simp)
    simp at hh
  · apply hi 0 pos bytes len
    simp [installCode, asmFetchAux, isLabelHOL]

end Flapjack.Test.LabToTargetCodeSafetyTransportParity
