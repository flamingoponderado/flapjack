import Flapjack.Compiler.Backend.LabToTarget.CodeSafety

namespace Flapjack.Test.LabCodeSafetyParity
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm

example {w : Nat} [NeZero w] : noInstall (width := w) [] := by
  simp [noInstall, asmFetchAux]
example {w : Nat} [NeZero w] : noShareMemInst (width := w) [] := by
  simp [noShareMemInst, asmFetchAux]
example : ¬ noInstall (width := 8) [⟨7, [.labAsm .install 0 [] 0]⟩] := by
  intro h
  have bad := h 0 0 [] 0
  simp [asmFetchAux, isLabelHOL] at bad
example : ¬ noShareMemInst (width := 8)
    [⟨7, [.asm (.shareMem .load 0 (.addr 0 0)) [] 0]⟩] := by
  intro h
  have bad := h 0 .load 0 (.addr 0 0) [] 0
  simp [asmFetchAux, isLabelHOL] at bad

example {w : Nat} [NeZero w] (code : LabProgHOL w) :
    noInstall code ↔ ∀ p pos bytes len,
      asmFetchAux p code ≠ some (.labAsm .install pos bytes len) := Iff.rfl
example {w : Nat} [NeZero w] (code : LabProgHOL w) :
    noShareMemInst code ↔ ∀ p op re a inst len,
      asmFetchAux p code ≠ some (.asm (.shareMem op re a) inst len) := Iff.rfl
example {w : Nat} [NeZero w] (code : LabProgHOL w) (names : List HolFfiName) :
    noInstallOrNoShareMem code names ↔
      (noShareMemInst code ∧ ∀ x ∈ names,
        ∃ name : Flapjack.Basis.Pure.MlString.MlString, x = .extCall name) ∨
      noInstall code := Iff.rfl
example {w : Nat} [NeZero w] (code : LabProgHOL w) (names : List HolFfiName)
    (h : noInstall code) : noInstallOrNoShareMem code names := Or.inr h
example {w : Nat} [NeZero w] (code : LabProgHOL w) (h : noShareMemInst code) :
    noInstallOrNoShareMem code [] := Or.inl ⟨h, by simp⟩
example {w : Nat} [NeZero w] (names : List HolFfiName) :
    noInstallOrNoShareMem (width := w) [] names := by
  exact Or.inr (by simp [noInstall, asmFetchAux])

-- Original safety_install_extcall: Install is allowed without shared memory.
example : noInstallOrNoShareMem (width := 8)
    [⟨7, [.labAsm .install 0 [] 0]⟩] [.extCall (.implode [])] := by
  apply Or.inl
  constructor
  · intro p op re a inst len
    cases p <;> simp [asmFetchAux, isLabelHOL]
  · simp

-- Original safety_install_shared_rejected: neither alternative holds.
example : ¬ noInstallOrNoShareMem (width := 8)
    [⟨7, [.labAsm .install 0 [] 0]⟩] [.sharedMem .mappedRead] := by
  intro h
  rcases h with h | h
  · obtain ⟨name, bad⟩ := h.2 (.sharedMem .mappedRead) (by simp)
    cases bad
  · have bad := h 0 0 [] 0
    simp [asmFetchAux, isLabelHOL] at bad

-- Original safety_shared_any_names: absence of Install suffices for any names.
example (names : List HolFfiName) : noInstallOrNoShareMem (width := 8)
    [⟨7, [.asm (.shareMem .load 0 (.addr 0 0)) [] 0]⟩] names := by
  apply Or.inr
  intro p pos bytes len
  cases p <;> simp [asmFetchAux, isLabelHOL]

end Flapjack.Test.LabCodeSafetyParity
