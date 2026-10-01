import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterLabels

/-! Kernel fixtures for the five original register-write label rows.
The theorem is instantiated non-vacuously without register/frame bounds. -/
namespace Flapjack.Test.WordToStackRegisterLabelsParity
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- wr_physical
example : getCodeLabels (wRegWrite1Native (fun _ => (.skip : HolProg 64)) 2 (4,9,8)) = ∅ ∧
    getCodeLabels (wRegWrite2Native (fun _ => (.skip : HolProg 64)) 2 (4,9,8)) = ∅ := by
  exact ⟨(getCodeLabelsWReg _ _ _).1 (by intro n; rfl),
    (getCodeLabelsWReg _ _ _).2 (by intro n; rfl)⟩

-- wr_boundary
example : getCodeLabels (wRegWrite1Native (fun r => (.stackStore r 0 : HolProg 64)) 8 (4,9,8)) = ∅ ∧
    getCodeLabels (wRegWrite2Native (fun r => (.stackStore r 0 : HolProg 64)) 8 (4,9,8)) = ∅ := by
  exact ⟨(getCodeLabelsWReg _ _ _).1 (by intro n; rfl),
    (getCodeLabelsWReg _ _ _).2 (by intro n; rfl)⟩

-- wr_spilled
example : getCodeLabels (wRegWrite1Native (fun r => (.seq .skip (.stackLoad r 1) : HolProg 64)) 20 (4,2,0)) = ∅ ∧
    getCodeLabels (wRegWrite2Native (fun r => (.seq .skip (.stackLoad r 1) : HolProg 64)) 20 (4,2,0)) = ∅ := by
  exact ⟨(getCodeLabelsWReg _ _ _).1 (by intro n; simp [getCodeLabels]),
    (getCodeLabelsWReg _ _ _).2 (by intro n; simp [getCodeLabels])⟩

-- wr_zero
example : getCodeLabels (wRegWrite1Native (fun _ => (.skip : HolProg 64)) 0 (0,0,0)) = ∅ ∧
    getCodeLabels (wRegWrite2Native (fun _ => (.skip : HolProg 64)) 0 (0,0,0)) = ∅ := by
  exact ⟨(getCodeLabelsWReg _ _ _).1 (by intro n; rfl),
    (getCodeLabelsWReg _ _ _).2 (by intro n; rfl)⟩

-- wr_large
example : getCodeLabels (wRegWrite1Native (fun _ => (.skip : HolProg 64)) (2^80) (4,2,2^85)) = ∅ ∧
    getCodeLabels (wRegWrite2Native (fun _ => (.skip : HolProg 64)) (2^80) (4,2,2^85)) = ∅ := by
  exact ⟨(getCodeLabelsWReg _ _ _).1 (by intro n; rfl),
    (getCodeLabelsWReg _ _ _).2 (by intro n; rfl)⟩

/-- The callback premise cannot be removed: an input label survives the helper. -/
example : ((7,3) ∈ getCodeLabels
    (wRegWrite1Native (fun _ => (.locValue 0 7 3 : HolProg 64)) 20 (4,0,0))) ∧
    ((7,3) ∈ getCodeLabels
    (wRegWrite2Native (fun _ => (.locValue 0 7 3 : HolProg 64)) 20 (4,0,0))) := by
  constructor
  · simp [wRegWrite1Native,getCodeLabels]; rfl
  · simp [wRegWrite2Native,getCodeLabels]; rfl

end Flapjack.Test.WordToStackRegisterLabelsParity
