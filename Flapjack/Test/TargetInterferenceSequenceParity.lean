import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceSequence

namespace Flapjack.Test.TargetInterferenceSequenceParity
open Flapjack Flapjack.Compiler.Backend.Semantics.TargetProps
variable {width : Nat} [NeZero width] {S Q σ : Type}
variable (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)

example : interferenceAppSeq mc ffi ms 0 = nextInterference mc ffi ms := rfl
example (P : InterferenceApp width S → Prop) : interferenceCount P mc ffi ms 0 = 0 := rfl
example (n : Nat) (h : nextInterference mc ffi ms = none) :
    interferenceAppSeq mc ffi ms (n + 1) = none := by
  simp [interferenceAppSeq, h]
example (n : Nat) (app : InterferenceApp width S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : nextInterference mc ffi ms = some (app, mc', ffi')) :
    interferenceAppSeq mc ffi ms (n + 1) = interferenceAppSeq mc' ffi' (appPost app) n := by
  simp [interferenceAppSeq, h]
example (P : InterferenceApp width S → Prop) (n : Nat)
    (h : interferenceAppSeq mc ffi ms n = none) :
    interferenceCount P mc ffi ms (n + 1) = interferenceCount P mc ffi ms n := by
  simp [interferenceCount, h]
example (P : InterferenceApp width S → Prop) (n : Nat) (app : InterferenceApp width S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : interferenceAppSeq mc ffi ms n = some (app, mc', ffi')) (hp : P app) :
    interferenceCount P mc ffi ms (n + 1) = interferenceCount P mc ffi ms n + 1 := by
  simp [interferenceCount, h, hp]
example (P : InterferenceApp width S → Prop) (n : Nat) (app : InterferenceApp width S)
    (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : interferenceAppSeq mc ffi ms n = some (app, mc', ffi')) (hp : ¬ P app) :
    interferenceCount P mc ffi ms (n + 1) = interferenceCount P mc ffi ms n := by
  simp [interferenceCount, h, hp]
-- Choice regressions assert witness specifications, never equality between arbitrary choices.
example (res : InterferenceApp width S × MachineConfig width S Q × HolFfiState σ)
    (h : nextInterference mc ffi ms = some res) :
    ∃ k, findNextInterference mc ffi k ms = some res :=
  holOptionSome_some (P := fun res => ∃ k, findNextInterference mc ffi k ms = some res) h
example (P : InterferenceApp width S → Prop) (k n : Nat)
    (h : interferencePos P mc ffi ms k = some n) :
    interferenceCount P mc ffi ms n = k ∧
      ∃ app mc' ffi', interferenceAppSeq mc ffi ms n = some (app, mc', ffi') ∧ P app :=
  holOptionSome_some (P := fun n => interferenceCount P mc ffi ms n = k ∧
    ∃ app mc' ffi', interferenceAppSeq mc ffi ms n = some (app, mc', ffi') ∧ P app) h
end Flapjack.Test.TargetInterferenceSequenceParity
