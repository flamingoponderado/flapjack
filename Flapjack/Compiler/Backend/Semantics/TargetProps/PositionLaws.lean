import Flapjack.Compiler.Backend.Semantics.TargetProps.PositionUnique

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source437: suffix counts start at the returned configuration, FFI and application post-state. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_count_tail" (words_as_type_indexed_bitvec)]
theorem interferenceCountTail {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (app0 : InterferenceApp width S) (mcc : MachineConfig width S Q)
    (ffic : HolFfiState σ) (h : nextInterference mc ffi ms = some (app0, mcc, ffic)) :
    ∀ n, interferenceCount P mc ffi ms (n + 1) =
      (if P app0 then 1 else 0) + interferenceCount P mcc ffic (appPost app0) n := by
  intro n
  induction n with
  | zero => simp [interferenceCount, interferenceAppSeq, h]
  | succ n ih =>
    rw [interferenceCount, ih, interferenceCount]
    rw [interferenceAppSeqTail mc ffi ms app0 mcc ffic h n]
    omega

/-- Literal source449: a selected first application is exactly the guarded choice for count zero. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_pos_head" (words_as_type_indexed_bitvec)]
theorem interferencePosHead {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (app0 : InterferenceApp width S) (mcc : MachineConfig width S Q)
    (ffic : HolFfiState σ)
    (h : nextInterference mc ffi ms = some (app0, mcc, ffic) ∧ P app0) :
    interferencePos P mc ffi ms 0 = some 0 := by
  have hz : interferenceAppSeq mc ffi ms 0 = some (app0, mcc, ffic) := h.1
  have hex : ∃ n, interferenceCount P mc ffi ms n = 0 ∧
      ∃ app mc' ffi', interferenceAppSeq mc ffi ms n = some (app, mc', ffi') ∧ P app :=
    ⟨0, rfl, app0, mcc, ffic, hz, h.2⟩
  unfold interferencePos holOptionSome
  rw [dif_pos hex]
  congr 1
  have hs := Classical.choose_spec hex
  rcases hs with ⟨hc, app, mc', ffi', hseq, hp⟩
  exact interferencePosUnique P mc ffi ms (Classical.choose hex) 0 app app0 mc' mcc ffi' ffic
    ⟨hseq, hp, hz, h.2, hc⟩

end Flapjack.Compiler.Backend.Semantics.TargetProps
