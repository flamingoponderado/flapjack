import Flapjack.Compiler.Backend.Semantics.TargetProps.PositionLaws

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Flapjack choice infrastructure: a successor correspondence between predicates
and uniqueness of the suffix witness determines the mapped guarded choice.
This helper has no standalone HOL original; the literal HOL laws below discharge
its premises from the native application sequence and count equations. -/
private theorem optionSomeSucc (P Q : Nat → Prop)
    (h : ∀ n, P n ↔ ∃ m, n = m + 1 ∧ Q m)
    (hu : ∀ a b, Q a → Q b → a = b) :
    holOptionSome P = (holOptionSome Q).map (fun n => n + 1) := by
  unfold holOptionSome
  by_cases hex : ∃ m, Q m
  · have hp : ∃ n, P n := by
      obtain ⟨m, hm⟩ := hex
      exact ⟨m + 1, (h _).2 ⟨m, rfl, hm⟩⟩
    rw [dif_pos hp, dif_pos hex]
    simp only [Option.map_some]
    congr 1
    obtain ⟨m, he, hm⟩ := (h _).1 (Classical.choose_spec hp)
    have hm' := hu m (Classical.choose hex) hm (Classical.choose_spec hex)
    omega
  · have hp : ¬ ∃ n, P n := by
      rintro ⟨n, hn⟩
      obtain ⟨m, _, hm⟩ := (h n).1 hn
      exact hex ⟨m, hm⟩
    rw [dif_neg hp, dif_neg hex]
    rfl

/-- Literal source468: the hit suffix position shifts by successor, including absence. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_pos_tail_hit" (words_as_type_indexed_bitvec)]
theorem interferencePosTailHit {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (app0 : InterferenceApp width S) (mcc : MachineConfig width S Q)
    (ffic : HolFfiState σ) (k : Nat)
    (h : nextInterference mc ffi ms = some (app0, mcc, ffic) ∧ P app0) :
    interferencePos P mc ffi ms (k + 1) =
      (interferencePos P mcc ffic (appPost app0) k).map (fun n => n + 1) := by
  unfold interferencePos
  apply optionSomeSucc
  · intro n
    cases n with
    | zero => simp [interferenceCount, interferenceAppSeq, h.1, h.2]
    | succ n =>
      simp only [interferenceCountTail P mc ffi ms app0 mcc ffic h.1 n,
        interferenceAppSeqTail mc ffi ms app0 mcc ffic h.1 n]
      simp [h.2]
      intro app mc' ffi' hs hp
      omega
  · intro a b ha hb
    obtain ⟨hca, appa, mca, ffia, hsa, hpa⟩ := ha
    obtain ⟨hcb, appb, mcb, ffib, hsb, hpb⟩ := hb
    exact interferencePosUnique P mcc ffic (appPost app0) a b appa appb mca mcb ffia ffib
      ⟨hsa, hpa, hsb, hpb, hca.trans hcb.symm⟩

/-- Literal source498: the miss suffix position shifts by successor, including absence. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_pos_tail_miss" (words_as_type_indexed_bitvec)]
theorem interferencePosTailMiss {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (app0 : InterferenceApp width S) (mcc : MachineConfig width S Q)
    (ffic : HolFfiState σ) (k : Nat)
    (h : nextInterference mc ffi ms = some (app0, mcc, ffic) ∧ ¬ P app0) :
    interferencePos P mc ffi ms k =
      (interferencePos P mcc ffic (appPost app0) k).map (fun n => n + 1) := by
  unfold interferencePos
  apply optionSomeSucc
  · intro n
    cases n with
    | zero => simp [interferenceCount, interferenceAppSeq, h.1, h.2]
    | succ n =>
      simp only [interferenceCountTail P mc ffi ms app0 mcc ffic h.1 n,
        interferenceAppSeqTail mc ffi ms app0 mcc ffic h.1 n]
      simp [h.2]
  · intro a b ha hb
    obtain ⟨hca, appa, mca, ffia, hsa, hpa⟩ := ha
    obtain ⟨hcb, appb, mcb, ffib, hsb, hpb⟩ := hb
    exact interferencePosUnique P mcc ffic (appPost app0) a b appa appb mca mcb ffia ffib
      ⟨hsa, hpa, hsb, hpb, hca.trans hcb.symm⟩

end Flapjack.Compiler.Backend.Semantics.TargetProps
