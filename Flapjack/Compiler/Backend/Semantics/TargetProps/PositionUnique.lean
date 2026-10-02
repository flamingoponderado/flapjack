import Flapjack.Compiler.Backend.Semantics.TargetProps.SequenceLaws

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source411: a present selected application strictly increases the count at every later index. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_count_lt" (words_as_type_indexed_bitvec)]
theorem interferenceCountLt {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (n n2 : Nat)
    (app : InterferenceApp width S) (mc' : MachineConfig width S Q) (ffi' : HolFfiState σ)
    (h : interferenceAppSeq mc ffi ms n = some (app, mc', ffi') ∧ P app ∧ n < n2) :
    interferenceCount P mc ffi ms n < interferenceCount P mc ffi ms n2 := by
  have hs : interferenceCount P mc ffi ms (n + 1) = interferenceCount P mc ffi ms n + 1 := by
    simp [interferenceCount, h.1, h.2.1]
  have hm := interferenceCountMono P mc ffi ms (n2 - (n + 1)) (n + 1)
  have hi : (n + 1) + (n2 - (n + 1)) = n2 := by omega
  rw [hi, hs] at hm
  omega

/-- Literal source425: selected present applications with equal preceding counts have the same index. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "interference_pos_unique" (words_as_type_indexed_bitvec)]
theorem interferencePosUnique {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (P : InterferenceApp width S → Prop)
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (n1 n2 : Nat)
    (app1 app2 : InterferenceApp width S) (mc1' mc2' : MachineConfig width S Q)
    (ffi1' ffi2' : HolFfiState σ)
    (h : interferenceAppSeq mc ffi ms n1 = some (app1, mc1', ffi1') ∧ P app1 ∧
      interferenceAppSeq mc ffi ms n2 = some (app2, mc2', ffi2') ∧ P app2 ∧
      interferenceCount P mc ffi ms n1 = interferenceCount P mc ffi ms n2) : n1 = n2 := by
  rcases h with ⟨hs1, hp1, hs2, hp2, hc⟩
  by_cases hn : n1 = n2
  · exact hn
  by_cases hl : n1 < n2
  · have ht := interferenceCountLt P mc ffi ms n1 n2 app1 mc1' ffi1' ⟨hs1, hp1, hl⟩
    omega
  · have hl' : n2 < n1 := by omega
    have ht := interferenceCountLt P mc ffi ms n2 n1 app2 mc2' ffi2' ⟨hs2, hp2, hl'⟩
    omega

end Flapjack.Compiler.Backend.Semantics.TargetProps
