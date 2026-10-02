import Flapjack.Compiler.Backend.Semantics.TargetProps.SearchMono
import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceSequence

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source333: a successful finite clock search fixes the result of
unbounded HOL option choice. Existence and uniqueness are proved, not assumed. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "next_interference_intro" (words_as_type_indexed_bitvec)]
theorem nextInterferenceIntro {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (k : Nat) (ms : S)
    (res : InterferenceApp width S × MachineConfig width S Q × HolFfiState σ)
    (h : findNextInterference mc ffi k ms = some res) :
    nextInterference mc ffi ms = some res := by
  unfold nextInterference holOptionSome
  split
  · rename_i hex
    apply congrArg Option.some
    obtain ⟨k', hk'⟩ := Classical.choose_spec hex
    exact findNextInterferenceUnique mc ffi ms k' k (Classical.choose hex) res ⟨hk', h⟩
  · rename_i hn
    exact False.elim (hn ⟨res, k, h⟩)

/-- Literal source343: equality of all shifted search results implies equality
of the complete unbounded next-interference result. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "next_interference_shift" (words_as_type_indexed_bitvec)]
theorem nextInterferenceShift {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc1 mc2 : MachineConfig width S Q)
    (ffi1 ffi2 : HolFfiState σ) (ms1 ms2 : S) (l : Nat)
    (h : ∀ k, findNextInterference mc1 ffi1 (k + l) ms1 =
      findNextInterference mc2 ffi2 k ms2) :
    nextInterference mc1 ffi1 ms1 = nextInterference mc2 ffi2 ms2 := by
  unfold nextInterference
  apply congrArg holOptionSome
  funext res
  apply propext
  constructor
  · rintro ⟨k, hk⟩
    have hs := findNextInterferenceMono k mc1 ffi1 ms1 res l hk
    rw [h k] at hs
    exact ⟨k, hs⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + l, (h k).trans hk⟩

end Flapjack.Compiler.Backend.Semantics.TargetProps
