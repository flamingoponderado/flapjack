import Flapjack.Compiler.Backend.Semantics.TargetProps.FindNextInterference
import Flapjack.Misc.Option

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal HOL Source215-218: option choice over all successful clock limits. Choices remain unspecified; no bounded search or uniqueness premise. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "next_interference_def"
  (words_as_type_indexed_bitvec)]
noncomputable def nextInterference {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) :=
  holOptionSome (fun res => ∃ k, findNextInterference mc ffi k ms = some res)

/-- Literal HOL Source221-228: advance using the returned configuration, FFI and application post state. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_app_seq_def"
  (words_as_type_indexed_bitvec)]
noncomputable def interferenceAppSeq {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) : Nat →
      Option (InterferenceApp width state × MachineConfig width state projection × HolFfiState σ)
  | 0 => nextInterference mc ffi ms
  | n + 1 => match nextInterference mc ffi ms with
    | none => none
    | some (app, mc', ffi') => interferenceAppSeq mc' ffi' (appPost app) n

/-- Literal HOL Source230-238: count matching applications strictly below n; missing applications contribute zero. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_count_def"
  (words_as_type_indexed_bitvec)]
noncomputable def interferenceCount {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (P : InterferenceApp width state → Prop)
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) : Nat → Nat
  | 0 => 0
  | n + 1 => interferenceCount P mc ffi ms n +
    match interferenceAppSeq mc ffi ms n with
    | some (app, _, _) => if P app then 1 else 0
    | none => 0

/-- Literal HOL Source241-249: option choice of a present matching application with preceding count k; no existence or uniqueness assumption. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "interference_pos_def"
  (words_as_type_indexed_bitvec)]
noncomputable def interferencePos {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (P : InterferenceApp width state → Prop)
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) (k : Nat) :=
  holOptionSome (fun n => interferenceCount P mc ffi ms n = k ∧
    ∃ app mc' ffi', interferenceAppSeq mc ffi ms n = some (app, mc', ffi') ∧ P app)

end Flapjack.Compiler.Backend.Semantics.TargetProps
