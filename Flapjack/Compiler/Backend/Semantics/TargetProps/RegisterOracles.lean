import Flapjack.Compiler.Backend.Semantics.TargetProps.InterferenceSequence

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source253: exact interference position/application selection and native register residue. The IO name argument is retained although unused; FP fallback is fixed word64. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_io_regs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def targetIoRegs {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (k : Nat) (_name : HolFfiName) (r : Nat) : Option (BitVec width) :=
  match interferencePos (fun app => isFfiApp app = true) mc ffi ms k with
  | none => none
  | some n => match interferenceAppSeq mc ffi ms n with
    | some (.ffiApp _ _ _ post, _, _) => if r ∈ mc.calleeSavedRegs ∨ ¬ r < mc.target.config.regCount ∨ r ∈ mc.target.config.avoidRegs then none
          else some (mc.target.getReg post r)
    | _ => none

/-- Literal source268: exact interference position/application selection and native register residue. The IO name argument is retained although unused; FP fallback is fixed word64. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_io_fp_regs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def targetIoFpRegs {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (k : Nat) (i : Nat) : BitVec 64 :=
  match interferencePos (fun app => isFfiApp app = true) mc ffi ms k with
  | none => 0
  | some n => match interferenceAppSeq mc ffi ms n with
    | some (.ffiApp _ _ _ post, _, _) => mc.target.getFpReg post i
    | _ => 0

/-- Literal source279: exact interference position/application selection and native register residue. The IO name argument is retained although unused; FP fallback is fixed word64. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_cc_regs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def targetCcRegs {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (k : Nat) (r : Nat) : Option (BitVec width) :=
  match interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k with
  | none => none
  | some n => match interferenceAppSeq mc ffi ms n with
    | some (.ccApp _ _ _ post, _, _) => if r ∈ mc.calleeSavedRegs ∨ r = mc.ptrReg ∨ ¬ r < mc.target.config.regCount ∨ r ∈ mc.target.config.avoidRegs then none
          else some (mc.target.getReg post r)
    | _ => none

/-- Literal source294: exact interference position/application selection and native register residue. The IO name argument is retained although unused; FP fallback is fixed word64. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml" "target_cc_fp_regs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def targetCcFpRegs {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S) (k : Nat) (i : Nat) : BitVec 64 :=
  match interferencePos (fun app => ¬ isFfiApp app = true) mc ffi ms k with
  | none => 0
  | some n => match interferenceAppSeq mc ffi ms n with
    | some (.ccApp _ _ _ post, _, _) => mc.target.getFpReg post i
    | _ => 0

end Flapjack.Compiler.Backend.Semantics.TargetProps
