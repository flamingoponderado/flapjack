import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Pancake.WordLang

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Full original expression register bound. Lookup is always rejected,
including when the named store would be available; operation lists check every
subexpression. The word dimension is positive as in HOL. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_exp_def"
  (words_as_type_indexed_bitvec)]
def regBoundExp {width : Nat} [NeZero width]
    (expression : WordLangExpHOL (BitVec width)) (bound : Nat) : Prop :=
  match expression with
  | .var register => register < bound
  | .load address => regBoundExp address bound
  | .shift _ first second => regBoundExp first bound ∧ regBoundExp second bound
  | .lookup _ => False
  | .op _ expressions => ∀ e ∈ expressions, regBoundExp e bound
  | .const _ => True

/-- Full original instruction bound. Floating-point register numbers are
ignored except the explicit integer-register fields of comparisons/transfers;
all arithmetic input/output/carry/overflow fields named by HOL are checked. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_inst_def"
  (words_as_type_indexed_bitvec)]
def regBoundInst {width : Nat} [NeZero width] (instruction : HolInst width) (bound : Nat) : Prop :=
  match instruction with
  | .mem _ destination (.addr base _) => destination < bound ∧ base < bound
  | .const destination _ => destination < bound
  | .arith (.shift _ destination source right)
  | .arith (.binop _ destination source right) =>
      source < bound ∧ destination < bound ∧
      (match right with | .reg register => register < bound | .imm _ => True)
  | .arith (.div first second third) => first < bound ∧ second < bound ∧ third < bound
  | .arith (.addCarry first second third fourth)
  | .arith (.addOverflow first second third fourth)
  | .arith (.subOverflow first second third fourth)
  | .arith (.longMul first second third fourth) =>
      first < bound ∧ second < bound ∧ third < bound ∧ fourth < bound
  | .arith (.longDiv first second third fourth fifth) =>
      first < bound ∧ second < bound ∧ third < bound ∧ fourth < bound ∧ fifth < bound
  | .fp (.fpLess register _ _) | .fp (.fpLessEqual register _ _) | .fp (.fpEqual register _ _) =>
      register < bound
  | .fp (.fpMovToReg first second _) | .fp (.fpMovFromReg _ first second) =>
      first < bound ∧ second < bound
  | _ => True

/-- Full original program register bound. Call checks the handler only inside
its SOME-return branch. StackLoad/StackStore check the original FIRST payload
slot, irrespective of its offset label in StackLang documentation. No
additional allocation, raw-call, label or stack-offset guard is introduced. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "reg_bound_def"
  (words_as_type_indexed_bitvec)]
def regBound {width : Nat} [NeZero width] : HolProg width → Nat → Prop
  | .halt register, bound | .raise register, bound | .get register _, bound
  | .locValue register _ _, bound | .ret register, bound => register < bound
  | .opCurrHeap _ first second, bound | .jumpLower first second _, bound =>
      first < bound ∧ second < bound
  | .set name register, bound => register < bound ∧ name ≠ .bitmapBase
  | .storeConsts first second _, bound => 3 < bound ∧ first < bound ∧ second < bound
  | .seq first second, bound => regBound first bound ∧ regBound second bound
  | .ite _ register right first second, bound =>
      register < bound ∧ (match right with | .reg r => r < bound | .imm _ => True) ∧
      regBound first bound ∧ regBound second bound
  | .loop body, bound => regBound body bound
  | .ffi _ first second third fourth fifth, bound
  | .install first second third fourth fifth, bound =>
      first < bound ∧ second < bound ∧ third < bound ∧ fourth < bound ∧ fifth < bound
  | .call returns target handler, bound =>
      (match target with | .inr register => register < bound | .inl _ => True) ∧
      (match returns with
       | none => True
       | some (body, register, _, _) => regBound body bound ∧ register < bound ∧
           (match handler with | none => True | some (body, _, _) => regBound body bound))
  | .shMemOp _ register (.addr base _), bound => register < bound ∧ base < bound
  | .codeBufferWrite first second, bound | .dataBufferWrite first second, bound
  | .bitmapLoad first second, bound => first < bound ∧ second < bound
  | .inst instruction, bound => regBoundInst instruction bound
  | .stackStore first _, bound | .stackLoad first _, bound
  | .stackSetSize first, bound | .stackGetSize first, bound => first < bound
  | .stackLoadAny first second, bound | .stackStoreAny first second, bound =>
      first < bound ∧ second < bound
  | _, _ => True

end Flapjack.Compiler.Backend.StackProps
