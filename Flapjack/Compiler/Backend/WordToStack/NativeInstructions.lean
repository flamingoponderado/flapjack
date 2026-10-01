import Flapjack.Compiler.Backend.WordToStackRegFormat

/-! Native instruction helpers for the literal Word-to-Stack compiler.
The instruction and program payloads use the same positive word width as the
faithful StackSem evaluator. Production routing remains tracked by parent .25.
-/
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackLang
open WordToStackRegFormat (wReg1 wReg2)

/-- Literal register-write helper over the native HOL program carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite1_def"
  (words_as_type_indexed_bitvec)]
def wRegWrite1Native {width : Nat} [NeZero width] (g : Nat → HolProg width)
    (r : Nat) (kf : Nat × Nat × Nat) : HolProg width :=
  let r := r / 2
  if r < kf.1 then g r
  else .seq (g kf.1) (.stackStore kf.1 (kf.2.1 - 1 - (r - kf.1)))

/-- Literal second temporary register-write helper. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wRegWrite2_def"
  (words_as_type_indexed_bitvec)]
def wRegWrite2Native {width : Nat} [NeZero width] (g : Nat → HolProg width)
    (r : Nat) (kf : Nat × Nat × Nat) : HolProg width :=
  let r := r / 2
  if r < kf.1 then g r
  else .seq (g (kf.1 + 1)) (.stackStore (kf.1 + 1) (kf.2.1 - 1 - (r - kf.1)))

/-- Literal ordered frame-slot loads on the native program carrier. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wStackLoad_def"
  (words_as_type_indexed_bitvec)]
def wStackLoadNative {width : Nat} [NeZero width] :
    List (Nat × Nat) → HolProg width → HolProg width
  | [], x => x
  | (r, i) :: ps, x => .seq (.stackLoad r i) (wStackLoadNative ps x)

/-- All literal source instruction clauses, including the 64-bit FP split and
unhandled-instruction catchall. No conversion success or bounds premise. -/
@[hol "cakeml/compiler/backend/word_to_stackScript.sml" "wInst_def"
  (words_as_type_indexed_bitvec)]
def wInstNative {width : Nat} [NeZero width] (i : HolInst width)
    (kf : Nat × Nat × Nat) : HolProg width :=
  match i with
  | .const n c =>
      wRegWrite1Native (fun n => .inst (.const n c)) n kf
  | .arith (.binop bop n1 n2 (.imm imm)) =>
      let l := wReg1 n2 kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun n1 => .inst (.arith (.binop bop n1 l.2 (.imm imm)))) n1 kf)
  | .arith (.binop bop n1 n2 (.reg n3)) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.binop bop n1 l.2 (.reg l'.2)))) n1 kf)
  | .arith (.shift sh n1 n2 (.imm imm)) =>
      let l := wReg1 n2 kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun n1 => .inst (.arith (.shift sh n1 l.2 (.imm imm)))) n1 kf)
  | .arith (.shift sh n1 n2 (.reg n3)) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.shift sh n1 l.2 (.reg l'.2)))) n1 kf)
  | .arith (.div n1 n2 n3) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.div n1 l.2 l'.2))) n1 kf)
  | .arith (.addCarry n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.addCarry n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.addOverflow n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.addOverflow n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.subOverflow n1 n2 n3 n4) =>
      let l := wReg1 n2 kf
      let l' := wReg2 n3 kf
      wStackLoadNative (l.1 ++ l'.1)
        (wRegWrite1Native (fun n1 => .inst (.arith (.subOverflow n1 l.2 l'.2 n4))) n1 kf)
  | .arith (.longMul _ _ _ _) =>
      .inst (.arith (.longMul 3 0 0 2))
  | .arith (.longDiv _ _ _ _ n5) =>
      let l := wReg1 n5 kf
      wStackLoadNative l.1
        (.inst (.arith (.longDiv 0 3 3 0 l.2)))
  | .mem .load n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun n1 => .inst (.mem .load n1 (.addr l.2 offset))) n1 kf)
  | .mem .store n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.inst (.mem .store l2.2 (.addr l1.2 offset)))
  | .mem .load8 n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun n1 => .inst (.mem .load8 n1 (.addr l.2 offset))) n1 kf)
  | .mem .store8 n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.inst (.mem .store8 l2.2 (.addr l1.2 offset)))
  | .mem .load32 n1 (.addr n2 offset) =>
      let l := wReg1 n2 kf
      wStackLoadNative l.1
        (wRegWrite1Native (fun n1 => .inst (.mem .load32 n1 (.addr l.2 offset))) n1 kf)
  | .mem .store32 n1 (.addr n2 offset) =>
      let l1 := wReg1 n2 kf
      let l2 := wReg2 n1 kf
      wStackLoadNative (l1.1 ++ l2.1)
        (.inst (.mem .store32 l2.2 (.addr l1.2 offset)))
  | .fp (.fpLess r f1 f2) =>
      wRegWrite1Native (fun r => .inst (.fp (.fpLess r f1 f2))) r kf
  | .fp (.fpLessEqual r f1 f2) =>
      wRegWrite1Native (fun r => .inst (.fp (.fpLessEqual r f1 f2))) r kf
  | .fp (.fpEqual r f1 f2) =>
      wRegWrite1Native (fun r => .inst (.fp (.fpEqual r f1 f2))) r kf
  | .fp (.fpMovToReg r1 r2 d) =>
      if width = 64 then
        wRegWrite1Native (fun r1 => .inst (.fp (.fpMovToReg r1 0 d))) r1 kf
      else
        wRegWrite2Native
          (fun r2 => wRegWrite1Native (fun r1 => .inst (.fp (.fpMovToReg r1 r2 d))) r1 kf)
          r2 kf
  | .fp (.fpMovFromReg d r1 r2) =>
      let l := wReg1 r1 kf
      let l' := if width = 64 then ([], 0) else wReg2 r2 kf
      wStackLoadNative (l.1 ++ l'.1)
        (.inst (.fp (.fpMovFromReg d l.2 l'.2)))
  | .fp f => .inst (.fp f)
  | _ => .inst .skip


/-- Flapjack-only payload translation; FFI names remain faithful MlString.
There is no HOL original for this representation codec. -/
def toGeneric {width : Nat} [NeZero width] (p : HolProg width) : ProgM (BitVec width) :=
  Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
    HolAddr.toWordLangAddr id p

/-- Flapjack-only transport of the literal register-write helper. -/
theorem toGeneric_wRegWrite1 {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat) :
    toGeneric (wRegWrite1Native g r kf) =
      WordToStackRegFormat.wRegWrite1 (fun n => toGeneric (g n)) r kf := by
  simp only [wRegWrite1Native, WordToStackRegFormat.wRegWrite1]
  split <;> simp [toGeneric, Prog.map]

/-- Flapjack-only transport of the second register-write helper. -/
theorem toGeneric_wRegWrite2 {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat) :
    toGeneric (wRegWrite2Native g r kf) =
      WordToStackRegFormat.wRegWrite2 (fun n => toGeneric (g n)) r kf := by
  simp only [wRegWrite2Native, WordToStackRegFormat.wRegWrite2]
  split <;> simp [toGeneric, Prog.map]

/-- Flapjack-only transport of ordered stack loads. -/
theorem toGeneric_wStackLoad {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) :
    toGeneric (wStackLoadNative loads p) = WordToStack.wStackLoad loads (toGeneric p) := by
  induction loads with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨r, i⟩
    simpa [wStackLoadNative, WordToStack.wStackLoad, toGeneric, Prog.map] using
      congrArg (fun q : ProgM (BitVec width) => StackLang.Prog.seq (StackLang.Prog.stackLoad r i) q) ih

set_option linter.unusedSimpArgs false in
/-- Flapjack-only all-input correspondence with the accepted generic helper.
This proves representation transport, not evaluation or compiler correctness. -/
theorem toGeneric_wInst {width : Nat} [NeZero width]
    (i : HolInst width) (kf : Nat × Nat × Nat) :
    toGeneric (wInstNative i kf) = WordToStackRegFormat.wInst i.toWordLangInst kf := by
  cases i with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals
      simp only [wInstNative, WordToStackRegFormat.wInst, HolInst.toWordLangInst,
        HolArith.toWordLangArith, HolRegImm.toWordRegImm]
      try simp only [toGeneric_wStackLoad, toGeneric_wRegWrite1, toGeneric_wRegWrite2]
      simp [toGeneric, StackLang.Prog.map, HolInst.toWordLangInst,
        HolArith.toWordLangArith, HolRegImm.toWordRegImm]
  | mem op d addr =>
    cases addr
    cases op <;>
      simp only [wInstNative, WordToStackRegFormat.wInst, HolInst.toWordLangInst,
        HolAddr.toWordLangAddr]
    all_goals
      try simp only [toGeneric_wStackLoad, toGeneric_wRegWrite1]
      simp [toGeneric, StackLang.Prog.map, HolInst.toWordLangInst,
        HolAddr.toWordLangAddr]
  | fp f =>
    cases f <;> simp only [wInstNative, WordToStackRegFormat.wInst, HolInst.toWordLangInst]
    all_goals
      by_cases hw : width = 64
      all_goals
        try simp only [hw, if_true, if_false]
        try simp only [toGeneric_wStackLoad, toGeneric_wRegWrite1, toGeneric_wRegWrite2]
        simp [toGeneric, StackLang.Prog.map, HolInst.toWordLangInst]
  | skip => simp [wInstNative, WordToStackRegFormat.wInst, toGeneric, StackLang.Prog.map,
      HolInst.toWordLangInst]
  | const n c =>
    simp only [wInstNative, WordToStackRegFormat.wInst, HolInst.toWordLangInst,
      toGeneric_wRegWrite1]
    simp [toGeneric, StackLang.Prog.map, HolInst.toWordLangInst]

end Flapjack.Compiler.Backend.WordToStack.Native
