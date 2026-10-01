import Flapjack.Compiler.Backend.Semantics.StackSem.Expressions

/-! Integer/memory cases of stackSemScript.sml inst_def:408-522.
This partial helper returns outer NONE only for FP (not handled here).
Inner NONE is the original instruction failure. No whole inst_def HOL tag
applies to this assembly fragment; `StackSemInst.instHOL` composes it with the
FP fragment. Its stronger real-carrier acceptance is tracked separately. -/
namespace Flapjack.StackSemIntegerInstructions
open StackSemStateOps StackSemExpressions Compiler.Encoders.Asm

/-- Literal HOL words$word_quot_def sign cases. HOL `/` is signed;
unsigned word_div is HOL `//`. This local rendering also retains DIV-zero
behavior, although the instruction guards against a zero divisor. -/
def wordQuot {width : Nat} (a b : BitVec width) : BitVec width :=
  if a.msb then
    if b.msb then (-a) / (-b) else -((-a) / b)
  else
    if b.msb then -(a / (-b)) else a / b

/-- Source-matched integer/memory dispatch. The same-register Or case copies
Word or Loc directly, unlike the general arithmetic branch. -/
def instInteger {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemStateFiniteExact width C F)) :=
  match i with
  | .fp _ => none
  | _ => some (match i with
    | .skip => some s
    | .const reg w => assign reg (.const w) s
    | .arith (.binop bop r1 r2 ri) =>
        if (bop == .or) && (match ri with | .reg r3 => r3 == r2 | .imm _ => false) then
          match s.regs.lookup r2 with
          | none => none
          | some value => some (setVar r1 value s)
        else
          assign r1 (.op bop [.var r2, match ri with | .reg r3 => .var r3 | .imm w => .const w]) s
    | .arith (.shift sh r1 r2 ri) =>
        assign r1 (.shift sh (.var r2) (match ri with | .reg r3 => .var r3 | .imm w => .const w)) s
    | .arith (.div r1 r2 r3) =>
        match getVars [r3, r2] s with
        | some [.word q, .word w2] => if q ≠ 0 then some (setVar r1 (.word (wordQuot w2 q)) s) else none
        | _ => none
    | .arith (.addCarry r1 r2 r3 r4) =>
        match getVars [r2, r3, r4] s with
        | some [.word l, .word r, .word c] =>
            let res := l.toNat + r.toNat + (if c = 0 then 0 else 1)
            some (setVar r4 (.word (if 2 ^ width ≤ res then 1 else 0))
              (setVar r1 (.word (BitVec.ofNat width res)) s))
        | _ => none
    | .arith (.addOverflow r1 r2 r3 r4) =>
        match getVars [r2, r3] s with
        | some [.word w2, .word w3] =>
            some (setVar r4 (.word (if (w2 + w3).toInt ≠ w2.toInt + w3.toInt then 1 else 0))
              (setVar r1 (.word (w2 + w3)) s))
        | _ => none
    | .arith (.subOverflow r1 r2 r3 r4) =>
        match getVars [r2, r3] s with
        | some [.word w2, .word w3] =>
            some (setVar r4 (.word (if (w2 - w3).toInt ≠ w2.toInt - w3.toInt then 1 else 0))
              (setVar r1 (.word (w2 - w3)) s))
        | _ => none
    | .arith (.longMul r1 r2 r3 r4) =>
        match getVars [r3, r4] s with
        | some [.word w3, .word w4] =>
            let r := w3.toNat * w4.toNat
            some (setVar r2 (.word (BitVec.ofNat width r))
              (setVar r1 (.word (BitVec.ofNat width (r / 2 ^ width))) s))
        | _ => none
    | .arith (.longDiv r1 r2 r3 r4 r5) =>
        match getVars [r3, r4, r5] s with
        | some [.word w3, .word w4, .word w5] =>
            let n := w3.toNat * 2 ^ width + w4.toNat
            let d := w5.toNat
            let q := n / d
            if d ≠ 0 ∧ q < 2 ^ width then
              some (setVar r1 (.word (BitVec.ofNat width q))
                (setVar r2 (.word (BitVec.ofNat width (n % d))) s))
            else none
        | _ => none
    | .mem .load r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]) with
        | some w =>
            match memLoad w s with
            | none => none
            | some w => some (setVar r w s)
        | _ => none
    | .mem .load8 r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]) with
        | some w =>
            match memLoadByteAuxExact s.memory s.mdomain s.be w with
            | none => none
            | some w => some (setVar r (.word (w.setWidth width)) s)
        | _ => none
    | .mem .load16 _ _ => none
    | .mem .load32 r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]) with
        | some w =>
            match memLoad32Exact s.memory s.mdomain s.be w with
            | none => none
            | some w => some (setVar r (.word (w.setWidth width)) s)
        | _ => none
    | .mem .store r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]), getVar r s with
        | some a, some w =>
            match memStore a w s with
            | some s1 => some s1
            | none => none
        | _, _ => none
    | .mem .store8 r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]), getVar r s with
        | some a, some (.word w) =>
            match memStoreByteAuxExact s.memory s.mdomain s.be a (w.setWidth 8) with
            | some newM => some { s with memory := newM }
            | none => none
        | _, _ => none
    | .mem .store16 _ _ => none
    | .mem .store32 r (.addr a w) =>
        match wordExp s (.op .add [.var a, .const w]), getVar r s with
        | some a, some (.word w) =>
            match memStore32Exact s.memory s.mdomain s.be a (w.setWidth 32) with
            | some newM => some { s with memory := newM }
            | none => none
        | _, _ => none
    | .fp _ => none)

/-- The executable guard is exactly HOL's bop=Or and ri=Reg r2 test;
these are constructor and natural-number equalities, not host string keys. -/
theorem sameRegisterOr_iff {width : Nat} [NeZero width]
    (bop : BinOp) (ri : HolRegImm width) (source : Nat) :
    ((bop == .or) && (match ri with | .reg name => name == source | .imm _ => false)) = true ↔
      bop = .or ∧ ri = .reg source := by
  cases bop <;> cases ri <;> simp [BEq.beq]

/-- Assembly equation for the source's special Or copy, including Loc values. -/
theorem instInteger_or_self {width : Nat} [NeZero width] {C F : Type}
    (destination source : Nat) (s : StackSemStateFiniteExact width C F) :
    instInteger (.arith (.binop .or destination source (.reg source))) s =
      some (match s.regs.lookup source with
        | none => none
        | some value => some (setVar destination value s)) := by
  simp [instInteger]

/-- Flapjack factoring of the accepted domain-checked memory update. -/
theorem memStore_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (address : BitVec width) (value : WordLocW width)
    (s t : StackSemStateFiniteExact width C F)
    (h : memStore address value s = some t) : t.clock = s.clock := by
  simp only [memStore] at h
  split at h
  · cases h; rfl
  · contradiction

/-- Every successful handled instruction preserves the clock. This Flapjack
assembly fact assumes only the instruction's own successful execution. -/
theorem instInteger_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instInteger i s = some (some t)) : t.clock = s.clock := by
  cases i <;> simp only [instInteger] at h
  all_goals repeat' (split at h)
  all_goals try contradiction
  all_goals try simp only [assign] at h
  all_goals try simp only [memStore] at h
  all_goals repeat' (split at h)
  all_goals try contradiction
  all_goals cases h
  all_goals first | rfl | exact memStore_clock_eq _ _ _ _ (by assumption)

end Flapjack.StackSemIntegerInstructions
