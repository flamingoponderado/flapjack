import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.BackendCommon

/-! Integer-only instruction semantics for the riscv-mi compiler branch.
The instruction carrier contains Skip, Const, arithmetic and memory operations.
This restriction intentionally differs from the original HOL instruction type.
-/

namespace Flapjack

namespace WordSemInstSupport

/-- Canonical finite-support roundtrip for the `fpRegs`/`store` fields that
    `inst` reads and writes.  Kept for the exact `inst_def` port (bead
    `flapjack-dshl`); `inst` itself is currently untagged. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemInstSupport

/-- HOL `words$word_extract h l w : 'b word = w2w ((h -- l) w)`, where
    `word_bits h l` keeps bits `l ..= MIN h (dimindex (:'a) - 1)` shifted to
    the bottom.  Untagged HOL standard-library helper. -/
def holWordExtract (h l : Nat) {n : Nat} (v : BitVec n) (m : Nat) : BitVec m :=
  BitVec.ofNat m ((v.toNat >>> l) % 2 ^ (min h (n - 1) + 1 - l))

/-- HOL `words$bit_field_insert h l a w`: `word_modify (λi. COND (l ≤ i ∧ i ≤
    h) (a ' (i - l)))` on `w`.  It replaces bits `l ..= h` of `w` with the low
    bits of `a`.  HOL leaves `a ' j` unspecified for `j ≥ dimindex (:'b)`, and
    this rendering reads such bits as zero; `inst_def` only inserts a
    `word32` into 32-bit fields, so it never reaches that case.  Untagged
    HOL standard-library helper. -/
def holBitFieldInsert (h l : Nat) {k n : Nat} (a : BitVec k) (w : BitVec n) : BitVec n :=
  let mask : BitVec n := BitVec.ofNat n ((2 ^ (h + 1 - l) - 1) * 2 ^ l)
  (w &&& ~~~mask) ||| ((a.setWidth n <<< l) &&& mask)

namespace WordSemStateFiniteExact

/-- Execute the integer-only instruction carrier. Missing operands and invalid
memory operations fail. Compatibility FP register fields are never accessed. -/
noncomputable def inst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemStateFiniteExact width C F) :=
  match i with
  | .skip => some s
  | .const reg w => assign reg (.const w) s
  | .arith (.binop bop r1 r2 ri) =>
      assign r1 (.op bop [.var r2, match ri with | .reg r3 => .var r3 | .imm w => .const w]) s
  | .arith (.shift sh r1 r2 ri) =>
      assign r1 (.shift sh (.var r2) (match ri with | .reg r3 => .var r3 | .imm w => .const w)) s
  | .arith (.div r1 r2 r3) =>
      match getVars [r3, r2] s with
      | some [.word q, .word w2] => if q ≠ 0 then some (setVar r1 (.word (w2.sdiv q)) s) else none
      | _ => none
  | .arith (.addCarry r1 r2 r3 r4) =>
      match getVars [r2, r3, r4] s with
      | some [.word l, .word r, .word c] =>
          let (res, co) := wordAddCarryHOL l r c
          some (setVar r4 (.word co) (setVar r1 (.word res) s))
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
      | some (.word w) =>
          match memLoad w s with
          | none => none
          | some w => some (setVar r w s)
      | _ => none
  | .mem .load8 r (.addr a w) =>
      match wordExp s (.op .add [.var a, .const w]) with
      | some (.word w) =>
          match memLoadByteAuxExact s.memory s.mdomain s.be w with
          | none => none
          | some w => some (setVar r (.word (w.setWidth width)) s)
      | _ => none
  | .mem .load16 _ _ => none
  | .mem .load32 r (.addr a w) =>
      match wordExp s (.op .add [.var a, .const w]) with
      | some (.word w) =>
          match memLoad32Exact s.memory s.mdomain s.be w with
          | none => none
          | some w => some (setVar r (.word (w.setWidth width)) s)
      | _ => none
  | .mem .store r (.addr a w) =>
      match wordExp s (.op .add [.var a, .const w]), getVar r s with
      | some (.word a), some w =>
          match memStore a w s with
          | some s1 => some s1
          | none => none
      | _, _ => none
  | .mem .store8 r (.addr a w) =>
      match wordExp s (.op .add [.var a, .const w]), getVar r s with
      | some (.word a), some (.word w) =>
          match memStoreByteAuxExact s.memory s.mdomain s.be a (w.setWidth 8) with
          | some newM => some { s with memory := newM }
          | none => none
      | _, _ => none
  | .mem .store16 _ _ => none
  | .mem .store32 r (.addr a w) =>
      match wordExp s (.op .add [.var a, .const w]), getVar r s with
      | some (.word a), some (.word w) =>
          match memStore32Exact s.memory s.mdomain s.be a (w.setWidth 32) with
          | some newM => some { s with memory := newM }
          | none => none
      | _, _ => none
end WordSemStateFiniteExact

end Flapjack
