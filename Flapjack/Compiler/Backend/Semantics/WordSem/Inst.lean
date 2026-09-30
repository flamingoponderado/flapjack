import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.Misc.BinaryIeeeArith
import Flapjack.Misc.BinaryIeeeConvert
import Flapjack.Misc.BinaryIeeeSqrt
import Flapjack.FpSemHOL

/-!
# Exact HOL `wordSem$inst_def`

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:716-939`
(bead `flapjack-h29l.6`): the semantics of one `asm$inst`.  It covers `Skip`,
`Const`, the eight `Arith` forms, the eight `Mem` forms, and the sixteen `FP`
forms, over the tagged `WordSemStateFiniteExact`.

The binary64 operations are the HOL standard-library renderings:
* comparisons and sign operations from `Flapjack.Misc.MachineIeee`;
* `fp64_add`/`sub`/`mul`/`div` from `Flapjack.Misc.BinaryIeeeArith`;
* the tagged `fpSem` `fpfma` (`fpSemFpfma`);
* `fp64_sqrt` from `Flapjack.Misc.BinaryIeeeSqrt`, the rational-cut
  rendering;
* `fp64_to_int` and `int_to_fp64` from `Flapjack.Misc.BinaryIeeeConvert`.

Their choice-based rounding and unspecified NaN results make `inst`
`noncomputable`.  The `roundTiesToEven` conformance theorems
(`holFp64Add_rte` and the others) rewrite every non-NaN result to the
computable algorithms.  The HOL `words` operations are:
* `w2w` is `BitVec.setWidth`, `w2i` is `BitVec.toInt`, and `i2w` is
  `BitVec.ofInt`;
* `n2w`/`w2n` are `BitVec.ofNat`/`toNat`, and `dimword (:'a)` is
  `2 ^ width`;
* word `/` is unsigned `BitVec` division;
* `word_extract` is `holWordExtract`, `bit_field_insert` is
  `holBitFieldInsert`, and `@@` into `word64` is concatenation followed by
  `setWidth 64`.
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

/-- Rendering of HOL `inst_def` (`wordSemScript.sml:716-939`); see the module
    docstring for the operation renderings.  Clause by clause:
    * `Skip` leaves the state unchanged, `Const` assigns `Const w`, and
      `Binop`/`Shift` assign the `Op`/`Shift` expression over `Var` and the
      register-or-immediate.
    * `Div`, `AddCarry`, `AddOverflow`, `SubOverflow`, `LongMul` and
      `LongDiv` read their operands with `get_vars` and write through
      `set_var`.  `Div` fails on a zero divisor, and `LongDiv` fails on a
      zero divisor or a quotient `≥ dimword`.
    * `Mem` computes the address `Var a + Const w` with `word_exp` and uses
      `mem_load`/`mem_store` or the byte/32-bit auxiliaries.  `Load16` and
      `Store16` fail.
    * `FP` reads and writes the `fp_regs` through `get_fp_var`/`set_fp_var`.
      Its `dimindex (:'a) = 64` tests are `width = 64`.

    Not an exact port: the `@[hol]` tag is withdrawn (bead `flapjack-2hoy.2`).
    The `FPSqrt` clause calls `holFp64Sqrt` (`BinaryIeeeSqrt`).  HOL
    `fp64_sqrt` rounds the real `sqrt r`, but `holFp64Sqrt` replaces each
    comparison against `sqrt r` with a rational cut criterion.  That is a
    reformulation of the specification, not an admitted carrier translation.
    Its agreement with HOL is the external assumption of `docs/SOUNDNESS.md`
    item 8.  The faithful rendering is bead `flapjack-dshl`.

    Every other clause matches HOL clause by clause.  The other FP clauses use
    the binary64 renderings over `Rat`.  Floats have dyadic rational values,
    so those renderings reach only rational arguments (see the `fpSem`
    comparison and arithmetic declarations for the argument).
    `real_to_float` is reached only through `int_to_fp64` in `FPFromInt`, with
    an integer argument (`w2i` of an extracted word).  NaN results are HOL's
    unspecified `float_some_qnan`, rendered by `Classical.epsilon` on the same
    predicate. -/
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
      | some [.word q, .word w2] => if q ≠ 0 then some (setVar r1 (.word (w2 / q)) s) else none
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
  | .fp (.fpLess r d1 d2) =>
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 => some (setVar r (.word (if holFp64LessThan f1 f2 then 1 else 0)) s)
      | _, _ => none
  | .fp (.fpLessEqual r d1 d2) =>
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 => some (setVar r (.word (if holFp64LessEqual f1 f2 then 1 else 0)) s)
      | _, _ => none
  | .fp (.fpEqual r d1 d2) =>
      match getFpVar d1 s, getFpVar d2 s with
      | some f1, some f2 => some (setVar r (.word (if holFp64Equal f1 f2 then 1 else 0)) s)
      | _, _ => none
  | .fp (.fpMov d1 d2) =>
      match getFpVar d2 s with
      | some f => some (setFpVar d1 f s)
      | _ => none
  | .fp (.fpAbs d1 d2) =>
      match getFpVar d2 s with
      | some f => some (setFpVar d1 (holFp64Abs f) s)
      | _ => none
  | .fp (.fpNeg d1 d2) =>
      match getFpVar d2 s with
      | some f => some (setFpVar d1 (holFp64Negate f) s)
      | _ => none
  | .fp (.fpSqrt d1 d2) =>
      match getFpVar d2 s with
      | some f => some (setFpVar d1 (holFp64Sqrt .roundTiesToEven f) s)
      | _ => none
  | .fp (.fpAdd d1 d2 d3) =>
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Add .roundTiesToEven f1 f2) s)
      | _, _ => none
  | .fp (.fpSub d1 d2 d3) =>
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Sub .roundTiesToEven f1 f2) s)
      | _, _ => none
  | .fp (.fpMul d1 d2 d3) =>
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Mul .roundTiesToEven f1 f2) s)
      | _, _ => none
  | .fp (.fpDiv d1 d2 d3) =>
      match getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2 => some (setFpVar d1 (holFp64Div .roundTiesToEven f1 f2) s)
      | _, _ => none
  | .fp (.fpFma d1 d2 d3) =>
      match getFpVar d1 s, getFpVar d2 s, getFpVar d3 s with
      | some f1, some f2, some f3 => some (setFpVar d1 (fpSemFpfma f1 f2 f3) s)
      | _, _, _ => none
  | .fp (.fpMovToReg r1 r2 d) =>
      match getFpVar d s with
      | some v =>
          if width = 64 then some (setVar r1 (.word (v.setWidth width)) s)
          else some (setVar r2 (.word (holWordExtract 63 32 v width))
            (setVar r1 (.word (holWordExtract 31 0 v width)) s))
      | _ => none
  | .fp (.fpMovFromReg d r1 r2) =>
      if width = 64 then
        match getVar r1 s with
        | some (.word w1) => some (setFpVar d (w1.setWidth 64) s)
        | _ => none
      else
        match getVar r1 s, getVar r2 s with
        | some (.word w1), some (.word w2) => some (setFpVar d ((w2 ++ w1).setWidth 64) s)
        | _, _ => none
  | .fp (.fpToInt d1 d2) =>
      match getFpVar d2 s with
      | none => none
      | some f =>
          match holFp64ToInt .roundTiesToEven f with
          | none => none
          | some i =>
              let w : BitVec 32 := BitVec.ofInt 32 i
              if w.toInt = i then
                (if width = 64 then some (setFpVar d1 (w.setWidth 64) s)
                 else
                  match getFpVar (d1 / 2) s with
                  | none => none
                  | some f =>
                      let (h, l) := if d1 % 2 = 1 then (63, 32) else (31, 0)
                      some (setFpVar (d1 / 2) (holBitFieldInsert h l w f) s))
              else none
  | .fp (.fpFromInt d1 d2) =>
      if width = 64 then
        match getFpVar d2 s with
        | some f =>
            let i := (holWordExtract 31 0 f 32).toInt
            some (setFpVar d1 (holIntToFp64 .roundTiesToEven i) s)
        | none => none
      else
        match getFpVar (d2 / 2) s with
        | some v =>
            let i := (if d2 % 2 = 1 then holWordExtract 63 32 v width
              else holWordExtract 31 0 v width).toInt
            some (setFpVar d1 (holIntToFp64 .roundTiesToEven i) s)
        | none => none

end WordSemStateFiniteExact

end Flapjack
