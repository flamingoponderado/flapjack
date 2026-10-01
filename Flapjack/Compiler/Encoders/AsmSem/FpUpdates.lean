import Flapjack.Compiler.Encoders.AsmSem.Arithmetic
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

/-! Native asmSem floating-point transition. IEEE primitives use the reviewed
reals_as_rational_cuts translation and SOUNDNESS item 8. Raw machine words,
fixed word64 FP registers, original paired aliases and failed writes retained. -/
namespace Flapjack.Compiler.Encoders.AsmSem
open Flapjack Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/encoders/asm/asmSemScript.sml" "fp_upd_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def fpUpd {width : Nat} [NeZero width] (operation : HolFp)
    (s : AsmState width) : AsmState width :=
  match operation with
  | .fpLess r d1 d2 => updReg r
      (if holFp64LessThan (readFpReg d1 s) (readFpReg d2 s) then 1 else 0) s
  | .fpLessEqual r d1 d2 => updReg r
      (if holFp64LessEqual (readFpReg d1 s) (readFpReg d2 s) then 1 else 0) s
  | .fpEqual r d1 d2 => updReg r
      (if holFp64Equal (readFpReg d1 s) (readFpReg d2 s) then 1 else 0) s
  | .fpMov d1 d2 => updFpReg d1 (readFpReg d2 s) s
  | .fpAbs d1 d2 => updFpReg d1 (holFp64Abs (readFpReg d2 s)) s
  | .fpNeg d1 d2 => updFpReg d1 (holFp64Negate (readFpReg d2 s)) s
  | .fpSqrt d1 d2 => updFpReg d1 (holFp64Sqrt .roundTiesToEven (readFpReg d2 s)) s
  | .fpAdd d1 d2 d3 => updFpReg d1 (holFp64Add .roundTiesToEven
      (readFpReg d2 s) (readFpReg d3 s)) s
  | .fpSub d1 d2 d3 => updFpReg d1 (holFp64Sub .roundTiesToEven
      (readFpReg d2 s) (readFpReg d3 s)) s
  | .fpMul d1 d2 d3 => updFpReg d1 (holFp64Mul .roundTiesToEven
      (readFpReg d2 s) (readFpReg d3 s)) s
  | .fpDiv d1 d2 d3 => updFpReg d1 (holFp64Div .roundTiesToEven
      (readFpReg d2 s) (readFpReg d3 s)) s
  | .fpFma d1 d2 d3 => updFpReg d1 (holFp64MulAdd .roundTiesToEven
      (readFpReg d2 s) (readFpReg d3 s) (readFpReg d1 s)) s
  | .fpMovToReg r1 r2 d =>
      if width = 64 then updReg r1 ((readFpReg d s).setWidth width) s
      else let value := readFpReg d s
        updReg r2 (holWordExtract 63 32 value width)
          (updReg r1 (holWordExtract 31 0 value width) s)
  | .fpMovFromReg d r1 r2 =>
      updFpReg d (if width = 64 then (readReg r1 s).setWidth 64
        else ((readReg r2 s) ++ (readReg r1 s)).setWidth 64) s
  | .fpToInt d1 d2 =>
      match holFp64ToInt .roundTiesToEven (readFpReg d2 s) with
      | none => assertState false s
      | some integer =>
          let value : BitVec 32 := BitVec.ofInt 32 integer
          let checked := assertState (decide (value.toInt = integer)) s
          if width = 64 then updFpReg d1 (value.setWidth 64) checked
          else let (high, low) := if d1 % 2 = 1 then (63, 32) else (31, 0)
            updFpReg (d1 / 2) (holBitFieldInsert high low value (readFpReg (d1 / 2) s)) checked
  | .fpFromInt d1 d2 =>
      let integer := if width = 64 then (holWordExtract 31 0 (readFpReg d2 s) 32).toInt
        else let value := readFpReg (d2 / 2) s
          (if d2 % 2 = 1 then holWordExtract 63 32 value width
            else holWordExtract 31 0 value width).toInt
      updFpReg d1 (holIntToFp64 .roundTiesToEven integer) s

end Flapjack.Compiler.Encoders.AsmSem
