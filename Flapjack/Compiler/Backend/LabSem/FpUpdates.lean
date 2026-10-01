import Flapjack.Compiler.Backend.LabSem.Updates
import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

namespace Flapjack.Compiler.Backend.LabSem

open Flapjack.Compiler.Encoders.Asm

/-- Literal sixteen clauses of HOL `fp_upd_def` (158-223) on the actual native
state. Binary64 primitives are the imported reviewed IEEE renderings, including
the source `fpSem$fpfma` operand order. Their real-number translation has the
same assurance boundary as the WordSem evaluator (SOUNDNESS item 8).

FPToInt asserts the signed-word32 range check but still writes the narrowed
bits on failure. Its non64 branch reads the old FP register for insertion.
FPFromInt's non64 extracted half has the actual word width before signed
interpretation; no assumption that this width equals32 is made. Register
updates are sequential, including when the two destinations alias. -/
@[hol "cakeml/compiler/backend/semantics/labSemScript.sml" "fp_upd_def"
  (words_as_type_indexed_bitvec) (reals_as_rational_cuts)]
noncomputable def fpUpd {width : Nat} [NeZero width] {C F : Type}
    (operation : HolFp) (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Flapjack.Compiler.Backend.LabSem.State width C F :=
  match operation with
  | .fpLess r d1 d2 => updReg r (.word (if holFp64LessThan (readFpReg d1 state)
      (readFpReg d2 state) then 1 else 0)) state
  | .fpLessEqual r d1 d2 => updReg r (.word (if holFp64LessEqual (readFpReg d1 state)
      (readFpReg d2 state) then 1 else 0)) state
  | .fpEqual r d1 d2 => updReg r (.word (if holFp64Equal (readFpReg d1 state)
      (readFpReg d2 state) then 1 else 0)) state
  | .fpMov d1 d2 => updFpReg d1 (readFpReg d2 state) state
  | .fpAbs d1 d2 => updFpReg d1 (holFp64Abs (readFpReg d2 state)) state
  | .fpNeg d1 d2 => updFpReg d1 (holFp64Negate (readFpReg d2 state)) state
  | .fpSqrt d1 d2 => updFpReg d1 (holFp64Sqrt .roundTiesToEven (readFpReg d2 state)) state
  | .fpAdd d1 d2 d3 => updFpReg d1 (holFp64Add .roundTiesToEven
      (readFpReg d2 state) (readFpReg d3 state)) state
  | .fpSub d1 d2 d3 => updFpReg d1 (holFp64Sub .roundTiesToEven
      (readFpReg d2 state) (readFpReg d3 state)) state
  | .fpMul d1 d2 d3 => updFpReg d1 (holFp64Mul .roundTiesToEven
      (readFpReg d2 state) (readFpReg d3 state)) state
  | .fpDiv d1 d2 d3 => updFpReg d1 (holFp64Div .roundTiesToEven
      (readFpReg d2 state) (readFpReg d3 state)) state
  | .fpFma d1 d2 d3 => updFpReg d1 (fpSemFpfma
      (readFpReg d1 state) (readFpReg d2 state) (readFpReg d3 state)) state
  | .fpMovToReg r1 r2 d =>
      if width = 64 then updReg r1 (.word ((readFpReg d state).setWidth width)) state
      else let value := readFpReg d state
        updReg r2 (.word (holWordExtract 63 32 value width))
          (updReg r1 (.word (holWordExtract 31 0 value width)) state)
  | .fpMovFromReg d r1 r2 =>
      if width = 64 then
        match state.regs r1 with
        | .word value => updFpReg d (value.setWidth 64) state
        | _ => assertState false state
      else
        match state.regs r1, state.regs r2 with
        | .word low, .word high => updFpReg d ((high ++ low).setWidth 64) state
        | _, _ => assertState false state
  | .fpToInt d1 d2 =>
      match holFp64ToInt .roundTiesToEven (readFpReg d2 state) with
      | none => assertState false state
      | some integer =>
          let value : BitVec 32 := BitVec.ofInt 32 integer
          let checked := assertState (decide (value.toInt = integer)) state
          if width = 64 then updFpReg d1 (value.setWidth 64) checked
          else let (high, low) := if d1 % 2 = 1 then (63, 32) else (31, 0)
            updFpReg (d1 / 2) (holBitFieldInsert high low value (readFpReg (d1 / 2) state)) checked
  | .fpFromInt d1 d2 =>
      let integer := if width = 64 then (holWordExtract 31 0 (readFpReg d2 state) 32).toInt
        else let value := readFpReg (d2 / 2) state
          (if d2 % 2 = 1 then holWordExtract 63 32 value width
            else holWordExtract 31 0 value width).toInt
      updFpReg d1 (holIntToFp64 .roundTiesToEven integer) state

end Flapjack.Compiler.Backend.LabSem
