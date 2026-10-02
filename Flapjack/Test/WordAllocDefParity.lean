import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef

namespace Flapjack.Test.WordAllocDefParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-! Kernel replay of `scripts/hol-probes/word_alloc_def_probe.out`: original HOL
`word_alloc` on small 64-bit programs for each allocator branch, an accepted and a
clashing oracle colouring, and stack and physical variables. HOL's `asm_config` is free and
only read through its `ISA` field, so the replay instantiates it with an arbitrary concrete
configuration updated to `isa := .riscv`. Output programs are compared through a structural
observation of their constructors and register numbers. Finite observations do not
establish cross-prover equivalence. -/

private def cfg : AsmConfigExact 64 :=
  { isa := .riscv, encode := fun _ => [], bigEndian := false, codeAlignment := 0,
    linkReg := none, avoidRegs := [], regCount := 0, fpRegCount := 0, twoRegArith := false,
    validImm := fun _ _ => false, addrOffset := (0, 0), hwOffset := (0, 0),
    byteOffset := (0, 0), jumpOffset := (0, 0), cjumpOffset := (0, 0), locOffset := (0, 0) }

abbrev P := WordLangProgHOL (BitVec 64)

/-- Structural observation of the program shapes used below. -/
private def obs : P → Option (List Nat)
  | .seq a b => do
      let x ← obs a
      let y ← obs b
      some (100 :: x ++ y)
  | .move p ls => some (200 :: p :: ls.flatMap fun (x, y) => [x, y])
  | .inst (.arith (.binop .add d s (.reg r))) => some [300, d, s, r]
  | .inst (.arith (.binop .add d s (.imm w))) => some [301, d, s, w.toNat]
  | .inst (.arith (.binop .sub d s (.reg r))) => some [302, d, s, r]
  | .inst (.const r w) => some [400, r, w.toNat]
  | .return l vs => some (500 :: l :: vs)
  | _ => none

private def p1 : P := .seq (.move 0 [(5, 9)]) (.inst (.arith (.binop .add 13 5 (.reg 9))))
private def p2 : P := .seq (.inst (.const 7 3)) (.seq (.inst (.const 5 4))
  (.inst (.arith (.binop .sub 9 5 (.reg 7)))))
private def p3 : P := .seq (.move 1 [(5, 2)]) (.seq (.inst (.arith (.binop .add 2 5 (.imm 1))))
  (.return 0 [2]))

-- wa_type=:num -> α asm_config -> num -> num -> α prog -> num sptree$num_map option -> α prog
example : Nat → AsmConfigExact 64 → Nat → Nat → P → Option (Spt Nat) → P := wordAlloc
-- wa_simple=Seq (Move0 [(0,2)]) (Inst (Arith (Binop Add 0 0 (Reg 2))))
example : obs (wordAlloc 0 cfg 0 3 p1 none) = some [100, 200, 0, 0, 2, 300, 0, 0, 2] := by decide +kernel
-- wa_irc=Seq (Move0 [(0,2)]) (Inst (Arith (Binop Add 0 0 (Reg 2))))
example : obs (wordAlloc 0 cfg 2 3 p1 none) = some [100, 200, 0, 0, 2, 300, 0, 0, 2] := by decide +kernel
-- wa_linear=Seq (Move0 [(2,0)]) (Inst (Arith (Binop Add 0 2 (Reg 0))))
example : obs (wordAlloc 0 cfg 4 3 p1 none) = some [100, 200, 0, 2, 0, 300, 0, 2, 0] := by
  decide +kernel
-- wa_oracle_ok=Seq (Move0 [(2,4)]) (Inst (Arith (Binop Add 6 2 (Reg 4))))
example : obs (wordAlloc 0 cfg 0 3 p1 (some (sptFromAList [(5, 1), (9, 2), (13, 3)]))) =
    some [100, 200, 0, 2, 4, 300, 6, 2, 4] := by decide +kernel
-- wa_oracle_clash=Seq (Move0 [(0,2)]) (Inst (Arith (Binop Add 0 0 (Reg 2))))
example : obs (wordAlloc 0 cfg 0 3 p1 (some (sptFromAList [(5, 1), (9, 1), (13, 3)]))) =
    some [100, 200, 0, 0, 2, 300, 0, 0, 2] := by decide +kernel
-- wa_stack_irc=Seq (Inst (Const 2 3w)) (Seq (Inst (Const 0 4w)) (Inst (Arith (Binop Sub 0 0 (Reg 2)))))
example : obs (wordAlloc 0 cfg 3 1 p2 none) =
    some [100, 400, 2, 3, 100, 400, 0, 4, 302, 0, 0, 2] := by decide +kernel
-- wa_stack_linear=Seq (Inst (Const 2 3w)) (Seq (Inst (Const 0 4w)) (Inst (Arith (Binop Sub 0 0 (Reg 2)))))
example : obs (wordAlloc 0 cfg 5 1 p2 none) =
    some [100, 400, 2, 3, 100, 400, 0, 4, 302, 0, 0, 2] := by decide +kernel
-- wa_phys=Seq (Move1 [(2,2)]) (Seq (Inst (Arith (Binop Add 2 2 (Imm 1w)))) (Return 0 [2]))
example : obs (wordAlloc 0 cfg 2 3 p3 none) =
    some [100, 200, 1, 2, 2, 100, 301, 2, 2, 1, 500, 0, 2] := by decide +kernel

end Flapjack.Test.WordAllocDefParity
