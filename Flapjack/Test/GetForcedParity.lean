import Flapjack.Compiler.Backend.WordAlloc.Proofs.GetForced
namespace Flapjack.Test.GetForcedParity
open Flapjack Flapjack.WordAlloc Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-! Kernel replay of `scripts/hol-probes/word_alloc_get_forced_probe.out`: original
HOL `get_forced` rows. HOL's free `c with ISA := _` is an arbitrary
`AsmConfigExact` updated at `isa`. -/

abbrev P := WordLangProgHOL (BitVec 64)
abbrev P32 := WordLangProgHOL (BitVec 32)
private def acc : List (Nat × Nat) := [(9, 8)]
private def o1 : P := .inst (.arith (.addOverflow 1 2 3 4))
private def o2 : P := .inst (.arith (.addOverflow 5 6 7 8))

-- gf_addcarry_riscv=[(1,3); (1,4); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.addCarry 1 2 3 4)) : P) acc = [(1,3), (1,4), (9,8)] := by
  simp [getForced, acc]
-- gf_addcarry_mips=[(1,3); (1,4); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .mips } (.inst (.arith (.addCarry 1 2 3 4)) : P) acc = [(1,3), (1,4), (9,8)] := by
  simp [getForced, acc]
-- gf_addcarry_self=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.addCarry 1 2 1 1)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_addcarry_x86=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .x86_64 } (.inst (.arith (.addCarry 1 2 3 4)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_addovf_riscv=[(1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.addOverflow 1 2 3 4)) : P) acc = [(1,3), (9,8)] := by
  simp [getForced, acc]
-- gf_addovf_armv8=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .armv8 } (.inst (.arith (.addOverflow 1 2 3 4)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_subovf_mips=[(1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .mips } (.inst (.arith (.subOverflow 1 2 3 4)) : P) acc = [(1,3), (9,8)] := by
  simp [getForced, acc]
-- gf_subovf_self=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.subOverflow 3 2 3 4)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_longmul_armv7=[(1,2); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .armv7 } (.inst (.arith (.longMul 1 2 3 4)) : P) acc = [(1,2), (9,8)] := by
  simp [getForced, acc]
-- gf_longmul_armv7_self=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .armv7 } (.inst (.arith (.longMul 1 1 3 4)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_longmul_riscv=[(1,3); (1,4); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.longMul 1 2 3 4)) : P) acc = [(1,3), (1,4), (9,8)] := by
  simp [getForced, acc]
-- gf_longmul_ag32=[(1,4); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .ag32 } (.inst (.arith (.longMul 1 2 1 4)) : P) acc = [(1,4), (9,8)] := by
  simp [getForced, acc]
-- gf_longmul_x86=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .x86_64 } (.inst (.arith (.longMul 1 2 3 4)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_fptoreg_32=[(1,2); (9,8)]
example (c : AsmConfigExact 32) : getForced { c with isa := .riscv } (.inst (.fp (.fpMovToReg 1 2 0)) : P32) acc = [(1,2), (9,8)] := by
  simp [getForced, acc]
-- gf_fptoreg_32_self=[(9,8)]
example (c : AsmConfigExact 32) : getForced { c with isa := .riscv } (.inst (.fp (.fpMovToReg 1 1 0)) : P32) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_fptoreg_64=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.fp (.fpMovToReg 1 2 0)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_fpfromreg_32=[(1,2); (9,8)]
example (c : AsmConfigExact 32) : getForced { c with isa := .x86_64 } (.inst (.fp (.fpMovFromReg 0 1 2)) : P32) acc = [(1,2), (9,8)] := by
  simp [getForced, acc]
-- gf_fpfromreg_64=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.fp (.fpMovFromReg 0 1 2)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_other_inst=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.div 1 2 3)) : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_seq=[(1,3); (5,7); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.seq o1 o2 : P) acc = [(1,3), (5,7), (9,8)] := by
  simp [getForced, acc, o1, o2]
-- gf_if=[(1,3); (5,7); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.ite .equal 0 (.imm 0) o1 o2 : P) acc = [(1,3), (5,7), (9,8)] := by
  simp [getForced, acc, o1, o2]
-- gf_must=[(1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.mustTerminate o1 : P) acc = [(1,3), (9,8)] := by
  simp [getForced, acc, o1]
-- gf_loop=[(1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.loop .ln o1 .ln : P) acc = [(1,3), (9,8)] := by
  simp [getForced, acc, o1]
-- gf_call_return=[(1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.call (some ([1], (.ln, .ln), o1, 17, 19)) none [] none : P) acc = [(1,3), (9,8)] := by
  simp [getForced, acc, o1]
-- gf_call_both=[(5,7); (1,3); (9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.call (some ([1], (.ln, .ln), o1, 17, 19)) none [] (some (1, o2, 11, 13)) : P) acc = [(5,7), (1,3), (9,8)] := by
  simp [getForced, acc, o1, o2]
-- gf_call_tail=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.call none none [] (some (1, o2, 11, 13)) : P) acc = [(9,8)] := by
  simp [getForced, acc, o2]
-- gf_skip=[(9,8)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.skip : P) acc = [(9,8)] := by
  simp [getForced, acc]
-- gf_large=[(36893488147419103232,36893488147419103233)]
example (c : AsmConfigExact 64) : getForced { c with isa := .riscv } (.inst (.arith (.addOverflow 36893488147419103232 0 36893488147419103233 0)) : P) [] = [(36893488147419103232,36893488147419103233)] := by
  simp [getForced]

/-- `get_forced_in_get_clash_tree` instantiated at the probe's returning call with a handler. -/
example (c : AsmConfigExact 64) (lt : List (NumSet × NumSet)) :
    ∀ x ∈ getForced { c with isa := .riscv } (.call (some ([1], (.ln, .ln), o1, 17, 19)) none []
      (some (1, o2, 11, 13)) : P) [],
      inClashTree (getClashTree (.call (some ([1], (.ln, .ln), o1, 17, 19)) none [] (some (1, o2, 11, 13)) : P) lt) x.1 ∧
      inClashTree (getClashTree (.call (some ([1], (.ln, .ln), o1, 17, 19)) none [] (some (1, o2, 11, 13)) : P) lt) x.2 :=
  getForcedInGetClashTree _ lt _

/-- `get_forced_tail_split` at the probe's `gf_call_both` row: the `[(9,8)]`
accumulator splits off the `[]`-accumulator result. -/
example (c : AsmConfigExact 64) :
    getForced { c with isa := .riscv } (.call (some ([1], (.ln, .ln), o1, 17, 19)) none []
      (some (1, o2, 11, 13)) : P) ([] ++ acc) =
    getForced { c with isa := .riscv } (.call (some ([1], (.ln, .ln), o1, 17, 19)) none []
      (some (1, o2, 11, 13)) : P) [] ++ acc :=
  getForcedTailSplit _ _ [] acc

/-- `EVERY_get_forced` at the `gf_seq` row with HOL's paired distinctness predicate. -/
example (c : AsmConfigExact 64) :
    (∀ x ∈ getForced { c with isa := .riscv } (.seq o1 o2 : P) acc, x.1 ≠ x.2) ↔
      (∀ x ∈ getForced { c with isa := .riscv } (.seq o1 o2 : P) [], x.1 ≠ x.2) ∧
        ∀ x ∈ acc, x.1 ≠ x.2 :=
  everyGetForced (fun x => x.1 ≠ x.2) _ _ acc

/-- `get_forced_pairwise_distinct` at the `gf_large` row's program, whose
starting accumulator `acc = [(9,8)]` is pairwise distinct. -/
example (c : AsmConfigExact 64) :
    ∀ x ∈ getForced { c with isa := .riscv }
      (.inst (.arith (.addOverflow 36893488147419103232 0 36893488147419103233 0)) : P) acc,
      x.1 ≠ x.2 :=
  getForcedPairwiseDistinct _ _ acc (by simp [acc])

end Flapjack.Test.GetForcedParity
