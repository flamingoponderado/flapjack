import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Comparison

/-! Local decomposition of the actual JumpCmp encoder. Branch guards are
original lowering cases, to be discharged by the full constructor proof. -/
namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target

def immediate_prefix (c : Cmp) (r : BitVec 5) (i : BitVec 12) : instruction :=
  match c with
  | .test | .notTest => .ArithI (.ANDI (31,r,i))
  | _ => .ArithI (.ORI (31,0,i))

def immediate_branch (c : Cmp) (r : BitVec 5) (off : BitVec 12) : instruction :=
  match c with
  | .test | .notTest => simple_branch c 31 0 off
  | _ => simple_branch c r 31 off

theorem near_immediate_encoding (c : Cmp) (r : Nat) (i a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) :
    riscvConfig.encode (.jumpCmp c r (.imm i) a) =
      riscvEncode (immediate_prefix c (BitVec.ofNat 5 r) (i.setWidth 12)) ++
      riscvEncode (immediate_branch c (BitVec.ofNat 5 r)
        ((a.sshiftRight 1).setWidth 12 - 2)) := by
  have bounds : (18446744073709547524#64).sle a = true ∧
      a.sle (4095#64) = true := by
    simpa [BitVec.sle_eq_decide, decide_eq_true_eq] using range
  cases c <;> simp [riscvConfig, riscvEnc, riscvAst, inSignedRange,
    bounds, immediate_prefix, immediate_branch, simple_branch]

theorem near_register_test_encoding (c : Cmp) (r s : Nat) (a : BitVec 64)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (test : c = .test ∨ c = .notTest) :
    riscvConfig.encode (.jumpCmp c r (.reg s) a) =
      riscvEncode (.ArithR (.AND (31,BitVec.ofNat 5 r,BitVec.ofNat 5 s))) ++
      riscvEncode (simple_branch c 31 0 ((a.sshiftRight 1).setWidth 12 - 2)) := by
  have bounds : (18446744073709547524#64).sle a = true ∧
      a.sle (4095#64) = true := by
    simpa [BitVec.sle_eq_decide, decide_eq_true_eq] using range
  rcases test with rfl | rfl <;>
    simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds, simple_branch]

def inverse_cmp : Cmp → Cmp
  | .equal => .notEqual
  | .less => .notLess
  | .lower => .notLower
  | .test => .notTest
  | .notEqual => .equal
  | .notLess => .less
  | .notLower => .lower
  | .notTest => .test

theorem inverse_word_cmp (c : Cmp) (left right : BitVec 64) :
    wordCmpHOL (inverse_cmp c) left right = !(wordCmpHOL c left right) := by
  cases c <;> simp [inverse_cmp, wordCmpHOL, bne, Bool.not_not]

theorem inverse_simple (c : Cmp) (simple : c ≠ .test ∧ c ≠ .notTest) :
    inverse_cmp c ≠ .test ∧ inverse_cmp c ≠ .notTest := by
  cases c <;> simp_all [inverse_cmp]

theorem far_immediate_encoding (c : Cmp) (r : Nat) (i a : BitVec 64)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095)) :
    riscvConfig.encode (.jumpCmp c r (.imm i) a) =
      riscvEncode (immediate_prefix c (BitVec.ofNat 5 r) (i.setWidth 12)) ++
      riscvEncode (immediate_branch (inverse_cmp c) (BitVec.ofNat 5 r) 4) ++
      riscvEncode (.Branch (.JAL (0,(a.sshiftRight 1).setWidth 20 - 4))) := by
  have bounds : ¬((18446744073709547524#64).sle a = true ∧
      a.sle (4095#64) = true) := by
    simpa [BitVec.sle_eq_decide, decide_eq_true_eq] using far
  cases c <;> simp [riscvConfig, riscvEnc, riscvAst, inSignedRange,
    bounds, immediate_prefix, immediate_branch, simple_branch, inverse_cmp,
    List.append_assoc]

theorem far_register_simple_encoding (c : Cmp) (r s : Nat) (a : BitVec 64)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest) :
    riscvConfig.encode (.jumpCmp c r (.reg s) a) =
      riscvEncode (simple_branch (inverse_cmp c) (BitVec.ofNat 5 r) (BitVec.ofNat 5 s) 4) ++
      riscvEncode (.Branch (.JAL (0,(a.sshiftRight 1).setWidth 20 - 2))) := by
  have bounds : ¬((18446744073709547524#64).sle a = true ∧
      a.sle (4095#64) = true) := by
    simpa [BitVec.sle_eq_decide, decide_eq_true_eq] using far
  cases c
  case test => exact False.elim (simple.1 rfl)
  case notTest => exact False.elim (simple.2 rfl)
  all_goals simp [riscvConfig, riscvEnc, riscvAst, inSignedRange,
    bounds, simple_branch, inverse_cmp]

theorem far_register_test_encoding (c : Cmp) (r s : Nat) (a : BitVec 64)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest) :
    riscvConfig.encode (.jumpCmp c r (.reg s) a) =
      riscvEncode (.ArithR (.AND (31,BitVec.ofNat 5 r,BitVec.ofNat 5 s))) ++
      riscvEncode (simple_branch (inverse_cmp c) 31 0 4) ++
      riscvEncode (.Branch (.JAL (0,((a.sshiftRight 1).setWidth 20 - 2) - 2))) := by
  have bounds : ¬((18446744073709547524#64).sle a = true ∧
      a.sle (4095#64) = true) := by
    simpa [BitVec.sle_eq_decide, decide_eq_true_eq] using far
  rcases test with rfl | rfl <;>
    simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds,
      simple_branch, inverse_cmp, List.append_assoc]

end Flapjack.RiscV.TargetProof.JumpCmp
