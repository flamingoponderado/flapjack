import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.Compiler.Encoders.RiscV.Target.State
import Flapjack.Compiler.Encoders.AsmProps.Encoding
import Flapjack.Compiler.Encoders.AsmSem.Arithmetic

/-! Full native target validity. Local range arithmetic establishes the original
positive and negative offset-length implications without assuming a target run. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Flapjack target-register guard infrastructure: a register accepted by
`asmRegOkExact` is not the zero register. Shared by the register-operand
encoder cases; no separately named HOL original. -/
theorem reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 0#5 := by
  have g : r < 32 ∧ r ≠ 0 := by
    have g := guard
    simp [asmRegOkExact, riscvConfig] at g
    exact ⟨of_decide_eq_true g.1, g.2.1⟩
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  rw [show 2 ^ 5 = 32 by decide, Nat.zero_mod] at n
  rw [Nat.mod_eq_of_lt g.1] at n
  exact g.2 n

/-- Flapjack target-register guard infrastructure: the register guard yields
the width bound, non-zeroness and the excluded scratch register. Shared by the
overflow encoders; no separately named HOL original. -/
theorem guard (r : Nat) (g : asmRegOkExact r riscvConfig = true) :
    r < 32 ∧ BitVec.ofNat 5 r ≠ 0#5 ∧ BitVec.ofNat 5 r ≠ 31#5 := by
  have facts : r < 32 ∧ r ≠ 0 ∧ r ≠ 31 := by
    simp [asmRegOkExact, riscvConfig] at g
    exact ⟨of_decide_eq_true g.1, g.2.1, g.2.2.2.2.2⟩
  refine ⟨facts.1, ?_, ?_⟩
  · intro eq
    have n := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at n
    rw [show 2 ^ 5 = 32 by decide, Nat.zero_mod] at n
    rw [Nat.mod_eq_of_lt facts.1] at n
    exact facts.2.1 n
  · intro eq
    have n := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at n
    rw [show 2 ^ 5 = 32 by decide, show 31 % 32 = 31 by decide] at n
    rw [Nat.mod_eq_of_lt facts.1] at n
    exact facts.2.2 n

/-- Flapjack target-register infrastructure: a guarded register reads the same
value in the native state and the assembly state. Shared by the register-operand
encoder cases; no separately named HOL original. -/
theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR, gpr, reg_nonzero r guard, readReg] using before

/-- Flapjack signed-interval infrastructure: the nearer-to-zero word remains
in a signed interval containing zero, for both original monotonic directions. -/
private theorem range_near (lo hi a1 a2 : BitVec 64)
    (hlo : lo.toInt ≤ 0) (hhi : 0 ≤ hi.toInt) :
    ((0 : BitVec 64).sle a1 = true ∧ (0 : BitVec 64).sle a2 = true ∧ a1.sle a2 = true →
      inSignedRange lo hi a2 = true → inSignedRange lo hi a1 = true) ∧
    (a1.slt 0 = true ∧ a2.slt 0 = true ∧ a2.sle a1 = true →
      inSignedRange lo hi a2 = true → inSignedRange lo hi a1 = true) := by
  simp only [inSignedRange, Bool.and_eq_true, BitVec.sle_eq_decide,
    BitVec.slt_eq_decide, decide_eq_true_eq]
  change (0 ≤ a1.toInt ∧ 0 ≤ a2.toInt ∧ a1.toInt ≤ a2.toInt →
    lo.toInt ≤ a2.toInt ∧ a2.toInt ≤ hi.toInt → lo.toInt ≤ a1.toInt ∧ a1.toInt ≤ hi.toInt) ∧
    (a1.toInt < 0 ∧ a2.toInt < 0 ∧ a2.toInt ≤ a1.toInt →
    lo.toInt ≤ a2.toInt ∧ a2.toInt ≤ hi.toInt → lo.toInt ≤ a1.toInt ∧ a1.toInt ≤ hi.toInt)
  omega

/-- Flapjack complete native jump offset-length obligation. -/
private theorem jump_monotonic (a1 a2 : BitVec 64) :
    offsetMonotonic riscvEnc riscvConfig a1 a2 (.jump a1) (.jump a2) := by
  intro _
  constructor <;> intro h
  all_goals
    have near := range_near (-1048576) 1048575 a1 a2 (by decide) (by decide)
    have hn : inSignedRange (-1048576) 1048575 a2 = true →
      inSignedRange (-1048576) 1048575 a1 = true := by
        first | exact near.1 h | exact near.2 h
    rw [riscvEnc_length_eq, riscvEnc_length_eq]
    by_cases h1 : inSignedRange (-1048576) 1048575 a1 = true <;>
      by_cases h2 : inSignedRange (-1048576) 1048575 a2 = true <;>
      simp_all [riscvAst]

/-- Flapjack complete native call offset-length obligation. -/
private theorem call_monotonic (a1 a2 : BitVec 64) :
    offsetMonotonic riscvEnc riscvConfig a1 a2 (.call a1) (.call a2) := by
  intro _
  constructor <;> intro h
  all_goals
    have near := range_near (-1048576) 1048575 a1 a2 (by decide) (by decide)
    have hn : inSignedRange (-1048576) 1048575 a2 = true →
      inSignedRange (-1048576) 1048575 a1 = true := by
        first | exact near.1 h | exact near.2 h
    rw [riscvEnc_length_eq, riscvEnc_length_eq]
    by_cases h1 : inSignedRange (-1048576) 1048575 a1 = true <;>
      by_cases h2 : inSignedRange (-1048576) 1048575 a2 = true <;>
      simp_all [riscvAst]

/-- Flapjack full conditional offset obligation over every cmp/reg-or-imm. -/
private theorem jumpCmp_monotonic (cmp : Cmp) (reg : Nat) (ri : HolRegImm 64)
    (a1 a2 : BitVec 64) :
    offsetMonotonic riscvEnc riscvConfig a1 a2 (.jumpCmp cmp reg ri a1) (.jumpCmp cmp reg ri a2) := by
  intro _
  constructor <;> intro h
  all_goals
    have near := range_near (-4092) 4095 a1 a2 (by decide) (by decide)
    have hn : inSignedRange (-4092) 4095 a2 = true → inSignedRange (-4092) 4095 a1 = true := by
      first | exact near.1 h | exact near.2 h
    rw [riscvEnc_length_eq, riscvEnc_length_eq]
    cases ri <;> cases cmp <;>
      by_cases h1 : inSignedRange (-4092) 4095 a1 = true <;>
      by_cases h2 : inSignedRange (-4092) 4095 a2 = true <;>
      simp_all [riscvAst]

/-- Flapjack native locations always have the same two-instruction length. -/
private theorem loc_monotonic (a1 a2 : BitVec 64) (reg : Nat) :
    offsetMonotonic riscvEnc riscvConfig a1 a2 (.loc reg a1) (.loc reg a2) := by
  intro _
  constructor <;> intro _ <;>
    rw [riscvEnc_length_eq, riscvEnc_length_eq] <;> simp [riscvAst]

/-- Full native encoding validity conjunct, without extra assumptions. This
is infrastructure for the assembling original target_ok theorem. -/
theorem riscv_enc_ok : encOk riscvConfig := by
  refine ⟨?_, ?_, jump_monotonic, jumpCmp_monotonic, call_monotonic, loc_monotonic⟩
  · rfl
  · intro i
    have h := riscv_encoding i
    refine ⟨h.1, ?_⟩
    change (riscvEnc i).length ≠ 0
    intro hz
    have he : riscvEnc i = [] := by
      cases he : riscvEnc i with
      | nil => rfl
      | cons a xs => simp [he] at hz
    exact h.2 he


/-- Full native projection consistency infrastructure. Floating register
observations are vacuous because the original configuration has count zero. -/
theorem riscv_projection_ok (ms1 ms2 : riscv_state) (s : AsmState 64)
    (hp : riscvProj s.memDomain ms1 = riscvProj s.memDomain ms2) :
    (targetStateRel riscvTarget s ms1 ↔ targetStateRel riscvTarget s ms2) ∧
    riscvOk ms1 = riscvOk ms2 ∧
    ms1.c_PC ms1.procID = ms2.c_PC ms2.procID ∧
    (∀ a, s.memDomain a → ms1.MEM8 a = ms2.MEM8 a) := by
  have hvm := congrArg (fun p : RiscVProjection => p.1) hp
  have ha := congrArg (fun p : RiscVProjection => p.2.1) hp
  have hn := congrArg (fun p : RiscVProjection => p.2.2.1) hp
  have he := congrArg (fun p : RiscVProjection => p.2.2.2.1) hp
  have hr := congrArg (fun p : RiscVProjection => p.2.2.2.2.1) hp
  have hm := congrArg (fun p : RiscVProjection => p.2.2.2.2.2.1) hp
  have hc := congrArg (fun p : RiscVProjection => p.2.2.2.2.2.2) hp
  simp only [riscvProj] at hvm ha hn he hr hm hc
  have hok : riscvOk ms1 = riscvOk ms2 := by
    simp only [riscvOk, hvm, ha, hn, he, hc]
  have hmem : ∀ a, s.memDomain a → ms1.MEM8 a = ms2.MEM8 a := by
    intro a hd
    have hgraph : SetSep.fun2Set (ms1.MEM8, s.memDomain) (a, ms1.MEM8 a) :=
      (SetSep.fun2SetThm _ _ _ _).mpr ⟨rfl, hd⟩
    rw [hm] at hgraph
    exact ((SetSep.fun2SetThm _ _ _ _).mp hgraph).1.symm
  refine ⟨?_, hok, hc, hmem⟩
  simp only [targetStateRel, riscvTarget, riscvConfig]
  simp only [hok, hc, hr]
  constructor
  · rintro ⟨h1, h2, h3, h4, _⟩
    refine ⟨h1, h2, ?_, h4, fun i hi => by omega⟩
    intro a hd
    rw [← hmem a hd]
    exact h3 a hd
  · rintro ⟨h1, h2, h3, h4, _⟩
    refine ⟨h1, h2, ?_, h4, fun i hi => by omega⟩
    intro a hd
    rw [hmem a hd]
    exact h3 a hd

/-- Full original native target validity, retaining all encoder and
projection obligations without a target execution assumption. -/
@[hol "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml" "riscv_target_ok"]
theorem riscv_target_ok : targetOk riscvTarget := by
  refine ⟨riscv_enc_ok, ?_⟩
  intro ms1 ms2 s hp
  exact riscv_projection_ok ms1 ms2 s hp

end Flapjack.RiscV.TargetProof
