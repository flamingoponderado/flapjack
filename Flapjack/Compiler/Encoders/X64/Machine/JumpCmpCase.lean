module

public import Flapjack.Compiler.Encoders.X64.Machine.FpCase

-- Sum `==` must reduce by `rfl`/`decide`; core's derived instance is not exposed.
import all Init.Data.Sum.Basic
@[expose] public section

/-!
# The `jumpCmp` cases of `encoder_correct x64Target`

`jumpCmp` lowers to a flag-setting comparison followed by a conditional jump:
`cmp r, s` (or `test r, s`) writes `cf`/`zf`/`sf`/`of` exactly as the source's
`word_cmp`, and the `jcc` branches to `pc + target` when the condition code
holds.  The offset subtracts the two instructions' length, so the taken branch
lands where `asmUpd`'s `jump_to_offset` puts it; the untaken branch advances by
the instruction length like `asmUpd`'s `upd_pc`.

The comparison's flag semantics are the source's `word_cmp`: `subFlags` gives
`cf`/`zf`/`sf`/`of` for the subtraction and `logicFlags` gives `zf` for the
`and`.  The register form is nine bytes (`cmp`/`test` plus a long `jcc`); the
immediate form is ten, twelve, or thirteen bytes depending on whether the
immediate fits in one byte and whether the register is `rax`.
-/

namespace Flapjack.Compiler.Encoders.X64
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

theorem toInt_bounds (a : BitVec 64) : -(2^63 : Int) ≤ a.toInt ∧ a.toInt < 2^63 := by
  constructor
  · rw [BitVec.toInt_eq_toNat_bmod]
    have h := Int.le_bmod (x := (a.toNat : Int)) (m := 2^64) (by decide)
    simpa using h
  · have h := BitVec.toInt_lt (x := a)
    simpa using h

theorem subFlags_msb (a b : BitVec 64) :
    (a - b).msb = decide ((a - b).toInt < 0) := by
  rw [BitVec.msb_eq_decide, BitVec.toInt_eq_toNat_cond]
  have ha := (a - b).isLt
  split <;> simp_all <;> omega

theorem decide_ne_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p ≠ decide q) ↔ (p ↔ ¬q) := by
  cases hp : decide p <;> cases hq : decide q <;> simp_all

theorem beq_eq_decide {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  cases h : (a == b) <;> simp_all

theorem subFlags_slt (a b : BitVec 64) :
    ((subFlags a b).sf != (subFlags a b).of) = decide (a.toInt < b.toInt) := by
  have hbne : ((subFlags a b).sf != (subFlags a b).of) =
      decide ((subFlags a b).sf ≠ (subFlags a b).of) := by
    cases (subFlags a b).sf <;> cases (subFlags a b).of <;> rfl
  rw [hbne, decide_eq_decide]
  have ha := toInt_bounds a
  have hb := toInt_bounds b
  have hmsb := subFlags_msb a b
  have hhalf : ((2^64 : Int) + 1) / 2 = 2^63 := by decide
  simp only [subFlags, hmsb, BitVec.toInt_sub, Int.bmod_def]
  split_ifs with hlt <;> rw [decide_ne_decide] <;> omega

theorem holAsmSignedLess_eq (a b : BitVec 64) : holAsmSignedLess a b = a.slt b := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> simp <;> omega

theorem subFlags_zf (a b : BitVec 64) : (subFlags a b).zf = (a == b) := by
  simp only [subFlags, _root_.beq_eq_decide]
  have h : (a - b = 0) ↔ (a = b) := by
    rw [BitVec.sub_eq_iff_eq_add]
    simp
  exact decide_eq_decide.mpr h

theorem subFlags_cf (a b : BitVec 64) : (subFlags a b).cf = decide (a < b) := by
  simp only [subFlags, BitVec.lt_def]

theorem subFlags_nl (a b : BitVec 64) :
    decide ((subFlags a b).sf = (subFlags a b).of) = !(a.slt b) := by
  have h := subFlags_slt a b
  have h2 : decide ((subFlags a b).sf = (subFlags a b).of) =
      !((subFlags a b).sf != (subFlags a b).of) := by
    cases (subFlags a b).sf <;> cases (subFlags a b).of <;> rfl
  rw [h2, h, BitVec.slt_eq_decide]

theorem logicFlags_zf (a b : BitVec 64) : (logicFlags (a &&& b)).zf = (a &&& b == 0) := by
  simp only [logicFlags]
  rw [beq_eq_decide, decide_eq_decide]

theorem evalCond_zL_subFlags (a b : BitVec 64) :
    evalCond .zL (subFlags a b) = a.slt b := by
  have h := subFlags_slt a b
  have h2 : decide ((subFlags a b).sf ≠ (subFlags a b).of) =
      ((subFlags a b).sf != (subFlags a b).of) := by
    cases (subFlags a b).sf <;> cases (subFlags a b).of <;> rfl
  simp only [evalCond, h2, h, BitVec.slt_eq_decide]

theorem evalCond_zE_subFlags (a b : BitVec 64) :
    evalCond .zE (subFlags a b) = (a == b) := by
  simp only [evalCond, subFlags_zf]

theorem evalCond_zB_subFlags (a b : BitVec 64) :
    evalCond .zB (subFlags a b) = decide (a < b) := by
  simp only [evalCond, subFlags_cf]

theorem evalCond_zNE_subFlags (a b : BitVec 64) :
    evalCond .zNE (subFlags a b) = !(a == b) := by
  simp only [evalCond, subFlags_zf]

theorem evalCond_zNB_subFlags (a b : BitVec 64) :
    evalCond .zNB (subFlags a b) = !decide (a < b) := by
  simp only [evalCond, subFlags_cf]

theorem evalCond_zNL_subFlags (a b : BitVec 64) :
    evalCond .zNL (subFlags a b) = !(a.slt b) := by
  simp only [evalCond, subFlags_nl]

theorem evalCond_zE_logicFlags (a b : BitVec 64) :
    evalCond .zE (logicFlags (a &&& b)) = (a &&& b == 0) := by
  simp only [evalCond, logicFlags_zf]

theorem evalCond_zNE_logicFlags (a b : BitVec 64) :
    evalCond .zNE (logicFlags (a &&& b)) = !(a &&& b == 0) := by
  simp only [evalCond, logicFlags_zf]

theorem evalCond_x64Cmp (operator : Cmp) (hnt : isTest operator = false) (a b : BitVec 64) :
    evalCond (x64Cmp operator) (subFlags a b) = wordCmpHOL operator a b := by
  cases operator
  case equal => simpa [x64Cmp, wordCmpHOL] using evalCond_zE_subFlags a b
  case less => simpa [x64Cmp, wordCmpHOL, holAsmSignedLess_eq] using evalCond_zL_subFlags a b
  case lower => simpa [x64Cmp, wordCmpHOL] using evalCond_zB_subFlags a b
  case test => simp [isTest] at hnt
  case notEqual => simpa [x64Cmp, wordCmpHOL] using evalCond_zNE_subFlags a b
  case notLess => simpa [x64Cmp, wordCmpHOL, holAsmSignedLess_eq] using evalCond_zNL_subFlags a b
  case notLower => simpa [x64Cmp, wordCmpHOL] using evalCond_zNB_subFlags a b
  case notTest => simp [isTest] at hnt

theorem evalCond_x64Cmp_test (operator : Cmp) (ht : isTest operator = true) (a b : BitVec 64) :
    evalCond (x64Cmp operator) (logicFlags (a &&& b)) = wordCmpHOL operator a b := by
  cases operator <;> simp_all [isTest, x64Cmp, wordCmpHOL, AndOp.and, bne,
    evalCond_zE_logicFlags, evalCond_zNE_logicFlags]

/-! ## The comparison and branch steps -/

/-- The decoder recovers a `cmp`/`test` of two registers. -/
theorem decode_binopCmp (zop : ZBinopName) (dst src : Nat) (hd : dst < 16) (hs : src < 16)
    (hz : zop = .zcmp ∨ zop = .ztest) :
    decode (byteListReader (encodeInsn (.binopRR zop .z64 dst src))) =
      some (.binopRR zop .z64 dst src, (encodeInsn (.binopRR zop .z64 dst src)).length) := by
  rcases hz with rfl | rfl
  · exact decode_binopRR_z64 .zcmp dst src hd hs (by decide)
  · exact decode_binopRR_test dst src hd hs

theorem x64Next_binopCmp (ms : X64State) (d : BitVec 64 → Prop) (zop : ZBinopName)
    (dst src : Nat) (hd : dst < 16) (hs : src < 16)
    (hz : zop = .zcmp ∨ zop = .ztest)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR zop .z64 dst src)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with
      flags := binopFlags zop (readReg ms dst) (readReg ms src) ms.flags,
      pc := ms.pc + BitVec.ofNat 64 3 } := by
  have hlen : (encodeInsn (.binopRR zop .z64 dst src)).length = 3 := by
    refine encodeInsn_binopRR_length zop dst src ?_
    intro hne hc
    rcases hz with rfl | rfl
    · simp [ZBinopName.code] at hc
    · exact absurd rfl hne
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR zop .z64 dst src, 3) := by
    have hd' := decode_binopCmp zop dst src hd hs hz
    rw [hlen] at hd'
    exact decode_bytesInMemory _ _ ms.mem d _ _ hbm hd' (by omega)
  rcases hz with rfl | rfl
  · simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, binopFlags]
  · simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, binopFlags]

theorem x64Next_jcc_long (ms : X64State) (d : BitVec 64 → Prop) (cond : ZCond) (imm : BitVec 64)
    (hne : cond ≠ .zAlways) (hneP : cond ≠ .zP)
    (hlo : -(2^31 : Int) ≤ imm.toInt) (hhi : imm.toInt < 2^31)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.jcc cond imm)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = if evalCond cond ms.flags then
      { ms with pc := ms.pc + BitVec.ofNat 64 6 + imm } else
      { ms with pc := ms.pc + BitVec.ofNat 64 6 } := by
  have hlen : (encodeInsn (.jcc cond imm)).length = 6 :=
    encodeInsn_jcc_long cond imm hneP hne hlo hhi
  have hdec := decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm
    (decode_jcc_long_other cond hne hneP imm hlo hhi) (by rw [hlen])
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn]


/-! ## The register form -/

/-- The `jumpCmp` register constructor of `encoder_correct x64Target`: `cmp`
writes the subtraction flags and the branch follows the condition code. -/
theorem case_jumpCmp_reg (operator : Cmp) (source right : Nat) (target : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.jumpCmp operator source (.reg right) target) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.jumpCmp operator source (.reg right) target) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.jumpCmp operator source (.reg right) target) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  have hlen : (x64Target.config.encode (.jumpCmp operator source (.reg right) target)).length = 9 :=
    x64Enc_jumpCmp_reg_length operator source right target hok
  simp only [asmOkExact, Bool.and_eq_true] at hok
  obtain ⟨hco, hcmpok⟩ := hok
  simp only [asmCmpOkExact, asmRegImmOkExact, Bool.and_eq_true] at hcmpok
  obtain ⟨hsrck, hrgtk⟩ := hcmpok
  have hsrc : source < 16 ∧ x64Target.config.avoidRegs.contains source = false := by
    simpa [asmRegOkExact, x64Config] using hsrck
  have hrgt : right < 16 ∧ x64Target.config.avoidRegs.contains right = false := by
    simpa [asmRegOkExact, x64Config] using hrgtk
  have hsrc' : totalNum2Zreg source = source := totalNum2Zreg_eq source hsrc.1
  have hrgt' : totalNum2Zreg right = right := totalNum2Zreg_eq right hrgt.1
  have htn1 : totalNum2Zreg source < 16 := by rw [hsrc']; exact hsrc.1
  have htn2 : totalNum2Zreg right < 16 := by rw [hrgt']; exact hrgt.1
  obtain ⟨hlo, hhi⟩ := cjump_offset_range target hco
  have hr9 := cjump_offset_sub_nine target hlo hhi
  have hupd : asmUpd (.jumpCmp operator source (.reg right) target)
      (s1.pc + BitVec.ofNat 64 9) s1 = s2 := by
    rw [← st.upd, hlen]
  have hbrlen : (encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
      (totalNum2Zreg source) (totalNum2Zreg right))).length = 3 := by
    apply encodeInsn_binopRR_length
    intro hne hc
    by_cases ht : isTest operator = true
    · simp only [ht, if_true] at hne
      exact absurd rfl hne
    · simp only [Bool.not_eq_true] at ht
      simp [ht] at hc
      simp [ZBinopName.code] at hc
  have hjcc : (encodeInsn (.jcc (x64Cmp operator) (target - 9))).length = 6 :=
    encodeInsn_jcc_long (x64Cmp operator) (target - 9)
      (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator) hr9.1 hr9.2
  have henc : x64Target.config.encode (.jumpCmp operator source (.reg right) target) =
      encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) (totalNum2Zreg right)) ++
      encodeInsn (.jcc (x64Cmp operator) (target - 9)) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp [x64Ast]
    · intro h'
      have := congrArg List.length h'
      rw [List.length_append, hbrlen, hjcc] at this
      simp at this
  have hbmAll : bytesInMemoryHOL ms.pc
      (encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) (totalNum2Zreg right)) ++
       encodeInsn (.jcc (x64Cmp operator) (target - 9))) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb0, hb1⟩ := (bytesInMemory_append _ _ ms.pc ms.mem s1.memDomain).1 hbmAll
  rw [hbrlen] at hb1
  have hzop : ((if isTest operator then ZBinopName.ztest else ZBinopName.zcmp) : ZBinopName) =
      ZBinopName.zcmp ∨
      ((if isTest operator then ZBinopName.ztest else ZBinopName.zcmp) : ZBinopName) =
        ZBinopName.ztest := by
    by_cases ht : isTest operator = true <;> simp [ht]
  have hdec0 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) (totalNum2Zreg right), 3) := by
    have hd := decode_binopCmp _ _ _ htn1 htn2 hzop
    rw [hbrlen] at hd
    exact decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb0 hd (by omega)
  have hdec1 : decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64 3) + BitVec.ofNat 64 k)) =
      some (.jcc (x64Cmp operator) (target - 9), 6) := by
    have hd := decode_jcc_long_other (x64Cmp operator)
      (x64Cmp_ne_zAlways operator) (x64Cmp_ne_zP operator) (target - 9) hr9.1 hr9.2
    exact decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb1 hd (by rw [hjcc])
  set ms1 : X64State := { ms with
      flags := binopFlags (if isTest operator then .ztest else .zcmp)
        (readReg ms (totalNum2Zreg source)) (readReg ms (totalNum2Zreg right)) ms.flags,
      pc := ms.pc + BitVec.ofNat 64 3 } with hms1
  have hms1pc : ms1.pc = ms.pc + BitVec.ofNat 64 3 := by simp only [hms1]
  have hms1mem : ms1.mem = ms.mem := by simp only [hms1]
  have hms1regs : ms1.regs = ms.regs := by simp only [hms1]
  have hms1failed : ms1.failed = ms.failed := by simp only [hms1]
  have hf1 : ms1.failed = false := by rw [hms1failed]; exact st.failed
  have hstep0 : x64Next ms = ms1 := by
    have hbm0 : bytesInMemoryHOL ms.pc
        (encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
          (totalNum2Zreg source) (totalNum2Zreg right))) ms.mem s1.memDomain := by
      exact hb0
    have hnext := x64Next_binopCmp ms s1.memDomain _ _ _ htn1 htn2 hzop hbm0 st.failed
    rw [hnext, hms1]
  set ms2 : X64State := if evalCond (x64Cmp operator) ms1.flags then
      { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 + (target - 9) }
    else { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 } with hms2
  have hstep1 : x64Next ms1 = ms2 := by
    have hbm1 : bytesInMemoryHOL ms1.pc (encodeInsn (.jcc (x64Cmp operator) (target - 9)))
        ms1.mem s1.memDomain := by
      rw [hms1pc, hms1mem]
      exact hb1
    have hnext := x64Next_jcc_long ms1 s1.memDomain (x64Cmp operator) (target - 9)
      (x64Cmp_ne_zAlways operator) (x64Cmp_ne_zP operator) hr9.1 hr9.2 hbm1 hf1
    rw [hnext, hms2]
  have hcond_eq : evalCond (x64Cmp operator) ms1.flags =
      wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
        (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg right) s1) := by
    have ha : readReg ms (totalNum2Zreg source) = s1.regs source := by
      rw [hsrc']; exact st.reg source hsrc
    have hb : readReg ms (totalNum2Zreg right) = s1.regs right := by
      rw [hrgt']; exact st.reg right hrgt
    have hflags : ms1.flags = binopFlags (if isTest operator then .ztest else .zcmp)
        (s1.regs source) (s1.regs right) ms.flags := by
      simp only [hms1, ha, hb]
    rw [hflags]
    simp only [Flapjack.Compiler.Encoders.AsmSem.regImm,
      Flapjack.Compiler.Encoders.AsmSem.readReg]
    by_cases ht : isTest operator = true
    · simp only [ht, if_true]
      exact evalCond_x64Cmp_test operator ht (s1.regs source) (s1.regs right)
    · have htf : isTest operator = false := by simpa using ht
      simp only [htf]
      exact evalCond_x64Cmp operator htf (s1.regs source) (s1.regs right)
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd]
    split_ifs <;> rfl
  have hcode : allPcs (x64Target.config.encode
      (.jumpCmp operator source (.reg right) target)).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hokS : ∀ s : X64State, s.failed = false → x64StateOk s = true := by
    intro s hs; simp [x64StateOk, hs]
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.binopRR (if isTest operator then .ztest else .zcmp) .z64
      (totalNum2Zreg source) (totalNum2Zreg right), 3, hdec0, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
          (totalNum2Zreg source) (totalNum2Zreg right))).length := by
        rw [hbrlen]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hb0 j hj'
    · intro a ha
      simp [x64Touched] at ha
  have hsafe1 : StepSafe s1.memDomain ms1 := by
    refine ⟨.jcc (x64Cmp operator) (target - 9), 6, ?_, ?_, ?_⟩
    · rw [hms1pc, hms1mem]
      exact hdec1
    · intro j hj
      have hj' : j < (encodeInsn (.jcc (x64Cmp operator) (target - 9))).length := by
        rw [hjcc]; exact hj
      exact bytesInMemoryHOL_domain _ (ms.pc + BitVec.ofNat 64 3) ms.mem s1.memDomain hb1 j hj'
    · intro a ha
      simp [x64Touched] at ha
  have hq : targetStateRel x64Target s2 (x64Next^[1 + 1] ms) := by
    have hi : x64Next^[2] ms = ms2 := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
        Function.iterate_one, hstep0, hstep1]
    show targetStateRel x64Target s2 (x64Next^[2] ms)
    rw [hi]
    by_cases hc : evalCond (x64Cmp operator) ms1.flags = true
    · have hwl : wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg right) s1) = true := by
        rw [← hcond_eq]; exact hc
      have hs2 : s2 = jumpToOffset target s1 := by
        rw [← hupd]
        simp only [asmUpd, hwl, if_true]
      have hms2 : ms2 = { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 + (target - 9) } := by
        simp only [hms2, hc, if_true]
      rw [hms2]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk _ = true
        simp only [x64StateOk, hms1failed, st.failed, Bool.not_false]
      · show ms1.pc + BitVec.ofNat 64 6 + (target - 9) = s2.pc
        rw [hms1pc, st.pc, hs2]
        simp only [jumpToOffset, updPc]
        bv_omega
      · intro a ha
        show ms1.mem a = s2.mem a
        rw [hms1mem, hs2]
        simp only [jumpToOffset, updPc]
        exact st.mem a (hs2dom ▸ ha)
      · intro x hx
        show readReg ms1 x = s2.regs x
        rw [show readReg ms1 x = readReg ms x from by simp only [readReg, hms1regs]]
        rw [hs2]
        simp only [jumpToOffset, updPc]
        exact st.reg x hx
      · intro x hx
        show readXmm ms1 x = s2.fpRegs x
        rw [show readXmm ms1 x = readXmm ms x from rfl]
        rw [hs2]
        simp only [jumpToOffset, updPc]
        exact st.fp x hx
    · have hwl : wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.reg right) s1) = false := by
        rw [← hcond_eq]
        cases h : evalCond (x64Cmp operator) ms1.flags <;> simp_all
      have hs2 : s2 = updPc (s1.pc + BitVec.ofNat 64 9) s1 := by
        rw [← hupd]
        simp only [asmUpd, hwl, Bool.false_eq_true, if_false]
      have hms2 : ms2 = { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 } := by
        simp only [hms2, hc, Bool.false_eq_true, if_false]
      rw [hms2]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk _ = true
        simp only [x64StateOk, hms1failed, st.failed, Bool.not_false]
      · show ms1.pc + BitVec.ofNat 64 6 = s2.pc
        rw [hms1pc, st.pc, hs2]
        simp only [updPc]
        bv_omega
      · intro a ha
        show ms1.mem a = s2.mem a
        rw [hms1mem, hs2]
        simp only [updPc]
        exact st.mem a (hs2dom ▸ ha)
      · intro x hx
        show readReg ms1 x = s2.regs x
        rw [show readReg ms1 x = readReg ms x from by simp only [readReg, hms1regs]]
        rw [hs2]
        simp only [updPc]
        exact st.reg x hx
      · intro x hx
        show readXmm ms1 x = s2.fpRegs x
        rw [show readXmm ms1 x = readXmm ms x from rfl]
        rw [hs2]
        simp only [updPc]
        exact st.fp x hx
  refine encoderCaseStep (.jumpCmp operator source (.reg right) target) s1 s2 ms 1 hs2dom hcode
    ?_ ?_ hq
  · intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simpa using hsafe0
    · rw [Function.iterate_one, hstep0]; exact hsafe1
  · intro k hk1 hk2
    have hk : k = 1 := by omega
    subst hk
    rw [Function.iterate_one, hstep0]
    refine ⟨hokS ms1 hf1, ?_, ?_⟩
    · intro pc _
      rw [hms1mem]
    · rw [hms1pc, st.pc, hlen]
      exact mem_allPcs_zero s1.pc (by omega)


/-! ## The immediate form -/

/-- The shared body of the `jumpCmp` immediate form: one flag-setting
`cmp`/`test` of a register against an immediate, then the conditional jump. -/
theorem jumpCmpImmAux (operator : Cmp) (source : Nat) (value target : BitVec 64)
    (zop : ZBinopName) (w len0 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.jumpCmp operator source (.imm value) target) s2 ∧
      targetStateRel x64Target s1 ms)
    (hsrc : source < 16 ∧ x64Target.config.avoidRegs.contains source = false)
    (hzop : zop = .zcmp ∨ zop = .ztest)
    (henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
      encodeInsn (.binopRI zop .z64 source value) ++
        encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)))
    (hlen : (x64Target.config.encode (.jumpCmp operator source (.imm value) target)).length = w)
    (hlen0 : w = len0 + 6)
    (hbrlen : (encodeInsn (.binopRI zop .z64 source value)).length = len0)
    (hdec0 : decode (byteListReader (encodeInsn (.binopRI zop .z64 source value))) =
      some (.binopRI zop .z64 source value, len0))
    (himm : -(2^31 : Int) ≤ (target - BitVec.ofNat 64 w).toInt ∧
      (target - BitVec.ofNat 64 w).toInt < 2^31)
    (hjcclen : (encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w))).length = 6)
    (hjccdec : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
      (target - BitVec.ofNat 64 w)))) = some (.jcc (x64Cmp operator)
        (target - BitVec.ofNat 64 w), 6))
    (hflags : evalCond (x64Cmp operator)
        (binopFlags zop (readReg ms source) value ms.flags) =
      wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
        (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1)) :
    CaseGoal (.jumpCmp operator source (.imm value) target) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hsrc16 : source < 16 := hsrc.1
  have hupd : asmUpd (.jumpCmp operator source (.imm value) target)
      (s1.pc + BitVec.ofNat 64 w) s1 = s2 := by
    rw [← st.upd, hlen]
  have hbmAll : bytesInMemoryHOL ms.pc
      (encodeInsn (.binopRI zop .z64 source value) ++
        encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w))) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb0, hb1⟩ := (bytesInMemory_append _ _ ms.pc ms.mem s1.memDomain).1 hbmAll
  rw [hbrlen] at hb1
  have hdec0' : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRI zop .z64 source value, len0) :=
    decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb0 hdec0 (by omega)
  have hdec1' : decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64 len0) + BitVec.ofNat 64 k)) =
      some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w), 6) :=
    decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb1 hjccdec (by rw [hjcclen])
  set ms1 : X64State := { ms with
      flags := binopFlags zop (readReg ms source) value ms.flags,
      pc := ms.pc + BitVec.ofNat 64 len0 } with hms1
  have hms1pc : ms1.pc = ms.pc + BitVec.ofNat 64 len0 := by simp only [hms1]
  have hms1mem : ms1.mem = ms.mem := by simp only [hms1]
  have hms1regs : ms1.regs = ms.regs := by simp only [hms1]
  have hms1failed : ms1.failed = ms.failed := by simp only [hms1]
  have hms1flags : ms1.flags = binopFlags zop (readReg ms source) value ms.flags := by
    simp only [hms1]
  have hf1 : ms1.failed = false := by rw [hms1failed]; exact st.failed
  have hstep0 : x64Next ms = ms1 := by
    have hbm0 : bytesInMemoryHOL ms.pc (encodeInsn (.binopRI zop .z64 source value))
        ms.mem s1.memDomain := by
      exact hb0
    have hdec := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm0 hdec0 (by omega)
    rcases hzop with rfl | rfl
    · simp only [x64Next, st.failed, Bool.false_eq_true, if_false, hdec, execInsn, hms1,
        binopFlags]
    · simp only [x64Next, st.failed, Bool.false_eq_true, if_false, hdec, execInsn, hms1,
        binopFlags]
  set ms2 : X64State := if evalCond (x64Cmp operator) ms1.flags then
      { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 + (target - BitVec.ofNat 64 w) }
    else { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 } with hms2
  have hstep1 : x64Next ms1 = ms2 := by
    have hbm1 : bytesInMemoryHOL ms1.pc
        (encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)))
        ms1.mem s1.memDomain := by
      rw [hms1pc, hms1mem]
      exact hb1
    have hnext := x64Next_jcc_long ms1 s1.memDomain (x64Cmp operator)
      (target - BitVec.ofNat 64 w) (x64Cmp_ne_zAlways operator) (x64Cmp_ne_zP operator)
      himm.1 himm.2 hbm1 hf1
    rw [hnext, hms2]
  have hcond_eq : evalCond (x64Cmp operator) ms1.flags =
      wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
        (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1) := by
    rw [hms1flags]
    exact hflags
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd]
    simp only [asmUpd]
    split_ifs <;> rfl
  have hcode : allPcs (x64Target.config.encode
      (.jumpCmp operator source (.imm value) target)).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hokS : ∀ s : X64State, s.failed = false → x64StateOk s = true := by
    intro s hs; simp [x64StateOk, hs]
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.binopRI zop .z64 source value, len0, hdec0', ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.binopRI zop .z64 source value)).length := by
        rw [hbrlen]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hb0 j hj'
    · intro a ha
      simp [x64Touched] at ha
  have hsafe1 : StepSafe s1.memDomain ms1 := by
    refine ⟨.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w), 6, ?_, ?_, ?_⟩
    · rw [hms1pc, hms1mem]
      exact hdec1'
    · intro j hj
      have hj' : j < (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 w))).length := by
        rw [hjcclen]; exact hj
      exact bytesInMemoryHOL_domain _ (ms.pc + BitVec.ofNat 64 len0) ms.mem s1.memDomain hb1 j hj'
    · intro a ha
      simp [x64Touched] at ha
  have hq : targetStateRel x64Target s2 (x64Next^[1 + 1] ms) := by
    have hi : x64Next^[2] ms = ms2 := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
        Function.iterate_one, hstep0, hstep1]
    show targetStateRel x64Target s2 (x64Next^[2] ms)
    rw [hi]
    by_cases hc : evalCond (x64Cmp operator) ms1.flags = true
    · have hwl : wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1) = true := by
        rw [← hcond_eq]; exact hc
      have hs2 : s2 = jumpToOffset target s1 := by
        rw [← hupd]
        simp only [asmUpd, hwl, if_true]
      have hms2' : ms2 = { ms1 with
          pc := ms1.pc + BitVec.ofNat 64 6 + (target - BitVec.ofNat 64 w) } := by
        simp only [hms2, hc, if_true]
      rw [hms2']
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk _ = true
        simp only [x64StateOk, hms1failed, st.failed, Bool.not_false]
      · show ms1.pc + BitVec.ofNat 64 6 + (target - BitVec.ofNat 64 w) = s2.pc
        rw [hms1pc, st.pc, hs2]
        simp only [jumpToOffset, updPc]
        bv_omega
      · intro a ha
        show ms1.mem a = s2.mem a
        rw [hms1mem, hs2]
        simp only [jumpToOffset, updPc]
        exact st.mem a (hs2dom ▸ ha)
      · intro x hx
        show readReg ms1 x = s2.regs x
        rw [show readReg ms1 x = readReg ms x from by simp only [readReg, hms1regs]]
        rw [hs2]
        simp only [jumpToOffset, updPc]
        exact st.reg x hx
      · intro x hx
        show readXmm ms1 x = s2.fpRegs x
        rw [show readXmm ms1 x = readXmm ms x from rfl]
        rw [hs2]
        simp only [jumpToOffset, updPc]
        exact st.fp x hx
    · have hwl : wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1) = false := by
        rw [← hcond_eq]
        cases h : evalCond (x64Cmp operator) ms1.flags <;> simp_all
      have hs2 : s2 = updPc (s1.pc + BitVec.ofNat 64 w) s1 := by
        rw [← hupd]
        simp only [asmUpd, hwl, Bool.false_eq_true, if_false]
      have hms2' : ms2 = { ms1 with pc := ms1.pc + BitVec.ofNat 64 6 } := by
        simp only [hms2, hc, Bool.false_eq_true, if_false]
      rw [hms2']
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk _ = true
        simp only [x64StateOk, hms1failed, st.failed, Bool.not_false]
      · show ms1.pc + BitVec.ofNat 64 6 = s2.pc
        rw [hms1pc, st.pc, hs2, hlen0]
        simp only [updPc]
        bv_omega
      · intro a ha
        show ms1.mem a = s2.mem a
        rw [hms1mem, hs2]
        simp only [updPc]
        exact st.mem a (hs2dom ▸ ha)
      · intro x hx
        show readReg ms1 x = s2.regs x
        rw [show readReg ms1 x = readReg ms x from by simp only [readReg, hms1regs]]
        rw [hs2]
        simp only [updPc]
        exact st.reg x hx
      · intro x hx
        show readXmm ms1 x = s2.fpRegs x
        rw [show readXmm ms1 x = readXmm ms x from rfl]
        rw [hs2]
        simp only [updPc]
        exact st.fp x hx
  refine encoderCaseStep (.jumpCmp operator source (.imm value) target) s1 s2 ms 1 hs2dom
    hcode ?_ ?_ hq
  · intro k hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simpa using hsafe0
    · rw [Function.iterate_one, hstep0]; exact hsafe1
  · intro k hk1 hk2
    have hk : k = 1 := by omega
    subst hk
    rw [Function.iterate_one, hstep0]
    refine ⟨hokS ms1 hf1, ?_, ?_⟩
    · intro pc _
      rw [hms1mem]
    · rw [hms1pc, st.pc, hlen, hlen0]
      exact mem_allPcs_zero s1.pc (by omega)


/-- The `jumpCmp` immediate constructor of `encoder_correct x64Target`. -/
theorem case_jumpCmp_imm (operator : Cmp) (source : Nat) (value target : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.jumpCmp operator source (.imm value) target) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.jumpCmp operator source (.imm value) target) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok0 : asmOkExact (.jumpCmp operator source (.imm value) target) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, Bool.and_eq_true] at hok0
  obtain ⟨hco, hcmpok⟩ := hok0
  simp only [asmCmpOkExact, asmRegImmOkExact, x64Config, Bool.and_eq_true] at hcmpok
  obtain ⟨hsrck, himmk⟩ := hcmpok
  have hsrc : source < 16 ∧ x64Target.config.avoidRegs.contains source = false := by
    simpa [asmRegOkExact, x64Config] using hsrck
  have himm32 : -(2^31 : Int) ≤ value.toInt ∧ value.toInt ≤ 2^31 - 1 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true] at himmk
    rcases himmk with ⟨hxor, _⟩ | hv
    · have hf : (Sum.inr operator == Sum.inl BinOp.xor) = false := rfl
      rw [hf] at hxor
      simp at hxor
    · rw [x64Min32, x64Max32] at hv
      simp only [BitVec.toInt_ofInt] at hv
      exact of_decide_eq_true hv
  obtain ⟨hlo, hhi⟩ := cjump_offset_range target hco
  set w : Nat := (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
    else if source % 16 = 0 then 12 else 13) with hwdef
  have hsrc0 : totalNum2Zreg source = source := totalNum2Zreg_eq source hsrc.1
  have hlen : (x64Target.config.encode (.jumpCmp operator source (.imm value) target)).length = w := by
    rw [x64Target_config, x64Config_encode, hwdef]
    exact x64Enc_jumpCmp_imm_length operator source value target hsrc.1
      (by simpa [x64Target_config] using st.asmOk)
  have ha : readReg ms source = s1.regs source := st.reg source hsrc
  by_cases ht : isTest operator = true
  · have hflags : evalCond (x64Cmp operator)
        (binopFlags .ztest (readReg ms source) value ms.flags) =
        wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1) := by
      rw [ha]
      simp only [Flapjack.Compiler.Encoders.AsmSem.regImm, binopFlags]
      exact evalCond_x64Cmp_test operator ht (s1.regs source) value
    have hw : w = (if source % 16 = 0 then 12 else 13) := by simp [hwdef, ht]
    by_cases hs0 : source % 16 = 0
    · have hw12 : w = 12 := by simp [hw, hs0]
      have hsrc0' : source = 0 := by omega
      have hbrlen : (encodeInsn (.binopRI .ztest .z64 source value)).length = 6 := by
        rw [hsrc0', encodeInsn_binopRI_test_rax value himm32.1 (by omega)]
        simp [binopRITestRaxBytes]
      have hdec0 : decode (byteListReader (encodeInsn (.binopRI .ztest .z64 source value))) =
          some (.binopRI .ztest .z64 source value, 6) := by
        rw [hsrc0']
        exact decode_binopRI_test_rax value himm32.1 (by omega)
      have hjcclen12 : (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 12))).length = 6 :=
        encodeInsn_jcc_long (x64Cmp operator) (target - 12)
          (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
          (cjump_offset_sub_twelve target hlo hhi).1 (cjump_offset_sub_twelve target hlo hhi).2
      have hjccdec12 : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 12)))) =
          some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 12), 6) :=
        decode_jcc_long_other (x64Cmp operator) (x64Cmp_ne_zAlways operator)
          (x64Cmp_ne_zP operator) (target - 12)
          (cjump_offset_sub_twelve target hlo hhi).1 (cjump_offset_sub_twelve target hlo hhi).2
      have henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
          encodeInsn (.binopRI .ztest .z64 source value) ++
            encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)) := by
        rw [hw12, x64Target_config, x64Config_encode]
        refine x64Enc_of_flatMap _ (encodeInsn (.binopRI .ztest .z64 source value) ++
          encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 12))) ?_ ?_
        · simp [x64Ast, ht, hs0, hsrc0]
        · intro h'
          have := congrArg List.length h'
          rw [List.length_append, hbrlen, hjcclen12] at this
          simp at this
      refine jumpCmpImmAux operator source value target .ztest w 6 s1 s2 ms h hsrc
        (by right; rfl) henc hlen (by omega) hbrlen hdec0
        (by rw [hw12]; exact cjump_offset_sub_twelve target hlo hhi)
        (by rw [hw12]; exact hjcclen12) (by rw [hw12]; exact hjccdec12) hflags
    · have hw13 : w = 13 := by simp [hw, hs0]
      have hne0 : source ≠ 0 := by omega
      have hbrlen : (encodeInsn (.binopRI .ztest .z64 source value)).length = 7 := by
        rw [encodeInsn_binopRI_test source hsrc.1 hne0 value himm32.1 (by omega)]
        simp [binopRITestBytes]
      have hdec0 : decode (byteListReader (encodeInsn (.binopRI .ztest .z64 source value))) =
          some (.binopRI .ztest .z64 source value, 7) :=
        decode_binopRI_test source hsrc.1 hne0 value himm32.1 (by omega)
      have hjcclen13 : (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 13))).length = 6 :=
        encodeInsn_jcc_long (x64Cmp operator) (target - 13)
          (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
          (cjump_offset_sub_thirteen target hlo hhi).1 (cjump_offset_sub_thirteen target hlo hhi).2
      have hjccdec13 : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 13)))) =
          some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 13), 6) :=
        decode_jcc_long_other (x64Cmp operator) (x64Cmp_ne_zAlways operator)
          (x64Cmp_ne_zP operator) (target - 13)
          (cjump_offset_sub_thirteen target hlo hhi).1 (cjump_offset_sub_thirteen target hlo hhi).2
      have henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
          encodeInsn (.binopRI .ztest .z64 source value) ++
            encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)) := by
        rw [hw13, x64Target_config, x64Config_encode]
        refine x64Enc_of_flatMap _ (encodeInsn (.binopRI .ztest .z64 source value) ++
          encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 13))) ?_ ?_
        · simp [x64Ast, ht, hs0, hsrc0]
        · intro h'
          have := congrArg List.length h'
          rw [List.length_append, hbrlen, hjcclen13] at this
          simp at this
      refine jumpCmpImmAux operator source value target .ztest w 7 s1 s2 ms h hsrc
        (by right; rfl) henc hlen (by omega) hbrlen hdec0
        (by rw [hw13]; exact cjump_offset_sub_thirteen target hlo hhi)
        (by rw [hw13]; exact hjcclen13) (by rw [hw13]; exact hjccdec13) hflags
  · have htf : isTest operator = false := by simpa using ht
    have hflags : evalCond (x64Cmp operator)
        (binopFlags .zcmp (readReg ms source) value ms.flags) =
        wordCmpHOL operator (Flapjack.Compiler.Encoders.AsmSem.readReg source s1)
          (Flapjack.Compiler.Encoders.AsmSem.regImm (.imm value) s1) := by
      rw [ha]
      simp only [Flapjack.Compiler.Encoders.AsmSem.regImm, binopFlags]
      exact evalCond_x64Cmp operator htf (s1.regs source) value
    have hw : w = (if -128 ≤ value.toInt && value.toInt ≤ 127 then 10
      else if source % 16 = 0 then 12 else 13) := by simp [hwdef, htf]
    by_cases h8 : -128 ≤ value.toInt ∧ value.toInt ≤ 127
    · have hw10 : w = 10 := by simp [hw, h8]
      have hbrlen : (encodeInsn (.binopRI .zcmp .z64 source value)).length = 4 := by
        rw [encodeInsn_binopRI_83 .zcmp source hsrc.1 value (by decide)
          (by decide) h8]
        simp [binopRI83Bytes]
      have hdec0 : decode (byteListReader (encodeInsn (.binopRI .zcmp .z64 source value))) =
          some (.binopRI .zcmp .z64 source value, 4) :=
        decode_binopRI_83 .zcmp source hsrc.1 value (by decide) (by decide) h8
      have hjcclen10 : (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 10))).length = 6 :=
        encodeInsn_jcc_long (x64Cmp operator) (target - 10)
          (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
          (cjump_offset_sub_ten target hlo hhi).1 (cjump_offset_sub_ten target hlo hhi).2
      have hjccdec10 : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
          (target - BitVec.ofNat 64 10)))) =
          some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 10), 6) :=
        decode_jcc_long_other (x64Cmp operator) (x64Cmp_ne_zAlways operator)
          (x64Cmp_ne_zP operator) (target - 10)
          (cjump_offset_sub_ten target hlo hhi).1 (cjump_offset_sub_ten target hlo hhi).2
      have henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
          encodeInsn (.binopRI .zcmp .z64 source value) ++
            encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)) := by
        rw [hw10, x64Target_config, x64Config_encode]
        refine x64Enc_of_flatMap _ (encodeInsn (.binopRI .zcmp .z64 source value) ++
          encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 10))) ?_ ?_
        · simp [x64Ast, htf, h8, hsrc0]
        · intro h'
          have := congrArg List.length h'
          rw [List.length_append, hbrlen, hjcclen10] at this
          simp at this
      refine jumpCmpImmAux operator source value target .zcmp w 4 s1 s2 ms h hsrc
        (by left; rfl) henc hlen (by omega) hbrlen hdec0
        (by rw [hw10]; exact cjump_offset_sub_ten target hlo hhi)
        (by rw [hw10]; exact hjcclen10) (by rw [hw10]; exact hjccdec10) hflags
    · by_cases hs0 : source % 16 = 0
      · have hw12 : w = 12 := by simp [hw, h8, hs0]
        have hsrc0' : source = 0 := by omega
        have hbrlen : (encodeInsn (.binopRI .zcmp .z64 source value)).length = 6 := by
          rw [hsrc0', encodeInsn_binopRI_rax .zcmp value (by decide) h8
            himm32.1 (by omega)]
          simp [binopRIRaxBytes]
        have hdec0 : decode (byteListReader (encodeInsn (.binopRI .zcmp .z64 source value))) =
            some (.binopRI .zcmp .z64 source value, 6) := by
          rw [hsrc0']
          exact decode_binopRI_rax .zcmp value (by decide) h8 himm32.1 (by omega)
        have hjcclen12 : (encodeInsn (.jcc (x64Cmp operator)
            (target - BitVec.ofNat 64 12))).length = 6 :=
          encodeInsn_jcc_long (x64Cmp operator) (target - 12)
            (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
            (cjump_offset_sub_twelve target hlo hhi).1 (cjump_offset_sub_twelve target hlo hhi).2
        have hjccdec12 : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
            (target - BitVec.ofNat 64 12)))) =
            some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 12), 6) :=
          decode_jcc_long_other (x64Cmp operator) (x64Cmp_ne_zAlways operator)
            (x64Cmp_ne_zP operator) (target - 12)
            (cjump_offset_sub_twelve target hlo hhi).1 (cjump_offset_sub_twelve target hlo hhi).2
        have henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
            encodeInsn (.binopRI .zcmp .z64 source value) ++
              encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)) := by
          rw [hw12, x64Target_config, x64Config_encode]
          refine x64Enc_of_flatMap _ (encodeInsn (.binopRI .zcmp .z64 source value) ++
            encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 12))) ?_ ?_
          · simp [x64Ast, htf, h8, hs0, hsrc0]
          · intro h'
            have := congrArg List.length h'
            rw [List.length_append, hbrlen, hjcclen12] at this
            simp at this
        refine jumpCmpImmAux operator source value target .zcmp w 6 s1 s2 ms h hsrc
          (by left; rfl) henc hlen (by omega) hbrlen hdec0
          (by rw [hw12]; exact cjump_offset_sub_twelve target hlo hhi)
          (by rw [hw12]; exact hjcclen12) (by rw [hw12]; exact hjccdec12) hflags
      · have hw13 : w = 13 := by simp [hw, h8, hs0]
        have hne0 : source ≠ 0 := by omega
        have hbrlen : (encodeInsn (.binopRI .zcmp .z64 source value)).length = 7 := by
          rw [encodeInsn_binopRI_81 .zcmp source hsrc.1 value (by decide)
            h8 hne0 himm32.1 (by omega)]
          simp [binopRI81Bytes]
        have hdec0 : decode (byteListReader (encodeInsn (.binopRI .zcmp .z64 source value))) =
            some (.binopRI .zcmp .z64 source value, 7) :=
          decode_binopRI_81 .zcmp source hsrc.1 value (by decide) h8 hne0
            himm32.1 (by omega)
        have hjcclen13 : (encodeInsn (.jcc (x64Cmp operator)
            (target - BitVec.ofNat 64 13))).length = 6 :=
          encodeInsn_jcc_long (x64Cmp operator) (target - 13)
            (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
            (cjump_offset_sub_thirteen target hlo hhi).1 (cjump_offset_sub_thirteen target hlo hhi).2
        have hjccdec13 : decode (byteListReader (encodeInsn (.jcc (x64Cmp operator)
            (target - BitVec.ofNat 64 13)))) =
            some (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 13), 6) :=
          decode_jcc_long_other (x64Cmp operator) (x64Cmp_ne_zAlways operator)
            (x64Cmp_ne_zP operator) (target - 13)
            (cjump_offset_sub_thirteen target hlo hhi).1 (cjump_offset_sub_thirteen target hlo hhi).2
        have henc : x64Target.config.encode (.jumpCmp operator source (.imm value) target) =
            encodeInsn (.binopRI .zcmp .z64 source value) ++
              encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 w)) := by
          rw [hw13, x64Target_config, x64Config_encode]
          refine x64Enc_of_flatMap _ (encodeInsn (.binopRI .zcmp .z64 source value) ++
            encodeInsn (.jcc (x64Cmp operator) (target - BitVec.ofNat 64 13))) ?_ ?_
          · simp [x64Ast, htf, h8, hs0, hsrc0]
          · intro h'
            have := congrArg List.length h'
            rw [List.length_append, hbrlen, hjcclen13] at this
            simp at this
        refine jumpCmpImmAux operator source value target .zcmp w 7 s1 s2 ms h hsrc
          (by left; rfl) henc hlen (by omega) hbrlen hdec0
          (by rw [hw13]; exact cjump_offset_sub_thirteen target hlo hhi)
          (by rw [hw13]; exact hjcclen13) (by rw [hw13]; exact hjccdec13) hflags

end Flapjack.Compiler.Encoders.X64
