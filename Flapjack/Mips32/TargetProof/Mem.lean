import Flapjack.Mips32.TargetProof.Arith
import Mathlib.Tactic.Set

/-! # `encoder_correct mips32Target`: memory instructions

CakeML's asm semantics reads and writes words byte by byte (`read_mem_word`,
`write_mem_word`, little-endian here); Ziren's model uses little-endian `readWord`,
`readHalf`, `writeWord`, `writeHalf`. A non-failing asm step guarantees that every
accessed byte is in the memory domain, which is exactly what the machine's accesses need. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem bytes4 (b0 b1 b2 b3 : BitVec 8) :
    ((((0 : W) <<< (8 : Nat) ||| b3.setWidth 32) <<< (8 : Nat) ||| b2.setWidth 32) <<< (8 : Nat) |||
        b1.setWidth 32) <<< (8 : Nat) ||| b0.setWidth 32 = b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h8 : j < 8
  · simp [h8, hj]
  have e0 : b0.getLsbD j = false := BitVec.getLsbD_of_ge b0 j (by omega)
  by_cases h16 : j < 16
  · simp [h8, hj, show j - 8 < 8 by omega, e0, show j - 8 < 32 by omega]
  have e1 : b1.getLsbD (j - 8) = false := BitVec.getLsbD_of_ge b1 _ (by omega)
  by_cases h24 : j < 24
  · simp [h8, hj, show j - 8 - 8 < 8 by omega, show ¬ j - 8 < 8 by omega, e0, e1,
      show j - 8 < 32 by omega, show j - 8 - 8 < 32 by omega]
  · have e2 : b2.getLsbD (j - 8 - 8) = false := BitVec.getLsbD_of_ge b2 _ (by omega)
    simp [h8, hj, show j - 8 - 8 - 8 < 8 by omega, show ¬ j - 8 < 8 by omega,
      show ¬ j - 8 - 8 < 8 by omega, e0, e1, e2, show j - 8 < 32 by omega,
      show j - 8 - 8 < 32 by omega, show j - 8 - 8 - 8 < 32 by omega]

theorem bytes2 (b0 b1 : BitVec 8) :
    ((0 : W) <<< (8 : Nat) ||| b1.setWidth 32) <<< (8 : Nat) ||| b0.setWidth 32 =
      (b1 ++ b0).zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, BitVec.zeroExtend_eq_setWidth]
  by_cases h8 : j < 8
  · simp [h8, hj]
  have e0 : b0.getLsbD j = false := BitVec.getLsbD_of_ge b0 j (by omega)
  by_cases h16 : j < 16
  · simp [h8, hj, show j - 8 < 8 by omega, e0, show j - 8 < 32 by omega]
  · have e1 : b1.getLsbD (j - 8) = false := BitVec.getLsbD_of_ge b1 _ (by omega)
    simp [h8, hj, show ¬ j - 8 < 8 by omega, e0, e1]

theorem bytes1 (b0 : BitVec 8) :
    (0 : W) <<< (8 : Nat) ||| b0.setWidth 32 = b0.zeroExtend 32 := by
  simp

theorem of_not_decide_false {p : Prop} {inst : Decidable p} (h : ¬ @decide p inst = false) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => exact absurd rfl h

theorem add111 (x : W) : x + 1 + 1 + 1 = x + 3 := by bv_omega
theorem add11 (x : W) : x + 1 + 1 = x + 2 := by bv_omega
theorem add21 (x : W) : x + 2 + 1 = x + 3 := by bv_omega

/-- The machine address of a memory instruction with an in-range offset. -/
theorem addr_eq (ms : State) (base : Fin 32) (off : W) (v : W) (hv : ms.reg base = v)
    (h : asmAddrOffsetOkExact mips32Config off = true) :
    ms.reg base + sext16 (lo16 off) = v + off := by
  simp only [asmAddrOffsetOkExact, asmOffsetOkExact, mips32Config, Bool.and_eq_true] at h
  rw [hv, sext_lo16 off h.1.1 h.1.2]

theorem addr_eq' (ms : State) (base : Fin 32) (off : W) (v : W) (hv : ms.reg base = v)
    (h1 : (-32768 : W).sle off = true) (h2 : off.sle 32767 = true) :
    ms.reg base + sext16 (lo16 off) = v + off := by
  rw [hv, sext_lo16 off h1 h2]

theorem case_load (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .load r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .load r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff : asmAddrOffsetOkExact mips32Config off = true := by simpa using hok.2
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memLoad, addrHOL, readReg, readMemWord_succ, readMemWord,
    updPc, updReg, assertState, hbe, Bool.false_eq_true, if_false, readMem] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, add11, add21, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, d1, d2, d3, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  try replace d2 := of_not_decide_false d2
  try replace d3 := of_not_decide_false d3
  have hx := addr_eq ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, wordAt, hx] at hx'
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr,
      hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', if_false, hx]
    simp only [add11, add21, bytes4, readWord_eq, st.mem _ d0, st.mem _ d1, st.mem _ d2,
      st.mem _ d3]

theorem case_load32 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .load32 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .load32 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff : asmAddrOffsetOkExact mips32Config off = true := by simpa using hok.2
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memLoad, addrHOL, readReg, readMemWord_succ, readMemWord,
    updPc, updReg, assertState, hbe, Bool.false_eq_true, if_false, readMem] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, add11, add21, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, d1, d2, d3, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  try replace d2 := of_not_decide_false d2
  try replace d3 := of_not_decide_false d3
  have hx := addr_eq ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, wordAt, hx] at hx'
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr,
      hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', if_false, hx]
    simp only [add11, add21, bytes4, readWord_eq, st.mem _ d0, st.mem _ d1, st.mem _ d2,
      st.mem _ d3]


theorem byte_shr8 (w : W) : (w >>> (8 : Nat)).setWidth 8 = w.extractLsb' 8 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [show 8 + j = j + 8 by omega]
theorem byte_shr16 (w : W) : ((w >>> (8 : Nat)) >>> (8 : Nat)).setWidth 8 = w.extractLsb' 16 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [show 16 + j = j + 8 + 8 by omega]
theorem byte_shr24 (w : W) :
    (((w >>> (8 : Nat)) >>> (8 : Nat)) >>> (8 : Nat)).setWidth 8 = w.extractLsb' 24 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [show 24 + j = j + 8 + 8 + 8 by omega]
theorem byte_lo (w : W) : w.setWidth 8 = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp

theorem store_word_bytes (m : Mem) (f : W → BitVec 8) (x v a : W) (hma : m.readByte a = f a) :
    (m.writeWord x v).readByte a =
      (if a = x then v.setWidth 8 else if a = x + 1 then (v >>> (8 : Nat)).setWidth 8
       else if a = x + 1 + 1 then ((v >>> (8 : Nat)) >>> (8 : Nat)).setWidth 8
       else if a = x + 1 + 1 + 1 then (((v >>> (8 : Nat)) >>> (8 : Nat)) >>> (8 : Nat)).setWidth 8
       else f a) := by
  rw [readByte_writeWord, add11, add21, byte_lo, byte_shr8, byte_shr16, byte_shr24]
  have n1 : x + 3 ≠ x + 2 := by bv_omega
  have n2 : x + 3 ≠ x + 1 := by bv_omega
  have n3 : x + 3 ≠ x := by bv_omega
  have n4 : x + 2 ≠ x + 1 := by bv_omega
  have n5 : x + 2 ≠ x := by bv_omega
  have n6 : x + 1 ≠ x := by bv_omega
  by_cases e0 : a = x
  · subst e0; simp []
  by_cases e1 : a = x + 1
  · subst e1; simp []
  by_cases e2 : a = x + 2
  · subst e2; simp []
  by_cases e3 : a = x + 3
  · subst e3; simp []
  simp only [if_neg e0, if_neg e1, if_neg e2, if_neg e3, hma]

theorem case_store (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .store r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .store r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff : asmAddrOffsetOkExact mips32Config off = true := by simpa using hok.2
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memStore, addrHOL, readReg, writeMemWord_succ, writeMemWord,
    updPc, updMem, assertState, hbe, Bool.false_eq_true, if_false] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, add11, add21, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, d1, d2, d3, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  try replace d2 := of_not_decide_false d2
  try replace d3 := of_not_decide_false d3
  have hx := addr_eq ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff
  have hv := st.reg _ o1.lt o1.avoid
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, wordAt, hx] at hx'
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · rfl
  · intro a ha
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, hx, hv]
    exact store_word_bytes _ _ _ _ _ (st.mem a ha)
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp [mips32Ast, exec, hr']

theorem case_store32 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .store32 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .store32 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff : asmAddrOffsetOkExact mips32Config off = true := by simpa using hok.2
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memStore, addrHOL, readReg, writeMemWord_succ, writeMemWord,
    updPc, updMem, assertState, hbe, Bool.false_eq_true, if_false] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, add11, add21, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, d1, d2, d3, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  try replace d2 := of_not_decide_false d2
  try replace d3 := of_not_decide_false d3
  have hx := addr_eq ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff
  have hv := st.reg _ o1.lt o1.avoid
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, wordAt, hx] at hx'
    rcases hx' with rfl | rfl | rfl | rfl <;> assumption
  · rfl
  · intro a ha
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, hx, hv]
    exact store_word_bytes _ _ _ _ _ (st.mem a ha)
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp [mips32Ast, exec, hr']

theorem offset_range {f : AsmConfigExact 32 → W → Bool} {off : W}
    (hf : f = asmHwOffsetOkExact ∨ f = asmByteOffsetOkExact) (h : f mips32Config off = true) :
    (-32768 : W).sle off = true ∧ off.sle 32767 = true := by
  rcases hf with rfl | rfl <;>
  · simp only [asmHwOffsetOkExact, asmByteOffsetOkExact, asmOffsetOkExact, mips32Config,
      Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2⟩

theorem case_load16 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .load16 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .load16 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hhw : asmHwOffsetOkExact mips32Config off = true ∧ ¬mips32Config.isa = AsmArchitecture.ag32 := by
    simpa using hok.2
  have hoff := offset_range (Or.inl rfl) hhw.1
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memLoad, addrHOL, readReg, readMemWord_succ, readMemWord,
    updPc, updReg, assertState, hbe, Bool.false_eq_true, if_false, readMem] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, decide_eq_false_iff_not, not_not] at hfail
  obtain ⟨-, d0, d1, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  have hx := addr_eq' ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff.1 hoff.2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, hx] at hx'
    rcases hx' with rfl | rfl <;> assumption
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr,
      hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', if_false, hx]
    simp only [bytes2, readHalf_eq, st.mem _ d0, st.mem _ d1]

theorem case_load8 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .load8 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .load8 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff := offset_range (Or.inr rfl) (by simpa using hok.2)
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memLoad, addrHOL, readReg, readMemWord,
    updPc, updReg, assertState, hbe, Bool.false_eq_true, if_false, readMem] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, decide_eq_false_iff_not, not_not] at hfail
  obtain ⟨-, d0, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  have hx := addr_eq' ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff.1 hoff.2
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, hx] at hx'
    subst hx'; assumption
  · rfl
  · intro a ha; simp [mips32Ast, exec, setReg_mem]; exact st.mem a ha
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, reg_setReg, reg_mk_gpr,
      hr.regOf_ne_zero, regOf_inj hr.lt o1.lt, hr', if_false, hx]
    simp only [bytes1, st.mem _ d0]

theorem store_half_bytes (m : Mem) (f : W → BitVec 8) (x v a : W) (hma : m.readByte a = f a) :
    (m.writeHalf x (v.extractLsb' 0 16)).readByte a =
      (if a = x then v.setWidth 8 else if a = x + 1 then (v >>> (8 : Nat)).setWidth 8 else f a) := by
  rw [readByte_writeHalf, byte_lo, byte_shr8]
  have n6 : x + 1 ≠ x := by bv_omega
  have e8 : (v.extractLsb' 0 16).extractLsb' 8 8 = v.extractLsb' 8 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp
  have e0 : (v.extractLsb' 0 16).extractLsb' 0 8 = v.extractLsb' 0 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp
  rw [e8, e0]
  by_cases h0 : a = x
  · subst h0; simp []
  by_cases h1 : a = x + 1
  · subst h1; simp []
  simp only [if_neg h0, if_neg h1, hma]

theorem store_byte_bytes (m : Mem) (f : W → BitVec 8) (x v a : W) (hma : m.readByte a = f a) :
    (m.writeByte x (v.extractLsb' 0 8)).readByte a = (if a = x then v.setWidth 8 else f a) := by
  rw [readByte_writeByte, byte_lo]
  by_cases h0 : a = x
  · simp [h0]
  · simp only [if_neg h0, hma]

theorem case_store16 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .store16 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .store16 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hhw : asmHwOffsetOkExact mips32Config off = true ∧ ¬mips32Config.isa = AsmArchitecture.ag32 := by
    simpa using hok.2
  have hoff := offset_range (Or.inl rfl) hhw.1
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memStore, addrHOL, readReg, writeMemWord_succ, writeMemWord,
    updPc, updMem, assertState, hbe, Bool.false_eq_true, if_false] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, d1, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  try replace d1 := of_not_decide_false d1
  have hx := addr_eq' ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff.1 hoff.2
  have hv := st.reg _ o1.lt o1.avoid
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, hx] at hx'
    rcases hx' with rfl | rfl <;> assumption
  · rfl
  · intro a ha
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, hx, hv]
    exact store_half_bytes _ _ _ _ _ (st.mem a ha)
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp [mips32Ast, exec, hr']


theorem case_store8 (r1 r2 : Nat) (off : W) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 (.inst (.mem .store8 r1 (.addr r2 off))) s2 ∧
      targetStateRel mips32Target s1 ms) :
    CaseGoal (.inst (.mem .store8 r1 (.addr r2 off))) s1 s2 ms := by
  have st := start _ _ _ _ h
  have hok := st.asmOk
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at hok
  have o1 := regOk_of_asm hok.1.1
  have o2 := regOk_of_asm hok.1.2
  have hoff := offset_range (Or.inr rfl) (by simpa using hok.2)
  have hs2 := st.upd
  have hbe := st.be
  have hfail := st.ok
  simp only [asmUpd, instUpd, memOp, memStore, addrHOL, readReg, writeMemWord,
    updPc, updMem, assertState, hbe, Bool.false_eq_true, if_false] at hs2
  subst hs2
  classical
  simp only [Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, not_or, Bool.not_eq_true] at hfail
  simp only [hbe, Bool.false_eq_true, if_false, decide_eq_false_iff_not,
    not_not] at hfail
  obtain ⟨-, d0, -⟩ := hfail
  try replace d0 := of_not_decide_false d0
  have hx := addr_eq' ms (regOf r2) off _ (st.reg _ o2.lt o2.avoid) hoff.1 hoff.2
  have hv := st.reg _ o1.lt o1.avoid
  apply straightCase' _ _ _ _ st rfl
  · simp [mips32Ast]; exact plain_of_sequential _ rfl
  · simp [mips32Ast]
  · intro k hk x hx'
    simp [mips32Ast] at hk; subst hk
    simp [mips32Ast, touched, hx] at hx'
    subst hx'; assumption
  · rfl
  · intro a ha
    simp only [mips32Ast, List.foldl_cons, List.foldl_nil, exec, hx, hv]
    exact store_byte_bytes _ _ _ _ _ (st.mem a ha)
  · intro r hr
    have hr' := st.reg _ hr.lt hr.avoid
    simp [mips32Ast, exec, hr']


end Flapjack.Mips32.TargetProof
