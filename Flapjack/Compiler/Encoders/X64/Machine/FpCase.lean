import Flapjack.Compiler.Encoders.X64.Machine.DivCase

/-!
# The floating-point cases of `encoder_correct x64Target`

`fp` instructions are the source's `fp_upd` transitions: comparisons write `0`
or `1` to a general register, and the arithmetic moves write a 64-bit word to an
XMM register.  The backend lowers them to the SSE subset this machine models,
and `execSSE` evaluates the floating-point operations with the same
`holFp64*` functions as `fp_upd`, so the values agree by construction.

This file proves the comparison cases (`fpLess`, `fpLessEqual`, `fpEqual`) and
the register-transfer case `fpMovToReg`.  A `comisd` comparison lowers to
`[comisd d1 d2; mov r, 0; jcc zP 4; setcc cc r]`: `comisd` sets `cf` to the
strict less-than, `zf` to equality and `pf` to the unordered (NaN) flag, the
`mov` clears the destination, and the parity branch skips the `setcc` exactly
when an operand is NaN, leaving the source's `0` in place.  The `setcc` writes
only the low byte of the already-cleared register, so the written word is the
source's `0`/`1`.

The remaining `fp` constructors are not yet proved: the machine's `writeXmm`
(`Machine/State.lean`) *or*s the new low word into the old register contents
instead of replacing it, so a `movsd`-style lowering leaves bits of the old
register set.  `case_fpMov` is false under that model, so the move and
arithmetic cases are blocked on repairing `writeXmm`.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## The `comisd` flags and unordered comparisons -/

/-- The `comisd` unordered flag: either operand is NaN. -/
def xmmUnordered (a b : BitVec 64) : Bool := holFp64IsNan a || holFp64IsNan b

/-- The flags `comisd` leaves: `cf` is the strict less-than, `zf` equality, and
`pf` the unordered (NaN) flag. -/
def x64ComisdFlags (a b : BitVec 64) : X64Flags :=
  { cf := !(xmmUnordered a b) && holFp64LessThan a b
    pf := xmmUnordered a b
    af := false
    zf := !(xmmUnordered a b) && holFp64Equal a b
    sf := false
    of := false }

/-- An unordered comparison is never less-than. -/
theorem holFp64LessThan_nan (a b : BitVec 64)
    (h : holFp64IsNan a = true ∨ holFp64IsNan b = true) : holFp64LessThan a b = false := by
  unfold holFp64IsNan holFloatIsNan at h
  unfold holFp64LessThan holFloatLessThan
  cases ha : holFloatValue (holFp64ToFloat a) <;>
    cases hb : holFloatValue (holFp64ToFloat b) <;> simp_all [holFloatCompare]

/-- An unordered comparison is never less-or-equal. -/
theorem holFp64LessEqual_nan (a b : BitVec 64)
    (h : holFp64IsNan a = true ∨ holFp64IsNan b = true) : holFp64LessEqual a b = false := by
  unfold holFp64IsNan holFloatIsNan at h
  unfold holFp64LessEqual holFloatLessEqual
  cases ha : holFloatValue (holFp64ToFloat a) <;>
    cases hb : holFloatValue (holFp64ToFloat b) <;> simp_all [holFloatCompare]

/-- An unordered comparison is never equal. -/
theorem holFp64Equal_nan (a b : BitVec 64)
    (h : holFp64IsNan a = true ∨ holFp64IsNan b = true) : holFp64Equal a b = false := by
  unfold holFp64IsNan holFloatIsNan at h
  unfold holFp64Equal holFloatEqual
  cases ha : holFloatValue (holFp64ToFloat a) <;>
    cases hb : holFloatValue (holFp64ToFloat b) <;> simp_all [holFloatCompare]

/-- Less-or-equal is less-than or equal. -/
theorem holFp64LessEqual_or (a b : BitVec 64) :
    holFp64LessEqual a b = (holFp64LessThan a b || holFp64Equal a b) := by
  unfold holFp64LessEqual holFloatLessEqual holFp64LessThan holFloatLessThan
    holFp64Equal holFloatEqual
  cases hc : holFloatCompare (holFp64ToFloat a) (holFp64ToFloat b) <;> simp_all

/-- An unordered pair has a NaN operand. -/
theorem xmmUnordered_nan (a b : BitVec 64) (h : xmmUnordered a b = true) :
    holFp64IsNan a = true ∨ holFp64IsNan b = true := by
  unfold xmmUnordered at h
  simpa using h

/-- `comisd`'s `cf` is the strict less-than, including the unordered case. -/
theorem holFp64LessThan_unordered (a b : BitVec 64) :
    holFp64LessThan a b = (!(xmmUnordered a b) && holFp64LessThan a b) := by
  by_cases h : xmmUnordered a b = true
  · rw [holFp64LessThan_nan a b (xmmUnordered_nan a b h)]; simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    simp [h']

/-- `comisd`'s `zf` is equality, including the unordered case. -/
theorem holFp64Equal_unordered (a b : BitVec 64) :
    holFp64Equal a b = (!(xmmUnordered a b) && holFp64Equal a b) := by
  by_cases h : xmmUnordered a b = true
  · rw [holFp64Equal_nan a b (xmmUnordered_nan a b h)]; simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    simp [h']

/-- `comisd`'s `cf || zf` is less-or-equal, including the unordered case. -/
theorem holFp64LessEqual_unordered (a b : BitVec 64) :
    holFp64LessEqual a b =
      ((!(xmmUnordered a b) && holFp64LessThan a b) ||
        (!(xmmUnordered a b) && holFp64Equal a b)) := by
  rw [holFp64LessEqual_or]
  by_cases h : xmmUnordered a b = true
  · rw [holFp64LessThan_nan a b (xmmUnordered_nan a b h),
      holFp64Equal_nan a b (xmmUnordered_nan a b h)]
    simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    simp [h']

/-- `setcc zB` after `comisd` is the strict less-than. -/
theorem evalCond_zB_comisd (a b : BitVec 64) :
    evalCond .zB (x64ComisdFlags a b) = holFp64LessThan a b := by
  simp only [evalCond, x64ComisdFlags]
  by_cases h : xmmUnordered a b = true
  · rw [holFp64LessThan_nan a b (xmmUnordered_nan a b h)]; simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    simp [h']

/-- `setcc zNA` after `comisd` is less-or-equal. -/
theorem evalCond_zNA_comisd (a b : BitVec 64) :
    evalCond .zNA (x64ComisdFlags a b) = holFp64LessEqual a b := by
  simp only [evalCond, x64ComisdFlags]
  by_cases h : xmmUnordered a b = true
  · rw [holFp64LessEqual_nan a b (xmmUnordered_nan a b h)]; simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    rw [holFp64LessEqual_or]
    simp [h']

/-- `setcc zE` after `comisd` is equality. -/
theorem evalCond_zE_comisd (a b : BitVec 64) :
    evalCond .zE (x64ComisdFlags a b) = holFp64Equal a b := by
  simp only [evalCond, x64ComisdFlags]
  by_cases h : xmmUnordered a b = true
  · rw [holFp64Equal_nan a b (xmmUnordered_nan a b h)]; simp [h]
  · have h' : xmmUnordered a b = false := by simpa using h
    simp [h']

/-- `jcc zP` after `comisd` is the unordered flag. -/
theorem evalCond_zP_comisd (a b : BitVec 64) :
    evalCond .zP (x64ComisdFlags a b) = xmmUnordered a b := by
  simp only [evalCond, x64ComisdFlags]

/-! ## Encoded lengths -/

/-- `comisd` is four bytes for register operands below eight. -/
theorem comisd_length (dst src : Nat) (hd : dst < 16) (hs : src < 16) :
    (encodeInsn (.sse (.comisd dst src))).length = 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0) := by
  interval_cases dst <;> interval_cases src <;> decide

/-- `comisd` on XMM registers is four bytes. -/
theorem comisd_length_lt8 (dst src : Nat) (hd : dst < 8) (hs : src < 8) :
    (encodeInsn (.sse (.comisd dst src))).length = 4 := by
  rw [comisd_length dst src (by omega) (by omega)]
  have h1 : ¬ 8 ≤ dst := by omega
  have h2 : ¬ 8 ≤ src := by omega
  simp [h1, h2]

/-- The parity branch's one-byte form is two bytes. -/
theorem jcc_zP4_length : (encodeInsn (.jcc .zP 4)).length = 2 := by decide

/-- A `setcc` with a forced REX prefix is four bytes. -/
theorem setcc_length (cond : ZCond) (dst : Nat) (hd : dst < 16) (hc : cond ≠ .zAlways) :
    (encodeInsn (.setcc cond true dst)).length = 4 := by
  cases cond <;> first | exact absurd rfl hc | (interval_cases dst <;> decide)

/-- The decoder recovers the parity branch. -/
theorem decode_jcc_zP4 :
    decode (byteListReader (encodeInsn (.jcc .zP 4))) = some (.jcc .zP 4, 2) := by decide

/-! ## One-step execution of the comparison sequence -/

/-- One `x64Next` step over `comisd` writes the comparison flags. -/
theorem x64Next_comisd (ms : X64State) (d : BitVec 64 → Prop) (dst src : Nat)
    (hd : dst < 16) (hs : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.comisd dst src))) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with
      flags := x64ComisdFlags (readXmm ms dst) (readXmm ms src),
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.sse (.comisd dst src))).length } := by
  have hlen := comisd_length dst src hd hs
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.comisd dst src), 4 + (if 8 ≤ dst ∨ 8 ≤ src then 1 else 0)) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_comisd dst src hd hs) (by rw [hlen])
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, execSSE,
    x64ComisdFlags, xmmUnordered]

/-- One `x64Next` step over the parity branch. -/
theorem x64Next_jcc_zP4 (ms : X64State) (d : BitVec 64 → Prop)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.jcc .zP 4)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms =
      (if evalCond .zP ms.flags then
        { ms with pc := ms.pc + BitVec.ofNat 64 2 + 4 }
      else { ms with pc := ms.pc + BitVec.ofNat 64 2 }) := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.jcc .zP 4, 2) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm decode_jcc_zP4 (by decide)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn]

/-- One `x64Next` step over a `setcc` writes the condition's `0`/`1` byte. -/
theorem x64Next_setcc (ms : X64State) (d : BitVec 64 → Prop) (cond : ZCond) (n : Nat)
    (hn : n < 16) (hc : cond ≠ .zAlways)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.setcc cond true n)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeRegSized (.z8 true) n (if evalCond cond ms.flags then 1 else 0) ms with
      pc := ms.pc + BitVec.ofNat 64 4 } := by
  have hlen := setcc_length cond n hn hc
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.setcc cond true n, 4) := by
    have hd := decode_setcc cond n hn hc
    rw [hlen] at hd
    exact decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm hd (by rw [hlen])
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn]

/-- A `setcc` over a cleared register writes the condition's `0`/`1` word. -/
theorem readReg_setcc (ms : X64State) (n x : Nat) (b : Bool) (hn : n < 16) (hx : x < 16)
    (hzero : readReg ms n = 0) :
    readReg (writeRegSized (.z8 true) n (if b then 1 else 0) ms) x =
      if x = n then (if b then 1 else 0) else readReg ms x := by
  rw [writeRegSized, readReg_writeReg _ n _ x hn hx]
  by_cases hxn : x = n
  · subst hxn
    rw [if_pos rfl]
    simp [hzero]
    cases b <;> decide
  · simp only [hxn, if_false]

/-- A `pc` inside the encoding is in the code-coverage set. -/
theorem mem_allPcs_zero {n off : Nat} (a : BitVec 64) (h : off < n) :
    a + BitVec.ofNat 64 off ∈ allPcs n a 0 := by
  rw [allPcs_eq]
  exact ⟨off, by simpa using h, by simp⟩

/-- Two byte offsets compose (local copy, so this module does not need the
carry-case module). -/
theorem fpAddOffset (a : BitVec 64) (m n : Nat) :
    (a + BitVec.ofNat 64 m) + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `pc` arithmetic for the comparison sequence: the four instruction lengths
add up. -/
theorem fpCmp_pc (pc : BitVec 64) (m : Nat) :
    pc + BitVec.ofNat 64 4 + BitVec.ofNat 64 m + BitVec.ofNat 64 2 + BitVec.ofNat 64 4 =
      pc + BitVec.ofNat 64 (4 + m + 2 + 4) := by
  bv_omega

/-! ## The comparison cases -/

/-- The shared body of the `comisd`-and-`setcc` comparison cases: an
interference-free run of three steps when an operand is NaN (the parity branch
skips the `setcc`) and four steps otherwise. -/
theorem fpCmpCase (op : HolFp) (cond : ZCond) (n d1 d2 : Nat)
    (test : BitVec 64 → BitVec 64 → Bool)
    (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp op)) s2 ∧ targetStateRel x64Target s1 ms)
    (hn : n < 16) (hregok : x64Target.config.avoidRegs.contains n = false)
    (hd1 : d1 < 8) (hd2 : d2 < 8) (hcne : cond ≠ .zAlways)
    (henc : x64Target.config.encode (.inst (.fp op)) =
      encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ++ encodeInsn (.movRI .z32 n 0) ++
      encodeInsn (.jcc .zP 4) ++ encodeInsn (.setcc cond true n))
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (x64Target.config.encode (.inst (.fp op))).length)
    (hs2mem : ∀ a, s2.mem a = s1.mem a)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x)
    (hs2regs : ∀ x, s2.regs x = if x = n then
      (if test (s1.fpRegs d1) (s1.fpRegs d2) then 1 else 0) else s1.regs x)
    (hcond : ∀ a b, evalCond cond (x64ComisdFlags a b) = test a b)
    (hnan : ∀ a b, xmmUnordered a b = true → test a b = false) :
    CaseGoal (.inst (.fp op)) s1 s2 ms := by
  have st := x64Start (.inst (.fp op)) s1 s2 ms h
  have hd1' : d1 % 8 = d1 := Nat.mod_eq_of_lt hd1
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlenC : (encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8)))).length = 4 :=
    comisd_length_lt8 (d1 % 8) (d2 % 8) (by omega) (by omega)
  have hlenM : (encodeInsn (.movRI .z32 n 0)).length = 5 + (if 8 ≤ n then 1 else 0) :=
    movRI_z32_length n hn 0 (by decide) (by decide)
  have hlenJ : (encodeInsn (.jcc .zP 4)).length = 2 := jcc_zP4_length
  have hlenS : (encodeInsn (.setcc cond true n)).length = 4 := setcc_length cond n hn hcne
  have htotal : (x64Target.config.encode (.inst (.fp op))).length =
      4 + (5 + (if 8 ≤ n then 1 else 0)) + 2 + 4 := by
    rw [henc, List.length_append, List.length_append, List.length_append,
      hlenC, hlenM, hlenJ, hlenS]
  have htotalE : (x64Enc (.inst (.fp op))).length =
      4 + (5 + (if 8 ≤ n then 1 else 0)) + 2 + 4 := htotal
  set a := readXmm ms (d1 % 8) with ha_def
  set b := readXmm ms (d2 % 8) with hb_def
  have ha : a = s1.fpRegs d1 := by
    rw [ha_def]
    simpa [hd1'] using st.fp d1 hd1
  have hb : b = s1.fpRegs d2 := by
    rw [hb_def]
    simpa [hd2'] using st.fp d2 hd2
  -- the encoding's bytes, split instruction by instruction
  have hbmAll : bytesInMemoryHOL ms.pc
      (encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ++ (encodeInsn (.movRI .z32 n 0) ++
       (encodeInsn (.jcc .zP 4) ++ encodeInsn (.setcc cond true n)))) ms.mem s1.memDomain := by
    have h' : bytesInMemoryHOL ms.pc (x64Target.config.encode (.inst (.fp op))) ms.mem
        s1.memDomain := by
      rw [st.pc]
      exact st.bytesTarget
    rw [henc] at h'
    simpa only [List.append_assoc] using h'
  obtain ⟨hb0, hrest1⟩ :=
    (bytesInMemory_append _ _ ms.pc ms.mem s1.memDomain).1 hbmAll
  rw [hlenC] at hrest1
  obtain ⟨hb1, hrest2⟩ :=
    (bytesInMemory_append _ _ (ms.pc + BitVec.ofNat 64 4) ms.mem s1.memDomain).1 hrest1
  rw [hlenM] at hrest2
  obtain ⟨hb2, hb3⟩ :=
    (bytesInMemory_append _ _
      ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0)))
      ms.mem s1.memDomain).1 hrest2
  rw [hlenJ] at hb3
  have hlt1' : ¬ 8 ≤ d1 % 8 := by omega
  have hlt2' : ¬ 8 ≤ d2 % 8 := by omega
  -- the four decoded instructions
  have dec0 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.comisd (d1 % 8) (d2 % 8)), 4) := by
    have hd := decode_comisd (d1 % 8) (d2 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hb0 hd
      (by simp [hlt1', hlt2', hlenC])
    simpa [hlt1', hlt2'] using h
  have dec1 : decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 k)) =
      some (.movRI .z32 n 0, 5 + (if 8 ≤ n then 1 else 0)) :=
    decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb1
      (decode_movRI_z32 n hn 0 (by decide) (by decide)) (by rw [hlenM])
  have dec2 : decode (fun k => ms.mem
      (((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) +
        BitVec.ofNat 64 k)) = some (.jcc .zP 4, 2) :=
    decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb2 decode_jcc_zP4 (by decide)
  have dec3 : decode (fun k => ms.mem
      ((((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) +
        BitVec.ofNat 64 2) + BitVec.ofNat 64 k)) = some (.setcc cond true n, 4) := by
    have hd := decode_setcc cond n hn hcne
    rw [hlenS] at hd
    exact decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb3 hd (by rw [hlenS])
  -- the states of the run
  set ms1 : X64State := { ms with flags := x64ComisdFlags a b, pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8)))).length } with hms1
  set ms2 : X64State := { (writeReg ms1 n 0) with pc := ms1.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 n 0)).length } with hms2
  have hms1pc : ms1.pc = ms.pc + BitVec.ofNat 64 4 := by simp only [hms1, hlenC]
  have hms1mem : ms1.mem = ms.mem := by simp [hms1]
  have hms1regs : ms1.regs = ms.regs := by simp [hms1]
  have hms1flags : ms1.flags = x64ComisdFlags a b := by simp [hms1]
  have hms1failed : ms1.failed = ms.failed := by simp [hms1]
  have hms2pc : ms2.pc = ms1.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 n 0)).length :=
    by simp [hms2]
  have hms2mem : ms2.mem = ms1.mem := by simp [hms2]
  have hms2regs : ms2.regs = (writeReg ms1 n 0).regs := by simp [hms2]
  have hms2flags : ms2.flags = ms1.flags := by simp [hms2, writeReg_flags]
  have hms2failed : ms2.failed = ms1.failed := by simp [hms2, writeReg_failed]
  have hf1 : ms1.failed = false := by rw [hms1failed]; exact st.failed
  have hf2 : ms2.failed = false := by rw [hms2failed]; exact hf1
  have hread2n : readReg ms2 n = 0 := by
    have h : readReg ms2 n = readReg (writeReg ms1 n 0) n := by
      simp only [readReg, hms2regs]
    rw [h, readReg_writeReg _ n 0 n hn hn]
    simp
  have hread2 : ∀ x, x < 16 → readReg ms2 x = if x = n then 0 else readReg ms1 x := by
    intro x hx
    have h : readReg ms2 x = readReg (writeReg ms1 n 0) x := by
      simp only [readReg, hms2regs]
    rw [h, readReg_writeReg _ n 0 x hn hx]
  have hread1 : ∀ x, x < 16 → x64Target.config.avoidRegs.contains x = false →
      readReg ms1 x = s1.regs x := by
    intro x hx hxav
    have h : readReg ms1 x = readReg ms x := by simp only [readReg, hms1regs]
    rw [h]
    exact st.reg x ⟨hx, hxav⟩
  -- the first two steps
  have hstep0 : x64Next ms = ms1 := by
    rw [x64Next_comisd ms s1.memDomain (d1 % 8) (d2 % 8) (by omega) (by omega) hb0 st.failed,
      ← ha_def, ← hb_def]
  have hstep1 : x64Next ms1 = ms2 := by
    have hbm : bytesInMemoryHOL ms1.pc (encodeInsn (.movRI .z32 n 0)) ms1.mem s1.memDomain := by
      rw [hms1pc, hms1mem]
      exact hb1
    rw [x64Next_const_mov32 ms1 s1.memDomain n 0 hn (by decide) hbm hf1]
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.sse (.comisd (d1 % 8) (d2 % 8)), 4, dec0, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8)))).length := by
        rw [hlenC]; exact hj
      exact bytesInMemoryHOL_domain (encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8)))) ms.pc ms.mem
        s1.memDomain hb0 j hj'
    · intro x hx
      simp [x64Touched] at hx
  have hsafe1 : StepSafe s1.memDomain ms1 := by
    have hdom1 : ∀ j, j < 5 + (if 8 ≤ n then 1 else 0) →
        s1.memDomain ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 j) := by
      intro j hj
      have hj' : j < (encodeInsn (.movRI .z32 n 0)).length := by rw [hlenM]; exact hj
      exact bytesInMemoryHOL_domain (encodeInsn (.movRI .z32 n 0)) (ms.pc + BitVec.ofNat 64 4)
        ms.mem s1.memDomain hb1 j hj'
    refine ⟨.movRI .z32 n 0, 5 + (if 8 ≤ n then 1 else 0), ?_, ?_, ?_⟩
    · rw [hms1pc, hms1mem]
      exact dec1
    · intro j hj
      rw [hms1pc]
      exact hdom1 j hj
    · intro x hx
      simp [x64Touched] at hx
  have hcode : allPcs (x64Target.config.encode (.inst (.fp op))).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hok : ∀ s : X64State, s.failed = false → x64StateOk s = true := by
    intro s hs; simp [x64StateOk, hs]
  by_cases hu : xmmUnordered a b = true
  · -- an operand is NaN: the parity branch skips the `setcc`
    have hflP : evalCond .zP ms2.flags = true := by
      simp only [hms2flags, hms1flags, evalCond_zP_comisd]
      exact hu
    have htest : test (s1.fpRegs d1) (s1.fpRegs d2) = false := by
      have h := hnan a b hu
      rwa [ha, hb] at h
    set ms3 : X64State := { ms2 with pc := ms2.pc + BitVec.ofNat 64 2 + 4 } with hms3
    have hstep2 : x64Next ms2 = ms3 := by
      have hbm : bytesInMemoryHOL ms2.pc (encodeInsn (.jcc .zP 4)) ms2.mem s1.memDomain := by
        rw [hms2pc, hms1pc, hlenM, hms2mem, hms1mem]
        exact hb2
      rw [x64Next_jcc_zP4 ms2 s1.memDomain hbm hf2, hflP]
      simp only [if_true]
      exact hms3.symm
    have hms3pc : ms3.pc = ms2.pc + BitVec.ofNat 64 2 + 4 := by simp [hms3]
    have hms3mem : ms3.mem = ms.mem := by simp [hms3, hms2mem, hms1mem]
    have hms3failed : ms3.failed = ms.failed := by simp [hms3, hms2failed, hms1failed]
    have hf3 : ms3.failed = false := by rw [hms3failed]; exact st.failed
    have hread3n : readReg ms3 n = 0 := by
      have h : readReg ms3 n = readReg ms2 n := by simp only [readReg, hms3]
      rw [h]; exact hread2n
    have hread3 : ∀ x, x < 16 → readReg ms3 x = readReg ms2 x := by
      intro x hx; simp only [readReg, hms3]
    have hsafe2 : StepSafe s1.memDomain ms2 := by
      have hdom2 : ∀ j, j < 2 →
          s1.memDomain (((ms.pc + BitVec.ofNat 64 4) +
            BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) + BitVec.ofNat 64 j) := by
        intro j hj
        have hj' : j < (encodeInsn (.jcc .zP 4)).length := by rw [hlenJ]; exact hj
        exact bytesInMemoryHOL_domain (encodeInsn (.jcc .zP 4))
          ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0)))
          ms.mem s1.memDomain hb2 j hj'
      refine ⟨.jcc .zP 4, 2, ?_, ?_, ?_⟩
      · rw [hms2pc, hms1pc, hlenM]
        exact dec2
      · intro j hj
        rw [hms2pc, hms1pc, hlenM]
        exact hdom2 j hj
      · intro x hx
        simp [x64Touched] at hx
    have hq : targetStateRel x64Target s2 (x64Next^[2 + 1] ms) := by
      have hi : x64Next^[3] ms = ms3 := by
        rw [show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
          show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1, hstep2]
      show targetStateRel x64Target s2 (x64Next^[3] ms)
      rw [hi]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk ms3 = true
        exact hok ms3 hf3
      · show ms3.pc = s2.pc
        rw [hms3pc, hms2pc, hms1pc, hlenM, st.pc, hs2pc, htotal]
        exact fpCmp_pc s1.pc (5 + (if 8 ≤ n then 1 else 0))
      · intro x hx
        show ms3.mem x = s2.mem x
        rw [hms3mem, hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro x hx
        have hx16 : x < 16 := by simpa [x64Target_config, x64Config] using hx.1
        have hxav : x64Target.config.avoidRegs.contains x = false := hx.2
        show readReg ms3 x = s2.regs x
        rw [hs2regs x]
        by_cases hxn : x = n
        · subst hxn
          rw [hread3n, htest]
          simp
        · rw [hread3 x hx16, hread2 x hx16, if_neg hxn, hread1 x hx16 hxav]
          simp [hxn]
      · intro x hx
        have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
        show readXmm ms3 x = s2.fpRegs x
        rw [hs2fp x]
        have h : readXmm ms3 x = readXmm ms x := by
          simp [readXmm, hms3, hms2, hms1, writeReg_xmm]
        rw [h]
        exact st.fp x hx8
    refine encoderCaseStep (.inst (.fp op)) s1 s2 ms 2 hdom hcode ?_ ?_ hq
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl
      · simpa using hsafe0
      · rw [Function.iterate_one, hstep0]; exact hsafe1
      · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1]
        exact hsafe2
    · intro k hk1 hk2
      have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · rw [Function.iterate_one, hstep0]
        refine ⟨hok ms1 hf1, ?_, ?_⟩
        · intro pc _
          rw [hms1mem]
        · simp only [x64Target_config, x64Config]
          rw [hms1pc, st.pc, htotalE]
          exact mem_allPcs_zero s1.pc (by split_ifs <;> omega)
      · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1]
        refine ⟨hok ms2 hf2, ?_, ?_⟩
        · intro pc _
          rw [hms2mem, hms1mem]
        · simp only [x64Target_config, x64Config]
          rw [hms2pc, hms1pc, hlenM, st.pc, htotalE,
            fpAddOffset s1.pc 4 (5 + (if 8 ≤ n then 1 else 0))]
          exact mem_allPcs_zero s1.pc (by split_ifs <;> omega)
  · -- ordered: the `setcc` writes the comparison
    have huf : xmmUnordered a b = false := by simpa using hu
    have hflP : evalCond .zP ms2.flags = false := by
      simp only [hms2flags, hms1flags, evalCond_zP_comisd]
      exact huf
    have hbeq : evalCond cond (x64ComisdFlags a b) = test (s1.fpRegs d1) (s1.fpRegs d2) := by
      rw [hcond, ha, hb]
    set ms3 : X64State := { ms2 with pc := ms2.pc + BitVec.ofNat 64 2 } with hms3
    have hstep2 : x64Next ms2 = ms3 := by
      have hbm : bytesInMemoryHOL ms2.pc (encodeInsn (.jcc .zP 4)) ms2.mem s1.memDomain := by
        rw [hms2pc, hms1pc, hlenM, hms2mem, hms1mem]
        exact hb2
      rw [x64Next_jcc_zP4 ms2 s1.memDomain hbm hf2, hflP]
      exact hms3.symm
    have hms3pc : ms3.pc = ms2.pc + BitVec.ofNat 64 2 := by simp [hms3]
    have hms3mem : ms3.mem = ms.mem := by simp [hms3, hms2mem, hms1mem]
    have hms3failed : ms3.failed = ms.failed := by simp [hms3, hms2failed, hms1failed]
    have hf3 : ms3.failed = false := by rw [hms3failed]; exact st.failed
    have hread3n : readReg ms3 n = 0 := by
      have h : readReg ms3 n = readReg ms2 n := by simp only [readReg, hms3]
      rw [h]; exact hread2n
    have hread3 : ∀ x, x < 16 → readReg ms3 x = readReg ms2 x := by
      intro x hx; simp only [readReg, hms3]
    set ms4 : X64State := { (writeRegSized (.z8 true) n (if evalCond cond (x64ComisdFlags a b) then 1 else 0) ms3) with pc := ms3.pc + BitVec.ofNat 64 4 } with hms4
    have hstep3 : x64Next ms3 = ms4 := by
      have hbm : bytesInMemoryHOL ms3.pc (encodeInsn (.setcc cond true n)) ms3.mem
          s1.memDomain := by
        rw [hms3pc, hms2pc, hms1pc, hlenM, hms3mem]
        exact hb3
      rw [x64Next_setcc ms3 s1.memDomain cond n hn hcne hbm hf3]
      exact hms4.symm
    have hms4pc : ms4.pc = ms3.pc + BitVec.ofNat 64 4 := by simp [hms4]
    have hms4mem : ms4.mem = ms.mem := by simp [hms4, hms3mem]
    have hms4failed : ms4.failed = ms.failed := by
      simp [hms4, hms3failed, writeRegSized, writeReg_failed]
    have hf4 : ms4.failed = false := by rw [hms4failed]; exact st.failed
    have hsafe2 : StepSafe s1.memDomain ms2 := by
      have hdom2 : ∀ j, j < 2 →
          s1.memDomain (((ms.pc + BitVec.ofNat 64 4) +
            BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) + BitVec.ofNat 64 j) := by
        intro j hj
        have hj' : j < (encodeInsn (.jcc .zP 4)).length := by rw [hlenJ]; exact hj
        exact bytesInMemoryHOL_domain (encodeInsn (.jcc .zP 4))
          ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0)))
          ms.mem s1.memDomain hb2 j hj'
      refine ⟨.jcc .zP 4, 2, ?_, ?_, ?_⟩
      · rw [hms2pc, hms1pc, hlenM]
        exact dec2
      · intro j hj
        rw [hms2pc, hms1pc, hlenM]
        exact hdom2 j hj
      · intro x hx
        simp [x64Touched] at hx
    have hsafe3 : StepSafe s1.memDomain ms3 := by
      have hdom3 : ∀ j, j < 4 →
          s1.memDomain ((((ms.pc + BitVec.ofNat 64 4) +
            BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) + BitVec.ofNat 64 2) +
            BitVec.ofNat 64 j) := by
        intro j hj
        have hj' : j < (encodeInsn (.setcc cond true n)).length := by rw [hlenS]; exact hj
        exact bytesInMemoryHOL_domain (encodeInsn (.setcc cond true n))
          (((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 (5 + (if 8 ≤ n then 1 else 0))) +
            BitVec.ofNat 64 2) ms.mem s1.memDomain hb3 j hj'
      refine ⟨.setcc cond true n, 4, ?_, ?_, ?_⟩
      · rw [hms3pc, hms2pc, hms1pc, hlenM, hms3mem]
        exact dec3
      · intro j hj
        rw [hms3pc, hms2pc, hms1pc, hlenM]
        exact hdom3 j hj
      · intro x hx
        simp [x64Touched] at hx
    have hq : targetStateRel x64Target s2 (x64Next^[3 + 1] ms) := by
      have hi : x64Next^[4] ms = ms4 := by
        rw [show (4 : Nat) = 3 + 1 from rfl, Function.iterate_succ_apply,
          show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
          show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1, hstep2, hstep3]
      show targetStateRel x64Target s2 (x64Next^[4] ms)
      rw [hi]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show x64StateOk ms4 = true
        exact hok ms4 hf4
      · show ms4.pc = s2.pc
        rw [hms4pc, hms3pc, hms2pc, hms1pc, hlenM, st.pc, hs2pc, htotal]
        exact fpCmp_pc s1.pc (5 + (if 8 ≤ n then 1 else 0))
      · intro x hx
        show ms4.mem x = s2.mem x
        rw [hms4mem, hs2mem x]
        exact st.mem x (hs2dom ▸ hx)
      · intro x hx
        have hx16 : x < 16 := by simpa [x64Target_config, x64Config] using hx.1
        have hxav : x64Target.config.avoidRegs.contains x = false := hx.2
        show readReg ms4 x = s2.regs x
        rw [hs2regs x]
        have h4 : readReg ms4 x = readReg (writeRegSized (.z8 true) n
            (if evalCond cond (x64ComisdFlags a b) then 1 else 0) ms3) x := by
          simp only [readReg, hms4]
        rw [h4, readReg_setcc ms3 n x _ hn hx16 hread3n, hbeq]
        by_cases hxn : x = n
        · subst hxn
          simp
        · rw [hread3 x hx16, hread2 x hx16, if_neg hxn, hread1 x hx16 hxav]
          simp [hxn]
      · intro x hx
        have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
        show readXmm ms4 x = s2.fpRegs x
        rw [hs2fp x]
        have h : readXmm ms4 x = readXmm ms x := by
          simp [readXmm, hms4, hms3, hms2, hms1, writeRegSized, writeReg_xmm]
        rw [h]
        exact st.fp x hx8
    refine encoderCaseStep (.inst (.fp op)) s1 s2 ms 3 hdom hcode ?_ ?_ hq
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl
      · simpa using hsafe0
      · rw [Function.iterate_one, hstep0]; exact hsafe1
      · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1]
        exact hsafe2
      · rw [show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
          show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1, hstep2]
        exact hsafe3
    · intro k hk1 hk2
      have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk with rfl | rfl | rfl
      · rw [Function.iterate_one, hstep0]
        refine ⟨hok ms1 hf1, ?_, ?_⟩
        · intro pc _
          rw [hms1mem]
        · simp only [x64Target_config, x64Config]
          rw [hms1pc, st.pc, htotalE]
          exact mem_allPcs_zero s1.pc (by split_ifs <;> omega)
      · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1]
        refine ⟨hok ms2 hf2, ?_, ?_⟩
        · intro pc _
          rw [hms2mem, hms1mem]
        · simp only [x64Target_config, x64Config]
          rw [hms2pc, hms1pc, hlenM, st.pc, htotalE,
            fpAddOffset s1.pc 4 (5 + (if 8 ≤ n then 1 else 0))]
          exact mem_allPcs_zero s1.pc (by split_ifs <;> omega)
      · rw [show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
          show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
          Function.iterate_one, hstep0, hstep1, hstep2]
        refine ⟨hok ms3 hf3, ?_, ?_⟩
        · intro pc _
          rw [hms3mem]
        · simp only [x64Target_config, x64Config]
          rw [hms3pc, hms2pc, hms1pc, hlenM, st.pc, htotalE,
            fpAddOffset s1.pc 4 (5 + (if 8 ≤ n then 1 else 0)),
            fpAddOffset s1.pc (4 + (5 + (if 8 ≤ n then 1 else 0))) 2]
          exact mem_allPcs_zero s1.pc (by split_ifs <;> omega)


/-- The `fpLess` constructor of `encoder_correct x64Target`. -/
theorem case_fpLess (n d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpLess n d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpLess n d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpLess n d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hnok, hd1ok⟩, hd2ok⟩ := hok
  have hreg := regOk_of_asmRegOk n hnok
  have hn : n < 16 := jumpReg_reg_lt n hnok
  have hnav : x64Target.config.avoidRegs.contains n = false := hreg.2
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpLess n d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2regs : ∀ x, s2.regs x = if x = n then
      (if holFp64LessThan (s1.fpRegs d1) (s1.fpRegs d2) then 1 else 0) else s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, readFpReg]
    rfl
  have henc : x64Target.config.encode (.inst (.fp (.fpLess n d1 d2))) =
      encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ++ encodeInsn (.movRI .z32 n 0) ++
      encodeInsn (.jcc .zP 4) ++ encodeInsn (.setcc .zB true n) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, totalNum2Zreg_eq n hn, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        simp [comisd_length_lt8 (d1 % 8) (d2 % 8) (by omega) (by omega)] at this
      have h3 := (List.append_eq_nil_iff.mp h').1
      have h2 := (List.append_eq_nil_iff.mp h3).1
      exact ha (List.append_eq_nil_iff.mp h2).1
  exact fpCmpCase (.fpLess n d1 d2) .zB n d1 d2 holFp64LessThan s1 s2 ms h hn hnav hd1 hd2
    (by decide) henc hs2pc hs2mem hs2dom hs2fp hs2regs
    (fun a b => evalCond_zB_comisd a b)
    (fun a b hu => holFp64LessThan_nan a b (xmmUnordered_nan a b hu))

/-- The `fpLessEqual` constructor of `encoder_correct x64Target`. -/
theorem case_fpLessEqual (n d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpLessEqual n d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpLessEqual n d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpLessEqual n d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hnok, hd1ok⟩, hd2ok⟩ := hok
  have hreg := regOk_of_asmRegOk n hnok
  have hn : n < 16 := jumpReg_reg_lt n hnok
  have hnav : x64Target.config.avoidRegs.contains n = false := hreg.2
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpLessEqual n d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2regs : ∀ x, s2.regs x = if x = n then
      (if holFp64LessEqual (s1.fpRegs d1) (s1.fpRegs d2) then 1 else 0) else s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, readFpReg]
    rfl
  have henc : x64Target.config.encode (.inst (.fp (.fpLessEqual n d1 d2))) =
      encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ++ encodeInsn (.movRI .z32 n 0) ++
      encodeInsn (.jcc .zP 4) ++ encodeInsn (.setcc .zNA true n) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, totalNum2Zreg_eq n hn, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        simp [comisd_length_lt8 (d1 % 8) (d2 % 8) (by omega) (by omega)] at this
      have h3 := (List.append_eq_nil_iff.mp h').1
      have h2 := (List.append_eq_nil_iff.mp h3).1
      exact ha (List.append_eq_nil_iff.mp h2).1
  exact fpCmpCase (.fpLessEqual n d1 d2) .zNA n d1 d2 holFp64LessEqual s1 s2 ms h hn hnav hd1 hd2
    (by decide) henc hs2pc hs2mem hs2dom hs2fp hs2regs
    (fun a b => evalCond_zNA_comisd a b)
    (fun a b hu => holFp64LessEqual_nan a b (xmmUnordered_nan a b hu))

/-- The `fpEqual` constructor of `encoder_correct x64Target`. -/
theorem case_fpEqual (n d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpEqual n d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpEqual n d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpEqual n d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hnok, hd1ok⟩, hd2ok⟩ := hok
  have hreg := regOk_of_asmRegOk n hnok
  have hn : n < 16 := jumpReg_reg_lt n hnok
  have hnav : x64Target.config.avoidRegs.contains n = false := hreg.2
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpEqual n d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg]
  have hs2regs : ∀ x, s2.regs x = if x = n then
      (if holFp64Equal (s1.fpRegs d1) (s1.fpRegs d2) then 1 else 0) else s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, readFpReg]
    rfl
  have henc : x64Target.config.encode (.inst (.fp (.fpEqual n d1 d2))) =
      encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ++ encodeInsn (.movRI .z32 n 0) ++
      encodeInsn (.jcc .zP 4) ++ encodeInsn (.setcc .zE true n) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, totalNum2Zreg_eq n hn, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.comisd (d1 % 8) (d2 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        simp [comisd_length_lt8 (d1 % 8) (d2 % 8) (by omega) (by omega)] at this
      have h3 := (List.append_eq_nil_iff.mp h').1
      have h2 := (List.append_eq_nil_iff.mp h3).1
      exact ha (List.append_eq_nil_iff.mp h2).1
  exact fpCmpCase (.fpEqual n d1 d2) .zE n d1 d2 holFp64Equal s1 s2 ms h hn hnav hd1 hd2
    (by decide) henc hs2pc hs2mem hs2dom hs2fp hs2regs
    (fun a b => evalCond_zE_comisd a b)
    (fun a b hu => holFp64Equal_nan a b (xmmUnordered_nan a b hu))

/-- `readXmm` depends only on the register number modulo eight. -/
theorem readXmm_congr_mod (s : X64State) {x y : Nat} (h : x % 8 = y % 8) :
    readXmm s x = readXmm s y := by
  simp only [readXmm, h]

/-- The `fpMov` constructor of `encoder_correct x64Target`: one `movsd` copies
the low word of the source XMM register into the destination. -/
theorem case_fpMov (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpMov d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpMov d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpMov d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨hd1ok, hd2ok⟩ := hok
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hd1' : d1 % 8 = d1 := Nat.mod_eq_of_lt hd1
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlt : ¬ (8 ≤ d1 % 8 ∨ 8 ≤ d2 % 8) := by omega
  have hlen : (encodeInsn (.sse (.movsd (d1 % 8) (d2 % 8)))).length = 4 := by
    rw [encodeInsn_movsd (d1 % 8) (d2 % 8) (by omega) (by omega)]
    simp [movsdBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpMov d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d1 then s1.fpRegs d2 else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpMov d1 d2))) =
      encodeInsn (.sse (.movsd (d1 % 8) (d2 % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.movsd (d1 % 8) (d2 % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.movsd (d1 % 8) (d2 % 8)), 4) := by
    have hd := decode_movsd (d1 % 8) (d2 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hnext : x64Next ms = { writeXmm ms (d1 % 8) (readXmm ms (d2 % 8)) with
      pc := ms.pc + BitVec.ofNat 64 4 } := by
    simp only [x64Next, st.failed, Bool.false_eq_true, if_false, hdec, execInsn, execSSE]
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeXmm_failed, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 4 = s2.pc
      rw [st.pc, hs2pc, henc, hlen]
    · intro a ha
      show (writeXmm ms (d1 % 8) (readXmm ms (d2 % 8))).mem a = s2.mem a
      rw [writeXmm_mem, hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      show readReg (writeXmm ms (d1 % 8) (readXmm ms (d2 % 8))) x = s2.regs x
      rw [show readReg (writeXmm ms (d1 % 8) (readXmm ms (d2 % 8))) x = readReg ms x from by
        simp only [readReg, writeXmm_regs]]
      rw [hs2regs x]
      exact st.reg x hx
    · intro x hx
      have hx8lt : x < 8 := by simpa [x64Target_config, x64Config] using hx
      show readXmm (writeXmm ms (d1 % 8) (readXmm ms (d2 % 8))) x = s2.fpRegs x
      by_cases hx1 : x = d1
      · rw [hx1, hd1', readXmm_writeXmm_self, hs2fp d1]
        simp only [if_true]
        rw [hd2']
        exact st.fp d2 hd2
      · have hne : x % 8 ≠ d1 % 8 := by
          rw [Nat.mod_eq_of_lt hx8lt, hd1']
          exact hx1
        rw [hd1']
        rw [readXmm_writeXmm_other ms d1 x _ hne, hs2fp x]
        simp only [if_neg hx1]
        exact st.fp x hx8lt
  have hcode : allPcs (x64Target.config.encode (.inst (.fp (.fpMov d1 d2)))).length
      s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.sse (.movsd (d1 % 8) (d2 % 8)), 4, hdec, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.sse (.movsd (d1 % 8) (d2 % 8)))).length := by
        rw [hlen]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hbm j hj'
    · intro a ha
      simp [x64Touched] at ha
  exact encoderCaseStep (.inst (.fp (.fpMov d1 d2))) s1 s2 ms 0 hs2dom hcode
    (by intro k hk; interval_cases k; exact hsafe0)
    (by intro k hk1 hk2; omega)
    hq


/-- A one-instruction fp case: the source writes the low word of one XMM
register, the model writes the same word in one step, and the written value is
the source's. -/
theorem fpWriteCase (op : HolFp) (insn : X64SSE) (d1 dst : Nat) (L : Nat) (W V : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp op)) s2 ∧ targetStateRel x64Target s1 ms)
    (hd1 : d1 < 8) (hdst : dst = d1 % 8)
    (henc : x64Target.config.encode (.inst (.fp op)) = encodeInsn (.sse insn))
    (hlen : (encodeInsn (.sse insn)).length = L)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) = some (.sse insn, L))
    (hexec : execSSE insn ms = writeXmm ms dst W)
    (htouch : ∀ a, a ∈ x64Touched ms (.sse insn) → s1.memDomain a)
    (hW : W = V)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (x64Target.config.encode (.inst (.fp op))).length)
    (hs2mem : ∀ a, s2.mem a = s1.mem a)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ x, s2.regs x = s1.regs x)
    (hs2fp : ∀ x, s2.fpRegs x = if x = d1 then V else s1.fpRegs x) :
    CaseGoal (.inst (.fp op)) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse insn)) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hnext : x64Next ms = { writeXmm ms dst W with pc := ms.pc + BitVec.ofNat 64 L } := by
    simp only [x64Next, st.failed, Bool.false_eq_true, if_false, hdec, execInsn, hexec]
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeXmm_failed, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 L = s2.pc
      rw [st.pc, hs2pc, henc, hlen]
    · intro a ha
      show (writeXmm ms dst W).mem a = s2.mem a
      rw [writeXmm_mem, hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      show readReg (writeXmm ms dst W) x = s2.regs x
      rw [show readReg (writeXmm ms dst W) x = readReg ms x from by
        simp only [readReg, writeXmm_regs]]
      rw [hs2regs x]
      exact st.reg x hx
    · intro x hx
      have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
      show readXmm (writeXmm ms dst W) x = s2.fpRegs x
      by_cases hx1 : x = d1
      · rw [hx1]
        rw [show readXmm (writeXmm ms dst W) d1 = W from by
          rw [readXmm_congr_mod _ (by omega : d1 % 8 = dst % 8), readXmm_writeXmm_self]]
        rw [hW, hs2fp d1]
        simp
      · have hdst1 : dst = d1 := by rw [hdst, Nat.mod_eq_of_lt hd1]
        have hne : x % 8 ≠ dst % 8 := by
          rw [Nat.mod_eq_of_lt hx8, hdst1, Nat.mod_eq_of_lt hd1]
          exact hx1
        rw [readXmm_writeXmm_other ms dst x W hne, hs2fp x]
        simp only [if_neg hx1]
        exact st.fp x hx8
  have hcode : allPcs (x64Target.config.encode (.inst (.fp op))).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.sse insn, L, hdec, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.sse insn)).length := by rw [hlen]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hbm j hj'
    · intro a ha
      exact htouch a ha
  exact encoderCaseStep (.inst (.fp op)) s1 s2 ms 0 hs2dom hcode
    (by intro k hk; interval_cases k; exact hsafe0)
    (by intro k hk1 hk2; omega)
    hq

/-- The `fpSqrt` constructor of `encoder_correct x64Target`: one `sqrtsd`. -/
theorem case_fpSqrt (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpSqrt d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpSqrt d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpSqrt d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨hd1ok, hd2ok⟩ := hok
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hd1' : d1 % 8 = d1 := Nat.mod_eq_of_lt hd1
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlt : ¬ (8 ≤ d1 % 8 ∨ 8 ≤ d2 % 8) := by omega
  have hlen : (encodeInsn (.sse (.sqrtsd (d1 % 8) (d2 % 8)))).length = 4 := by
    rw [encodeInsn_sqrtsd (d1 % 8) (d2 % 8) (by omega) (by omega)]
    simp [sqrtsdBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpSqrt d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d1 then
      holFp64Sqrt .roundTiesToEven (s1.fpRegs d2) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpSqrt d1 d2))) =
      encodeInsn (.sse (.sqrtsd (d1 % 8) (d2 % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.sqrtsd (d1 % 8) (d2 % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.sqrtsd (d1 % 8) (d2 % 8)), 4) := by
    have hd := decode_sqrtsd (d1 % 8) (d2 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holFp64Sqrt .roundTiesToEven (readXmm ms (d2 % 8)) =
      holFp64Sqrt .roundTiesToEven (s1.fpRegs d2) := by
    rw [hd2']
    rw [st.fp d2 hd2]
  exact fpWriteCase (.fpSqrt d1 d2) (.sqrtsd (d1 % 8) (d2 % 8)) d1 (d1 % 8) 4
    (holFp64Sqrt .roundTiesToEven (readXmm ms (d2 % 8)))
    (holFp64Sqrt .roundTiesToEven (s1.fpRegs d2)) s1 s2 ms h hd1 rfl henc hlen hdec
    rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


/-- The `fpAdd` constructor of `encoder_correct x64Target`: one `sseAdd`-style SSE
operation writing the destination XMM register's low word. -/
theorem case_fpAdd (d l r : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpAdd d l r))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpAdd d l r))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpAdd d l r))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hdeq, hdok⟩, hlok⟩, hrok⟩ := hok
  have hdl : d = l := by simpa using hdeq
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hl : l < 8 := by simpa [asmFpRegOkExact, x64Config] using hlok
  have hr : r < 8 := by simpa [asmFpRegOkExact, x64Config] using hrok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hr' : r % 8 = r := Nat.mod_eq_of_lt hr
  have hlt : ¬ (8 ≤ d % 8 ∨ 8 ≤ r % 8) := by omega
  have hlen : (encodeInsn (.sse (.binSD .sseAdd (d % 8) (r % 8)))).length = 4 := by
    rw [encodeInsn_binSD .sseAdd (d % 8) (r % 8) (by omega) (by omega)]
    simp [binSDBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpAdd d l r)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d then
      holFp64Add .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpAdd d l r))) =
      encodeInsn (.sse (.binSD .sseAdd (d % 8) (r % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.binSD .sseAdd (d % 8) (r % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.binSD .sseAdd (d % 8) (r % 8)), 4) := by
    have hd := decode_binSD .sseAdd (d % 8) (r % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd
      (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holFp64Add .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)) =
      holFp64Add .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) := by
    have h1 : readXmm ms (d % 8) = s1.fpRegs l := by
      rw [hd', hdl]
      exact st.fp l hl
    have h2 : readXmm ms (r % 8) = s1.fpRegs r := by
      rw [hr']
      exact st.fp r hr
    rw [h1, h2]
  exact fpWriteCase (.fpAdd d l r) (.binSD .sseAdd (d % 8) (r % 8)) d (d % 8) 4
    (holFp64Add .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)))
    (holFp64Add .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r)) s1 s2 ms h hd rfl henc hlen
    hdec rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


/-- The `fpSub` constructor of `encoder_correct x64Target`: one `sseSub`-style SSE
operation writing the destination XMM register's low word. -/
theorem case_fpSub (d l r : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpSub d l r))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpSub d l r))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpSub d l r))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hdeq, hdok⟩, hlok⟩, hrok⟩ := hok
  have hdl : d = l := by simpa using hdeq
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hl : l < 8 := by simpa [asmFpRegOkExact, x64Config] using hlok
  have hr : r < 8 := by simpa [asmFpRegOkExact, x64Config] using hrok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hr' : r % 8 = r := Nat.mod_eq_of_lt hr
  have hlt : ¬ (8 ≤ d % 8 ∨ 8 ≤ r % 8) := by omega
  have hlen : (encodeInsn (.sse (.binSD .sseSub (d % 8) (r % 8)))).length = 4 := by
    rw [encodeInsn_binSD .sseSub (d % 8) (r % 8) (by omega) (by omega)]
    simp [binSDBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpSub d l r)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d then
      holFp64Sub .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpSub d l r))) =
      encodeInsn (.sse (.binSD .sseSub (d % 8) (r % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.binSD .sseSub (d % 8) (r % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.binSD .sseSub (d % 8) (r % 8)), 4) := by
    have hd := decode_binSD .sseSub (d % 8) (r % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd
      (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holFp64Sub .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)) =
      holFp64Sub .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) := by
    have h1 : readXmm ms (d % 8) = s1.fpRegs l := by
      rw [hd', hdl]
      exact st.fp l hl
    have h2 : readXmm ms (r % 8) = s1.fpRegs r := by
      rw [hr']
      exact st.fp r hr
    rw [h1, h2]
  exact fpWriteCase (.fpSub d l r) (.binSD .sseSub (d % 8) (r % 8)) d (d % 8) 4
    (holFp64Sub .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)))
    (holFp64Sub .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r)) s1 s2 ms h hd rfl henc hlen
    hdec rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


/-- The `fpMul` constructor of `encoder_correct x64Target`: one `sseMul`-style SSE
operation writing the destination XMM register's low word. -/
theorem case_fpMul (d l r : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpMul d l r))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpMul d l r))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpMul d l r))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hdeq, hdok⟩, hlok⟩, hrok⟩ := hok
  have hdl : d = l := by simpa using hdeq
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hl : l < 8 := by simpa [asmFpRegOkExact, x64Config] using hlok
  have hr : r < 8 := by simpa [asmFpRegOkExact, x64Config] using hrok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hr' : r % 8 = r := Nat.mod_eq_of_lt hr
  have hlt : ¬ (8 ≤ d % 8 ∨ 8 ≤ r % 8) := by omega
  have hlen : (encodeInsn (.sse (.binSD .sseMul (d % 8) (r % 8)))).length = 4 := by
    rw [encodeInsn_binSD .sseMul (d % 8) (r % 8) (by omega) (by omega)]
    simp [binSDBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpMul d l r)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d then
      holFp64Mul .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpMul d l r))) =
      encodeInsn (.sse (.binSD .sseMul (d % 8) (r % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.binSD .sseMul (d % 8) (r % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.binSD .sseMul (d % 8) (r % 8)), 4) := by
    have hd := decode_binSD .sseMul (d % 8) (r % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd
      (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holFp64Mul .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)) =
      holFp64Mul .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) := by
    have h1 : readXmm ms (d % 8) = s1.fpRegs l := by
      rw [hd', hdl]
      exact st.fp l hl
    have h2 : readXmm ms (r % 8) = s1.fpRegs r := by
      rw [hr']
      exact st.fp r hr
    rw [h1, h2]
  exact fpWriteCase (.fpMul d l r) (.binSD .sseMul (d % 8) (r % 8)) d (d % 8) 4
    (holFp64Mul .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)))
    (holFp64Mul .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r)) s1 s2 ms h hd rfl henc hlen
    hdec rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


/-- The `fpDiv` constructor of `encoder_correct x64Target`: one `sseDiv`-style SSE
operation writing the destination XMM register's low word. -/
theorem case_fpDiv (d l r : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpDiv d l r))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpDiv d l r))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpDiv d l r))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hdeq, hdok⟩, hlok⟩, hrok⟩ := hok
  have hdl : d = l := by simpa using hdeq
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hl : l < 8 := by simpa [asmFpRegOkExact, x64Config] using hlok
  have hr : r < 8 := by simpa [asmFpRegOkExact, x64Config] using hrok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hr' : r % 8 = r := Nat.mod_eq_of_lt hr
  have hlt : ¬ (8 ≤ d % 8 ∨ 8 ≤ r % 8) := by omega
  have hlen : (encodeInsn (.sse (.binSD .sseDiv (d % 8) (r % 8)))).length = 4 := by
    rw [encodeInsn_binSD .sseDiv (d % 8) (r % 8) (by omega) (by omega)]
    simp [binSDBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpDiv d l r)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d then
      holFp64Div .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpDiv d l r))) =
      encodeInsn (.sse (.binSD .sseDiv (d % 8) (r % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.binSD .sseDiv (d % 8) (r % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.binSD .sseDiv (d % 8) (r % 8)), 4) := by
    have hd := decode_binSD .sseDiv (d % 8) (r % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd
      (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holFp64Div .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)) =
      holFp64Div .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r) := by
    have h1 : readXmm ms (d % 8) = s1.fpRegs l := by
      rw [hd', hdl]
      exact st.fp l hl
    have h2 : readXmm ms (r % 8) = s1.fpRegs r := by
      rw [hr']
      exact st.fp r hr
    rw [h1, h2]
  exact fpWriteCase (.fpDiv d l r) (.binSD .sseDiv (d % 8) (r % 8)) d (d % 8) 4
    (holFp64Div .roundTiesToEven (readXmm ms (d % 8)) (readXmm ms (r % 8)))
    (holFp64Div .roundTiesToEven (s1.fpRegs l) (s1.fpRegs r)) s1 s2 ms h hd rfl henc hlen
    hdec rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


/-- The `fpMovFromReg` constructor of `encoder_correct x64Target`: one 64-bit
`movq` from a general register into the destination XMM register. -/
theorem case_fpMovFromReg (d r1 r2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpMovFromReg d r1 r2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpMovFromReg d r1 r2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpMovFromReg d r1 r2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hrok, hmid⟩, hdok⟩ := hok
  have hreg := regOk_of_asmRegOk r1 hrok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hrok
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hlen : (encodeInsn (.sse (.movDQ true true (d % 8) (.zr r1)))).length = 5 := by
    rw [encodeInsn_movDQ true true (d % 8) r1 (by omega) hr1]
    simp [movDQBytes]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpMovFromReg d r1 r2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d then (s1.regs r1).setWidth 64 else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, if_true,
      Flapjack.Compiler.Encoders.AsmSem.readReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpMovFromReg d r1 r2))) =
      encodeInsn (.sse (.movDQ true true (d % 8) (.zr r1))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, totalNum2Zreg_eq r1 hr1, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.movDQ true true (d % 8) (.zr r1))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.movDQ true true (d % 8) (.zr r1)), 5) := by
    have hd0 := decode_movDQ true true (d % 8) r1 (by omega) hr1
    rw [hlen] at hd0
    exact decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd0 (by rw [hlen])
  have hW : readReg ms r1 = (s1.regs r1).setWidth 64 := by
    rw [st.reg r1 hreg]
    simp
  exact fpWriteCase (.fpMovFromReg d r1 r2) (.movDQ true true (d % 8) (.zr r1)) d (d % 8) 5
    (readReg ms r1) ((s1.regs r1).setWidth 64) s1 s2 ms h hd rfl henc hlen hdec rfl
    (by intro a ha; simp [x64Touched, effectiveAddress] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp

/-- The `fpMovToReg` constructor of `encoder_correct x64Target`: one 64-bit
`movq` from the source XMM register into a general register. -/
theorem case_fpMovToReg (r1 r2 d : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpMovToReg r1 r2 d))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpMovToReg r1 r2 d))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpMovToReg r1 r2 d))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hrok, hmid⟩, hdok⟩ := hok
  have hreg := regOk_of_asmRegOk r1 hrok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hrok
  have hd : d < 8 := by simpa [asmFpRegOkExact, x64Config] using hdok
  have hd' : d % 8 = d := Nat.mod_eq_of_lt hd
  have hlen : (encodeInsn (.sse (.movDQ false true (d % 8) (.zr r1)))).length = 5 := by
    rw [encodeInsn_movDQ false true (d % 8) r1 (by omega) hr1]
    simp [movDQBytes]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpMovToReg r1 r2 d)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, if_true]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, if_true]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, if_true]
  have hs2regs : ∀ x, s2.regs x = if x = r1 then (s1.fpRegs d).setWidth 64 else s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, if_true,
      Flapjack.Compiler.Encoders.AsmSem.readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpMovToReg r1 r2 d))) =
      encodeInsn (.sse (.movDQ false true (d % 8) (.zr r1))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, totalNum2Zreg_eq r1 hr1, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.movDQ false true (d % 8) (.zr r1))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.movDQ false true (d % 8) (.zr r1)), 5) := by
    have hd0 := decode_movDQ false true (d % 8) r1 (by omega) hr1
    rw [hlen] at hd0
    exact decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd0 (by rw [hlen])
  have hnext : x64Next ms = { writeReg ms r1 (readXmm ms (d % 8)) with
      pc := ms.pc + BitVec.ofNat 64 5 } := by
    simp only [x64Next, st.failed, Bool.false_eq_true, if_false, hdec, execInsn, execSSE,
      writeRegSized, if_true]
  have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
    show targetStateRel x64Target s2 (x64Next ms)
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg_failed, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 5 = s2.pc
      rw [st.pc, hs2pc, henc, hlen]
    · intro a ha
      show (writeReg ms r1 (readXmm ms (d % 8))).mem a = s2.mem a
      rw [writeReg_mem, hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      have hx16 : x < 16 := by simpa [x64Target_config, x64Config] using hx.1
      show readReg (writeReg ms r1 (readXmm ms (d % 8))) x = s2.regs x
      rw [readReg_writeReg ms r1 _ x hr1 hx16, hs2regs x]
      by_cases hx1 : x = r1
      · rw [if_pos hx1, if_pos hx1]
        rw [hd']
        rw [st.fp d hd]
        simp
      · rw [if_neg hx1, if_neg hx1]
        exact st.reg x hx
    · intro x hx
      have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
      show readXmm (writeReg ms r1 (readXmm ms (d % 8))) x = s2.fpRegs x
      rw [show readXmm (writeReg ms r1 (readXmm ms (d % 8))) x = readXmm ms x from by
        simp only [readXmm, writeReg_xmm]]
      rw [hs2fp x]
      exact st.fp x hx8
  have hcode : allPcs (x64Target.config.encode (.inst (.fp (.fpMovToReg r1 r2 d)))).length
      s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.sse (.movDQ false true (d % 8) (.zr r1)), 5, hdec, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.sse (.movDQ false true (d % 8) (.zr r1)))).length := by
        rw [hlen]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hbm j hj'
    · intro a ha
      simp [x64Touched, effectiveAddress] at ha
  exact encoderCaseStep (.inst (.fp (.fpMovToReg r1 r2 d))) s1 s2 ms 0 hs2dom hcode
    (by intro k hk; interval_cases k; exact hsafe0)
    (by intro k hk1 hk2; omega)
    hq

end Flapjack.Compiler.Encoders.X64
