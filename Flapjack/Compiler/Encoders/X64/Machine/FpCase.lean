module

public import Flapjack.Compiler.Encoders.X64.Machine.DivCase
public import Flapjack.Misc.MachineIeee.SignBits

@[expose] public section

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

The move and arithmetic cases write the source's value into the destination's
low word (`movsd`, `sqrtsd`, the `sseAdd`-style operations, and the integer
conversions).  `writeXmm` (`Machine/State.lean`) keeps the old high word and
replaces the low one, so the written word is the source's value.

The two sign-manipulation cases (`fpAbs`, `fpNeg`) build their mask in the
register itself: `pcmpeqq dst dst` fills both 64-bit lanes with ones, one
per-lane shift (`psrlq`/`psllq`, modelled per lane by `psrlqLanes`/
`psllqLanes`) leaves `0x7FFF…FF` or `0x8000…00` in each lane, and `logicPD`
combines that mask with the source's low word.  `holFp64Abs_eq_and` and
`holFp64Negate_eq_xor` identify the source operations with that masking.

Every `fp` constructor now has a kernel-checked case.
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
theorem setcc_length_fp (cond : ZCond) (dst : Nat) (hd : dst < 16) (hc : cond ≠ .zAlways) :
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
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn, execSSE,
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
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn]

/-- One `x64Next` step over a `setcc` writes the condition's `0`/`1` byte. -/
theorem x64Next_setcc_fp (ms : X64State) (d : BitVec 64 → Prop) (cond : ZCond) (n : Nat)
    (hn : n < 16) (hc : cond ≠ .zAlways)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.setcc cond true n)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeRegSized (.z8 true) n (if evalCond cond ms.flags then 1 else 0) ms with
      pc := ms.pc + BitVec.ofNat 64 4 } := by
  have hlen := setcc_length_fp cond n hn hc
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.setcc cond true n, 4) := by
    have hd := decode_setcc cond n hn hc
    rw [hlen] at hd
    exact decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm hd (by rw [hlen])
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn]

/-- A `setcc` over a cleared register writes the condition's `0`/`1` word. -/
theorem readReg_setcc (ms : X64State) (n x : Nat) (b : Bool) (hn : n < 16) (hx : x < 16)
    (hzero : readReg ms n = 0) :
    readReg (writeRegSized (.z8 true) n (if b then 1 else 0) ms) x =
      if x = n then (if b then 1 else 0) else readReg ms x := by
  rw [writeRegSized, readReg_writeReg _ n _ x hn hx]
  by_cases hxn : x = n
  · subst hxn
    rw [ite_eq_left rfl]
    simp [hzero]
    cases b <;> decide
  · simp only [hxn, ite_false]

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

/-- Splitting three instructions' bytes off a `bytesInMemoryHOL` fact (local
copy, so this module does not need the carry-case module). -/
theorem fpBytesInMemory_three (pc : BitVec 64) (l1 l2 l3 : List (BitVec 8))
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc (l1 ++ l2 ++ l3) m dm ↔
      bytesInMemoryHOL pc l1 m dm ∧
      bytesInMemoryHOL (pc + BitVec.ofNat 64 l1.length) l2 m dm ∧
      bytesInMemoryHOL ((pc + BitVec.ofNat 64 l1.length) + BitVec.ofNat 64 l2.length) l3 m dm := by
  rw [bytesInMemory_append, bytesInMemory_append, and_assoc, List.length_append, fpAddOffset]

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
  have hlenS : (encodeInsn (.setcc cond true n)).length = 4 := setcc_length_fp cond n hn hcne
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
      simp only [ite_true]
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
        · rw [hread3 x hx16, hread2 x hx16, ite_eq_right hxn, hread1 x hx16 hxav]
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
      rw [x64Next_setcc_fp ms3 s1.memDomain cond n hn hcne hbm hf3]
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
        · rw [hread3 x hx16, hread2 x hx16, ite_eq_right hxn, hread1 x hx16 hxav]
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

/-- The byte-shift amount `12` of the `fpToInt` lowering, as a natural. -/
theorem toNat_twelve : (12 : BitVec 8).toNat = 12 := by decide

/-- A 32-bit value written into the low word of an XMM register, shifted left
and then right by 96 bits, reads back as its 64-bit zero extension.  The
amounts are annotated `Nat`: with an unannotated literal Lean would pick the
homogeneous `ShiftLeft (Word width)` view from `Flapjack/RiscV/Model.lean`
instead of the `Nat` shift that the `BitVec` bit-index lemmas cover. -/
theorem writeXmm_low32 (s : X64State) (r : Nat) (hr : r < 8) (v : BitVec 32) :
    ((((writeXmm s (r % 8) (BitVec.setWidth 64 v)).xmm (r % 8)) <<< (96 : Nat)) >>>
        (96 : Nat)).setWidth 64 =
      BitVec.setWidth 64 v := by
  simp only [writeXmm, Nat.mod_eq_of_lt hr]
  rw [ite_true]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (BitVec.ofNat 128 (2 ^ 128 - 2 ^ 64)) =
      ((BitVec.allOnes 64).setWidth 128) <<< (64 : Nat) := by decide
  rw [hm]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
  by_cases h32 : i < 32
  · have e1 : 96 + i < 128 := by omega
    have e2 : ¬ (96 + i < 96) := by omega
    have e3 : 96 + i - 96 = i := by omega
    have h64 : i < 64 := by omega
    have h128 : i < 128 := by omega
    simp [h32, e1, e2, e3, h64, h128]
  · have e1 : ¬ (96 + i < 128) := by omega
    have h128 : i < 128 := by omega
    have hge : 32 ≤ i := by omega
    simp [e1, h128, hge]

/-- The HOL 32-bit low extraction of a 64-bit word is a truncation. -/
theorem holWordExtract_31_0 (v : BitVec 64) :
    holWordExtract 31 0 v 32 = BitVec.setWidth 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [holWordExtract, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  norm_num

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
    simp only [x64Next, st.failed, Bool.false_eq_true, ite_false, hdec, execInsn, execSSE]
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
        simp only [ite_true]
        rw [hd2']
        exact st.fp d2 hd2
      · have hne : x % 8 ≠ d1 % 8 := by
          rw [Nat.mod_eq_of_lt hx8lt, hd1']
          exact hx1
        rw [hd1']
        rw [readXmm_writeXmm_other ms d1 x _ hne, hs2fp x]
        simp only [ite_eq_right hx1]
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
    simp only [x64Next, st.failed, Bool.false_eq_true, ite_false, hdec, execInsn, hexec]
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
        simp only [ite_eq_right hx1]
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
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, ite_true,
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
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, ite_true]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, ite_true]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, ite_true]
  have hs2regs : ∀ x, s2.regs x = if x = r1 then (s1.fpRegs d).setWidth 64 else s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updReg, ite_true,
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
    simp only [x64Next, st.failed, Bool.false_eq_true, ite_false, hdec, execInsn, execSSE,
      writeRegSized, ite_true]
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
      · rw [ite_eq_left hx1, ite_eq_left hx1]
        rw [hd']
        rw [st.fp d hd]
        simp
      · rw [ite_eq_right hx1, ite_eq_right hx1]
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


/-- The `fpFromInt` constructor of `encoder_correct x64Target`: one `cvtdq2pd`
converts the low 32 bits of the source XMM register. -/
theorem case_fpFromInt (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpFromInt d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpFromInt d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpFromInt d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨hd1ok, hd2ok⟩ := hok
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlt : ¬ (8 ≤ d1 % 8 ∨ 8 ≤ d2 % 8) := by omega
  have hlen : (encodeInsn (.sse (.cvtdq2pd (d1 % 8) (d2 % 8)))).length = 4 := by
    rw [encodeInsn_cvtdq2pd (d1 % 8) (d2 % 8) (by omega) (by omega)]
    simp [cvtdq2pdBytes, sseRex, hlt]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpFromInt d1 d2)))).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, ite_true]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, ite_true]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, ite_true]
  have hs2fp : ∀ x, s2.fpRegs x = if x = d1 then
      holIntToFp64 .roundTiesToEven (holWordExtract 31 0 (s1.fpRegs d2) 32).toInt
      else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, ite_true,
      Flapjack.Compiler.Encoders.AsmSem.readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpFromInt d1 d2))) =
      encodeInsn (.sse (.cvtdq2pd (d1 % 8) (d2 % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · intro h'
      have := congrArg List.length h'
      simp [hlen] at this
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.sse (.cvtdq2pd (d1 % 8) (d2 % 8))))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.cvtdq2pd (d1 % 8) (d2 % 8)), 4) := by
    have hd := decode_cvtdq2pd (d1 % 8) (d2 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm hd
      (by rw [hlen]; simp [hlt])
    simpa [hlt] using h
  have hW : holIntToFp64 .roundTiesToEven
        (BitVec.setWidth 32 (readXmm ms (d2 % 8))).toInt =
      holIntToFp64 .roundTiesToEven
        (holWordExtract 31 0 (s1.fpRegs d2) 32).toInt := by
    have hread : readXmm ms (d2 % 8) = s1.fpRegs d2 := by
      rw [hd2']
      exact st.fp d2 hd2
    rw [hread, holWordExtract_31_0]
  exact fpWriteCase (.fpFromInt d1 d2) (.cvtdq2pd (d1 % 8) (d2 % 8)) d1 (d1 % 8) 4
    (holIntToFp64 .roundTiesToEven
      (BitVec.setWidth 32 (readXmm ms (d2 % 8))).toInt)
    (holIntToFp64 .roundTiesToEven
      (holWordExtract 31 0 (s1.fpRegs d2) 32).toInt) s1 s2 ms h hd1 rfl henc hlen hdec
    rfl (by intro a ha; simp [x64Touched] at ha) hW hs2pc hs2mem hs2dom hs2regs hs2fp


set_option maxHeartbeats 4000000 in
/-- The `fpToInt` constructor of `encoder_correct x64Target`: `cvtpd2dq` writes
the 32-bit conversion into the low word, and the two byte-shifts move it to the
bottom of the register. -/
theorem case_fpToInt (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpToInt d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpToInt d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpToInt d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨hd1ok, hd2ok⟩ := hok
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hd1' : d1 % 8 = d1 := Nat.mod_eq_of_lt hd1
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlt : ¬ (8 ≤ d1 % 8 ∨ 8 ≤ d2 % 8) := by omega
  have hlt1 : ¬ 8 ≤ d1 % 8 := by omega
  have hlen0 : (encodeInsn (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8)))).length = 4 := by
    rw [encodeInsn_cvtpd2dq (d1 % 8) (d2 % 8) (by omega) (by omega)]
    simp [cvtpd2dqBytes, sseRex, hlt]
  have hd1mod8 : d1 % 8 < 8 := Nat.mod_lt d1 (by decide : 0 < 8)
  have hd1mod16 : d1 % 8 < 16 := by omega
  have hlen1 : (encodeInsn (.sse (.pslldq (d1 % 8) 12))).length = 5 := by
    rw [encodeInsn_pslldq (d1 % 8) hd1mod16 12]
    simp [pslldqBytes, sseRex, hd1mod8]
  have hlen2 : (encodeInsn (.sse (.psrldq (d1 % 8) 12))).length = 5 := by
    rw [encodeInsn_psrldq (d1 % 8) hd1mod16 12]
    simp [psrldqBytes, sseRex, hd1mod8]
  have henc : x64Target.config.encode (.inst (.fp (.fpToInt d1 d2))) =
      encodeInsn (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8))) ++
      encodeInsn (.sse (.pslldq (d1 % 8) 12)) ++
      encodeInsn (.sse (.psrldq (d1 % 8) 12)) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [hlen0] at this
        simp at this
      have h2 := (List.append_eq_nil_iff.mp h').1
      exact ha (List.append_eq_nil_iff.mp h2).1
  have hread : readXmm ms (d2 % 8) = Flapjack.Compiler.Encoders.AsmSem.readFpReg d2 s1 := by
    rw [hd2']
    exact st.fp d2 hd2
  cases hint : holFp64ToInt .roundTiesToEven
      (Flapjack.Compiler.Encoders.AsmSem.readFpReg d2 s1) with
  | none =>
      exfalso
      have hf : s2.failed = true := by
        rw [← st.upd]
        simp only [asmUpd, instUpd, updPc, fpUpd, hint, assertState, Bool.not_false,
          Bool.true_or]
      have hnotfailed := st.ok
      rw [hf] at hnotfailed
      simp at hnotfailed
  | some integer =>
      have hintT : holFp64ToInt .roundTiesToEven (readXmm ms (d2 % 8)) = some integer := by
        rw [hread, hint]
      by_cases hchk : (BitVec.ofInt 32 integer).toInt = integer
      · -- the conversion succeeds and fits in 32 bits
        have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
            (x64Target.config.encode (.inst (.fp (.fpToInt d1 d2)))).length := by
          rw [← st.upd]
          simp only [asmUpd, instUpd, updPc]
        have hs2mem : ∀ a, s2.mem a = s1.mem a := by
          rw [← st.upd]; intro a
          simp only [asmUpd, instUpd, updPc, fpUpd, hint, ite_true, updFpReg, assertState]
        have hs2dom : s2.memDomain = s1.memDomain := by
          rw [← st.upd]
          simp only [asmUpd, instUpd, updPc, fpUpd, hint, ite_true, updFpReg, assertState]
        have hs2regs : ∀ x, s2.regs x = s1.regs x := by
          rw [← st.upd]; intro x
          simp only [asmUpd, instUpd, updPc, fpUpd, hint, ite_true, updFpReg, assertState]
        have hs2fp : ∀ x, s2.fpRegs x = if x = d1 then
            BitVec.setWidth 64 (BitVec.ofInt 32 integer) else s1.fpRegs x := by
          intro x
          rw [← st.upd]
          simp only [asmUpd, instUpd, updPc, fpUpd, hint, ite_true, updFpReg, assertState]
        -- the target run
        have hbmAll : bytesInMemoryHOL ms.pc
            (encodeInsn (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8))) ++
             encodeInsn (.sse (.pslldq (d1 % 8) 12)) ++
             encodeInsn (.sse (.psrldq (d1 % 8) 12))) ms.mem s1.memDomain := by
          have h' := st.bytesTarget
          rw [henc] at h'
          rw [← st.pc] at h'
          exact h'
        obtain ⟨hb0, hb1, hb2⟩ :=
          (fpBytesInMemory_three ms.pc _ _ _ ms.mem s1.memDomain).1 hbmAll
        rw [hlen0] at hb1
        rw [hlen0] at hb2
        rw [hlen1] at hb2
        have hdec0 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
            some (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8)), 4) := by
          have hd := decode_cvtpd2dq (d1 % 8) (d2 % 8) (by omega) (by omega)
          have h := decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hb0 hd
            (by rw [hlen0]; simp [hlt])
          simpa [hlt] using h
        have hdec1 : decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64 4) +
            BitVec.ofNat 64 k)) = some (.sse (.pslldq (d1 % 8) 12), 5) := by
          have hd := decode_pslldq (d1 % 8) hd1mod16 12
          have h := decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb1 hd
            (by rw [hlen1]; simp [hlt1])
          simpa [hlt1] using h
        have hdec2 : decode (fun k => ms.mem (((ms.pc + BitVec.ofNat 64 4) +
            BitVec.ofNat 64 5) + BitVec.ofNat 64 k)) =
            some (.sse (.psrldq (d1 % 8) 12), 5) := by
          have hd := decode_psrldq (d1 % 8) hd1mod16 12
          have h := decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb2 hd
            (by rw [hlen2]; simp [hlt1])
          simpa [hlt1, hlen0] using h
        set ms1 : X64State :=
          { writeXmm ms (d1 % 8) (BitVec.setWidth 64 (BitVec.ofInt 32 integer)) with
            pc := ms.pc + BitVec.ofNat 64 4 } with hms1
        set ms2 : X64State :=
          { ms1 with
            xmm := fun r => if r = d1 % 8 then (ms1.xmm (d1 % 8)) <<< (8 * 12)
              else ms1.xmm r,
            pc := ms1.pc + BitVec.ofNat 64 5 } with hms2
        set ms3 : X64State :=
          { ms2 with
            xmm := fun r => if r = d1 % 8 then (ms2.xmm (d1 % 8)) >>> (8 * 12)
              else ms2.xmm r,
            pc := ms2.pc + BitVec.ofNat 64 5 } with hms3
        have hstep0 : x64Next ms = ms1 := by
          simp only [hms1, x64Next, st.failed, Bool.false_eq_true, ite_false, hdec0, execInsn,
            execSSE, hintT, hchk, ne_self_iff_false]
        have hstep1 : x64Next ms1 = ms2 := by
          simp only [hms1, hms2, x64Next, writeXmm_failed, st.failed, Bool.false_eq_true,
            ite_false, writeXmm_mem, hdec1, execInsn, execSSE, Nat.mod_mod, toNat_twelve]
          rfl
        have hstep2 : x64Next ms2 = ms3 := by
          simp only [hms1, hms2, hms3, x64Next, writeXmm_failed, st.failed, Bool.false_eq_true,
            ite_false, writeXmm_mem, hdec2, execInsn, execSSE, Nat.mod_mod, toNat_twelve]
          rfl
        have hms1pc : ms1.pc = ms.pc + BitVec.ofNat 64 4 := by simp only [hms1]
        have hms2pc : ms2.pc = ms1.pc + BitVec.ofNat 64 5 := by simp only [hms2]
        have hms3pc : ms3.pc = ms2.pc + BitVec.ofNat 64 5 := by simp only [hms3]
        have hms1mem : ms1.mem = ms.mem := by simp only [hms1, writeXmm_mem]
        have hms2mem : ms2.mem = ms1.mem := by simp only [hms2]
        have hms3mem : ms3.mem = ms2.mem := by simp only [hms3]
        have hms1regs : ms1.regs = ms.regs := by simp only [hms1, writeXmm_regs]
        have hms2regs : ms2.regs = ms1.regs := by simp only [hms2]
        have hms3regs : ms3.regs = ms2.regs := by simp only [hms3]
        have hms1failed : ms1.failed = ms.failed := by simp only [hms1, writeXmm_failed]
        have hms2failed : ms2.failed = ms1.failed := by simp only [hms2]
        have hms3failed : ms3.failed = ms2.failed := by simp only [hms3]
        have hq : targetStateRel x64Target s2 (x64Next^[2 + 1] ms) := by
          have hi : x64Next^[3] ms = ms3 := by
            rw [show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
              show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
              Function.iterate_one, hstep0, hstep1, hstep2]
          show targetStateRel x64Target s2 (x64Next^[3] ms)
          rw [hi]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show x64StateOk ms3 = true
            simp only [x64StateOk, hms3failed, hms2failed, hms1failed, st.failed, Bool.not_false]
          · show ms3.pc = s2.pc
            rw [hms3pc, hms2pc, hms1pc, hs2pc, st.pc, henc, List.length_append,
              List.length_append, hlen0, hlen1, hlen2]
            rw [fpAddOffset s1.pc 4 5, fpAddOffset s1.pc (4 + 5) 5]
          · intro x hx
            show ms3.mem x = s2.mem x
            rw [hms3mem, hms2mem, hms1mem, hs2mem x]
            exact st.mem x (hs2dom ▸ hx)
          · intro x hx
            show readReg ms3 x = s2.regs x
            rw [show readReg ms3 x = readReg ms x from by
              simp only [readReg, hms3regs, hms2regs, hms1regs]]
            rw [hs2regs x]
            exact st.reg x hx
          · intro x hx
            have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
            show readXmm ms3 x = s2.fpRegs x
            by_cases hx1 : x = d1
            · rw [hx1, hs2fp d1]
              rw [show readXmm ms3 d1 = BitVec.setWidth 64 (BitVec.ofInt 32 integer) from by
                rw [readXmm]
                rw [show ms3.xmm (d1 % 8) = ms2.xmm (d1 % 8) >>> (8 * 12) from by
                  simp [hms3]]
                rw [show ms2.xmm (d1 % 8) = ms1.xmm (d1 % 8) <<< (8 * 12) from by
                  simp [hms2]]
                rw [show ms1.xmm (d1 % 8) =
                    (writeXmm ms (d1 % 8) (BitVec.setWidth 64 (BitVec.ofInt 32 integer))).xmm
                      (d1 % 8) from rfl]
                exact writeXmm_low32 ms d1 hd1 (BitVec.ofInt 32 integer)]
              simp
            · have hne : x % 8 ≠ d1 % 8 := by
                rw [Nat.mod_eq_of_lt hx8, Nat.mod_eq_of_lt hd1]
                exact hx1
              rw [hs2fp x]
              rw [show readXmm ms3 x = readXmm ms x from by
                rw [readXmm]
                rw [show ms3.xmm (x % 8) = ms2.xmm (x % 8) from by
                  simp [hms3, hne]]
                rw [show ms2.xmm (x % 8) = ms1.xmm (x % 8) from by
                  simp [hms2, hne]]
                rw [show ms1.xmm (x % 8) = ms.xmm (x % 8) from by
                  simp [hms1, writeXmm, hne]]
                rw [readXmm]]
              simp only [ite_eq_right hx1]
              exact st.fp x hx8
        have hcode : allPcs (x64Target.config.encode (.inst (.fp (.fpToInt d1 d2)))).length
            s1.pc 0 ⊆ s1.memDomain :=
          bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
        have hsafe0 : StepSafe s1.memDomain ms := by
          refine ⟨.sse (.cvtpd2dq false (d1 % 8) (d2 % 8)), 4, hdec0, ?_, ?_⟩
          · intro j hj
            have hj' : j < (encodeInsn (.sse (.cvtpd2dq false (d1 % 8) (d2 % 8)))).length := by
              rw [hlen0]; exact hj
            exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hb0 j hj'
          · intro a ha
            simp [x64Touched] at ha
        have hsafe1 : StepSafe s1.memDomain ms1 := by
          refine ⟨.sse (.pslldq (d1 % 8) 12), 5, ?_, ?_, ?_⟩
          · rw [hms1]
            exact hdec1
          · intro j hj
            have hj' : j < (encodeInsn (.sse (.pslldq (d1 % 8) 12))).length := by
              rw [hlen1]; exact hj
            exact bytesInMemoryHOL_domain _ (ms.pc + BitVec.ofNat 64 4) ms.mem s1.memDomain
              hb1 j hj'
          · intro a ha
            simp [x64Touched] at ha
        have hsafe2 : StepSafe s1.memDomain ms2 := by
          refine ⟨.sse (.psrldq (d1 % 8) 12), 5, ?_, ?_, ?_⟩
          · rw [hms2]
            exact hdec2
          · intro j hj
            have hj' : j < (encodeInsn (.sse (.psrldq (d1 % 8) 12))).length := by
              rw [hlen2]; exact hj
            exact bytesInMemoryHOL_domain _ ((ms.pc + BitVec.ofNat 64 4) + BitVec.ofNat 64 5)
              ms.mem s1.memDomain hb2 j hj'
          · intro a ha
            simp [x64Touched] at ha
        have hokS : ∀ s : X64State, s.failed = false → x64StateOk s = true := by
          intro s hs; simp [x64StateOk, hs]
        have hf1 : ms1.failed = false := by
          simp only [hms1, writeXmm_failed, st.failed]
        have hf2 : ms2.failed = false := by
          simp only [hms2, hf1]
        refine encoderCaseStep (.inst (.fp (.fpToInt d1 d2))) s1 s2 ms 2 hs2dom hcode ?_ ?_ hq
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
            refine ⟨hokS ms1 hf1, ?_, ?_⟩
            · intro pc _
              rw [hms1mem]
            · rw [hms1pc, st.pc, henc, List.length_append, List.length_append,
                hlen0, hlen1, hlen2]
              exact mem_allPcs_zero s1.pc (by omega)
          · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
              Function.iterate_one, hstep0, hstep1]
            refine ⟨hokS ms2 hf2, ?_, ?_⟩
            · intro pc _
              rw [hms2mem, hms1mem]
            · rw [hms2pc, hms1pc, st.pc, fpAddOffset s1.pc 4 5, henc, List.length_append,
                List.length_append, hlen0, hlen1, hlen2]
              exact mem_allPcs_zero s1.pc (by omega)
      · -- the conversion does not fit in 32 bits: the source fails
        exfalso
        have hchk' : ¬ (integer.bmod 4294967296 = integer) := by
          intro h
          exact hchk (by simpa using h)
        have hdec : decide ((BitVec.ofInt 32 integer).toInt = integer) = false := by
          simp [hchk']
        have hf : s2.failed = true := by
          rw [← st.upd]
          simp only [asmUpd, instUpd, updPc, fpUpd, hint, ite_true, assertState, updFpReg, hdec]
          simp
        have hnotfailed := st.ok
        rw [hf] at hnotfailed
        simp at hnotfailed

def maskApply (lop : SSELogic) (m b : BitVec 64) : BitVec 64 :=
  match lop with
  | .sseAnd => m &&& b
  | .sseAndn => (~~~m) &&& b
  | .sseOr => m ||| b
  | .sseXor => m ^^^ b

theorem logicPD_apply (s : X64State) (lop : SSELogic) (dst src : Nat) :
    execSSE (.logicPD lop dst src) s =
      writeXmm s dst (maskApply lop (readXmm s dst) (readXmm s src)) := by
  cases lop <;> simp only [execSSE, maskApply]

theorem execSSE_pcmpeqq_self (s : X64State) (dst : Nat) :
    execSSE (.pcmpeqq dst dst) s =
      { s with xmm := fun r => if r = dst % 8 then BitVec.ofNat 128 (2 ^ 128 - 1) else s.xmm r } := by
  simp only [execSSE, readXmm, beq_self_eq_true, ite_true]

theorem execSSE_psrlqImm (s : X64State) (dst : Nat) (imm : BitVec 8) :
    execSSE (.psrlqImm dst imm) s =
      { s with xmm := fun r => if r = dst % 8 then psrlqLanes (s.xmm (dst % 8)) imm.toNat else s.xmm r } := by
  simp only [execSSE]

theorem execSSE_psllqImm (s : X64State) (dst : Nat) (imm : BitVec 8) :
    execSSE (.psllqImm dst imm) s =
      { s with xmm := fun r => if r = dst % 8 then psllqLanes (s.xmm (dst % 8)) imm.toNat else s.xmm r } := by
  simp only [execSSE]

theorem execSSE_shift_const (shift : X64SSE) (sh : BitVec 128 → BitVec 128) (M128 : BitVec 128)
    (d : Nat) (s : X64State)
    (hshift : ∀ (s : X64State), execSSE shift s =
      { s with xmm := fun r => if r = d then sh (s.xmm d) else s.xmm r })
    (hs : s.xmm d = BitVec.ofNat 128 (2 ^ 128 - 1))
    (hsh : sh (BitVec.ofNat 128 (2 ^ 128 - 1)) = M128) :
    execSSE shift s = { s with xmm := fun r => if r = d then M128 else s.xmm r } := by
  rw [hshift s]
  have h : sh (s.xmm d) = M128 := by rw [hs, hsh]
  rw [h]

theorem toNat_one : (1 : BitVec 8).toNat = 1 := by decide

theorem toNat_sixtythree : (63 : BitVec 8).toNat = 63 := by decide

theorem pcmpeqq_length_lt8 (dst src : Nat) (hd : dst < 8) (hs : src < 8) :
    (encodeInsn (.sse (.pcmpeqq dst src))).length = 5 := by
  rw [encodeInsn_pcmpeqq dst src (by omega) (by omega)]
  simp [pcmpeqqBytes, sseRex, hd, hs]

theorem logicPD_length_lt8 (lop : SSELogic) (dst src : Nat) (hd : dst < 8) (hs : src < 8) :
    (encodeInsn (.sse (.logicPD lop dst src))).length = 4 := by
  rw [encodeInsn_logicPD lop dst src (by omega) (by omega)]
  simp [logicPDBytes, sseRex, hd, hs]

theorem psrlqImm_length_lt8 (dst : Nat) (imm : BitVec 8) (hd : dst < 8) :
    (encodeInsn (.sse (.psrlqImm dst imm))).length = 5 := by
  rw [encodeInsn_psrlqImm dst (by omega) imm]
  simp [psrlqBytes, sseRex, hd]

theorem psllqImm_length_lt8 (dst : Nat) (imm : BitVec 8) (hd : dst < 8) :
    (encodeInsn (.sse (.psllqImm dst imm))).length = 5 := by
  rw [encodeInsn_psllqImm dst (by omega) imm]
  simp [psllqBytes, sseRex, hd]

theorem psrlqLanes_allOnes_one :
    psrlqLanes (BitVec.ofNat 128 (2 ^ 128 - 1)) 1 =
      BitVec.ofNat 128 (2 ^ 127 - 2 ^ 64 + 2 ^ 63 - 1) := by decide

theorem psllqLanes_allOnes_63 :
    psllqLanes (BitVec.ofNat 128 (2 ^ 128 - 1)) 63 =
      BitVec.ofNat 128 (2 ^ 127 + 2 ^ 63) := by decide

theorem maskApply_abs (b : BitVec 64) :
    maskApply .sseAnd (BitVec.ofNat 64 (2 ^ 63 - 1)) b = holFp64Abs b := by
  rw [holFp64Abs_eq_and]
  simp only [maskApply]
  exact BitVec.and_comm ..

theorem maskApply_neg (b : BitVec 64) :
    maskApply .sseXor (BitVec.ofNat 64 (2 ^ 63)) b = holFp64Negate b := by
  rw [holFp64Negate_eq_xor]
  simp only [maskApply]
  exact BitVec.xor_comm ..

/-- The shared body of the two mask cases (`fpAbs`, `fpNeg`). -/
theorem fpMaskCase (op : HolFp) (d1 d2 : Nat) (lop : SSELogic) (shift : X64SSE)
    (sh : BitVec 128 → BitVec 128) (M128 : BitVec 128) (M V : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp op)) s2 ∧ targetStateRel x64Target s1 ms)
    (hd1 : d1 < 8) (hd2 : d2 < 8) (hne : d1 % 8 ≠ d2 % 8)
    (henc : x64Target.config.encode (.inst (.fp op)) =
      encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ++ encodeInsn (.sse shift) ++
        encodeInsn (.sse (.logicPD lop (d1 % 8) (d2 % 8))))
    (hlen1 : (encodeInsn (.sse shift)).length = 5)
    (hdecShift : decode (byteListReader (encodeInsn (.sse shift))) = some (.sse shift, 5))
    (hshift : ∀ (s : X64State), execSSE shift s =
      { s with xmm := fun r => if r = d1 % 8 then sh (s.xmm (d1 % 8)) else s.xmm r })
    (htouchShift : ∀ (s : X64State), x64Touched s (.sse shift) = [])
    (hsh : sh (BitVec.ofNat 128 (2 ^ 128 - 1)) = M128)
    (hM : M = M128.setWidth 64)
    (hV : V = maskApply lop M (s1.fpRegs d2))
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (x64Target.config.encode (.inst (.fp op))).length)
    (hs2mem : ∀ a, s2.mem a = s1.mem a)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ x, s2.regs x = s1.regs x)
    (hs2fp : ∀ x, s2.fpRegs x = if x = d1 then V else s1.fpRegs x) :
    CaseGoal (.inst (.fp op)) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hd1' : d1 % 8 = d1 := Nat.mod_eq_of_lt hd1
  have hd2' : d2 % 8 = d2 := Nat.mod_eq_of_lt hd2
  have hlt1 : ¬ 8 ≤ d1 % 8 := by omega
  have hlt2 : ¬ 8 ≤ d2 % 8 := by omega
  have hne' : d2 % 8 ≠ d1 % 8 := by omega
  have hlen0 : (encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8)))).length = 5 :=
    pcmpeqq_length_lt8 _ _ (by omega) (by omega)
  have hlen2 : (encodeInsn (.sse (.logicPD lop (d1 % 8) (d2 % 8)))).length = 4 :=
    logicPD_length_lt8 _ _ _ (by omega) (by omega)
  have htotal : (x64Target.config.encode (.inst (.fp op))).length = 5 + 5 + 4 := by
    rw [henc, List.length_append, List.length_append, hlen0, hlen1, hlen2]
  have hbmAll : bytesInMemoryHOL ms.pc
      (encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ++ encodeInsn (.sse shift) ++
        encodeInsn (.sse (.logicPD lop (d1 % 8) (d2 % 8)))) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb0, hb1, hb2⟩ := (fpBytesInMemory_three ms.pc _ _ _ ms.mem s1.memDomain).1 hbmAll
  rw [hlen0] at hb1
  rw [hlen0, hlen1] at hb2
  have hdec0 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.sse (.pcmpeqq (d1 % 8) (d1 % 8)), 5) := by
    have hd := decode_pcmpeqq (d1 % 8) (d1 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb0 hd (by rw [hlen0]; simp [hlt1])
    simpa [hlt1] using h
  have hdec1 : decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64 5) + BitVec.ofNat 64 k)) =
      some (.sse shift, 5) := by
    have h := decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb1 hdecShift (by rw [hlen1])
    simpa using h
  have hdec2 : decode (fun k => ms.mem (((ms.pc + BitVec.ofNat 64 5) + BitVec.ofNat 64 5) +
      BitVec.ofNat 64 k)) = some (.sse (.logicPD lop (d1 % 8) (d2 % 8)), 4) := by
    have hd := decode_logicPD lop (d1 % 8) (d2 % 8) (by omega) (by omega)
    have h := decode_bytesInMemory _ _ ms.mem s1.memDomain _ _ hb2 hd (by rw [hlen2]; simp [hlt1, hlt2])
    simpa [hlt1, hlt2] using h
  set ms1 : X64State :=
    { ms with
      xmm := fun r => if r = d1 % 8 then BitVec.ofNat 128 (2 ^ 128 - 1) else ms.xmm r,
      pc := ms.pc + BitVec.ofNat 64 5 } with hms1
  have hms1xmm : ms1.xmm (d1 % 8) = BitVec.ofNat 128 (2 ^ 128 - 1) := by rw [hms1]; simp
  have hms1pc : ms1.pc = ms.pc + BitVec.ofNat 64 5 := by simp only [hms1]
  have hms1mem : ms1.mem = ms.mem := by simp only [hms1]
  have hf1 : ms1.failed = false := by rw [hms1]; exact st.failed
  have hdec1' : decode (fun k => ms1.mem (ms1.pc + BitVec.ofNat 64 k)) = some (.sse shift, 5) := by
    rw [hms1pc, hms1mem]
    exact hdec1
  have hstep0 : x64Next ms = ms1 := by
    simp only [hms1, x64Next, st.failed, Bool.false_eq_true, ite_false, hdec0, execInsn,
      execSSE_pcmpeqq_self, Nat.mod_mod]
  set ms2 : X64State :=
    { ms1 with
      xmm := fun r => if r = d1 % 8 then M128 else ms1.xmm r,
      pc := ms1.pc + BitVec.ofNat 64 5 } with hms2
  have hms2pc : ms2.pc = ms1.pc + BitVec.ofNat 64 5 := by simp only [hms2]
  have hms2mem : ms2.mem = ms1.mem := by simp only [hms2]
  have hf2 : ms2.failed = false := by rw [hms2]; exact hf1
  have hdec2' : decode (fun k => ms1.mem ((ms1.pc + BitVec.ofNat 64 5) + BitVec.ofNat 64 k)) =
      some (.sse (.logicPD lop (d1 % 8) (d2 % 8)), 4) := by
    rw [hms1pc, hms1mem]
    exact hdec2
  have hstep1 : x64Next ms1 = ms2 := by
    have hsc : execSSE shift ms1 =
        { ms1 with xmm := fun r => if r = d1 % 8 then M128 else ms1.xmm r } :=
      execSSE_shift_const shift sh M128 (d1 % 8) ms1 hshift hms1xmm hsh
    simp only [hms2, x64Next, hf1, Bool.false_eq_true, ite_false, hdec1', execInsn]
    rw [hsc, hms1]
    simp only [st.failed]
  set ms3 : X64State :=
    { writeXmm ms2 (d1 % 8) (maskApply lop (readXmm ms2 (d1 % 8)) (readXmm ms2 (d2 % 8))) with
      pc := ms2.pc + BitVec.ofNat 64 4 } with hms3
  have hstep2 : x64Next ms2 = ms3 := by
    simp only [hms3, hms2, hf1, x64Next, Bool.false_eq_true, ite_false, hdec2',
      execInsn, logicPD_apply]
  have hms3pc : ms3.pc = ms2.pc + BitVec.ofNat 64 4 := by simp only [hms3]
  have hms3mem : ms3.mem = ms2.mem := by simp only [hms3, writeXmm_mem]
  have hms1regs : ms1.regs = ms.regs := by simp only [hms1]
  have hms2regs : ms2.regs = ms1.regs := by simp only [hms2]
  have hms3regs : ms3.regs = ms2.regs := by simp only [hms3, writeXmm_regs]
  have hms1failed : ms1.failed = ms.failed := by simp only [hms1]
  have hms2failed : ms2.failed = ms1.failed := by simp only [hms2]
  have hms3failed : ms3.failed = ms2.failed := by simp only [hms3, writeXmm_failed]
  have hb : (ms.xmm (d2 % 8)).setWidth 64 = s1.fpRegs d2 := by
    simpa only [readXmm] using st.fp d2 hd2
  have hq : targetStateRel x64Target s2 (x64Next^[2 + 1] ms) := by
    have hi : x64Next^[3] ms = ms3 := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Function.iterate_succ_apply,
        show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
        Function.iterate_one, hstep0, hstep1, hstep2]
    show targetStateRel x64Target s2 (x64Next^[3] ms)
    rw [hi]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show x64StateOk ms3 = true
      simp only [x64StateOk, hms3failed, hms2failed, hms1failed, st.failed, Bool.not_false]
    · show ms3.pc = s2.pc
      rw [hms3pc, hms2pc, hms1pc, hs2pc, st.pc, henc, List.length_append, List.length_append,
        hlen0, hlen1, hlen2]
      rw [fpAddOffset s1.pc 5 5, fpAddOffset s1.pc (5 + 5) 4]
    · intro x hx
      show ms3.mem x = s2.mem x
      rw [hms3mem, hms2mem, hms1mem, hs2mem x]
      exact st.mem x (hs2dom ▸ hx)
    · intro x hx
      show readReg ms3 x = s2.regs x
      rw [show readReg ms3 x = readReg ms x from by
        simp only [readReg, hms3regs, hms2regs, hms1regs]]
      rw [hs2regs x]
      exact st.reg x hx
    · intro x hx
      have hx8 : x < 8 := by simpa [x64Target_config, x64Config] using hx
      show readXmm ms3 x = s2.fpRegs x
      by_cases hx1 : x = d1
      · rw [hx1, hs2fp d1]
        have h3 : readXmm ms3 d1 =
            maskApply lop (readXmm ms2 (d1 % 8)) (readXmm ms2 (d2 % 8)) := by
          simpa [readXmm, hms3] using
            readXmm_writeXmm_self ms2 (d1 % 8)
              (maskApply lop (readXmm ms2 (d1 % 8)) (readXmm ms2 (d2 % 8)))
        have h2a : readXmm ms2 (d1 % 8) = M := by
          simp only [readXmm, hms2, Nat.mod_mod, ite_true]
          rw [hM]
        have h2b : readXmm ms2 (d2 % 8) = s1.fpRegs d2 := by
          simp only [readXmm, hms2, Nat.mod_mod, ite_eq_right hne', hms1]
          exact hb
        rw [h3, h2a, h2b, ← hV]
        simp
      · have hx8' : x % 8 = x := Nat.mod_eq_of_lt hx8
        have hne8 : x % 8 ≠ d1 % 8 := by
          rw [hx8', hd1']; exact hx1
        rw [hs2fp x]
        have hx3 : readXmm ms3 x = readXmm ms2 x := by
          simp only [readXmm, hms3, writeXmm_xmm, Nat.mod_mod, ite_eq_right hne8]
        have hx2 : readXmm ms2 x = readXmm ms x := by
          simp only [readXmm, hms2, ite_eq_right hne8, hms1]
        rw [hx3, hx2]
        simp only [ite_eq_right hx1]
        exact st.fp x hx8
  have hcode : allPcs (x64Target.config.encode (.inst (.fp op))).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hokS : ∀ s : X64State, s.failed = false → x64StateOk s = true := by
    intro s hs; simp [x64StateOk, hs]
  have hsafe0 : StepSafe s1.memDomain ms := by
    refine ⟨.sse (.pcmpeqq (d1 % 8) (d1 % 8)), 5, hdec0, ?_, ?_⟩
    · intro j hj
      have hj' : j < (encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8)))).length := by
        rw [hlen0]; exact hj
      exact bytesInMemoryHOL_domain _ ms.pc ms.mem s1.memDomain hb0 j hj'
    · intro a ha
      simp [x64Touched] at ha
  have hsafe1 : StepSafe s1.memDomain ms1 := by
    refine ⟨.sse shift, 5, ?_, ?_, ?_⟩
    · rw [hms1]; exact hdec1
    · intro j hj
      have hj' : j < (encodeInsn (.sse shift)).length := by rw [hlen1]; exact hj
      exact bytesInMemoryHOL_domain _ (ms.pc + BitVec.ofNat 64 5) ms.mem s1.memDomain hb1 j hj'
    · intro a ha
      rw [htouchShift ms1] at ha
      simp at ha
  have hsafe2 : StepSafe s1.memDomain ms2 := by
    refine ⟨.sse (.logicPD lop (d1 % 8) (d2 % 8)), 4, ?_, ?_, ?_⟩
    · rw [hms2]; exact hdec2
    · intro j hj
      have hj' : j < (encodeInsn (.sse (.logicPD lop (d1 % 8) (d2 % 8)))).length := by
        rw [hlen2]; exact hj
      exact bytesInMemoryHOL_domain _ ((ms.pc + BitVec.ofNat 64 5) + BitVec.ofNat 64 5)
        ms.mem s1.memDomain hb2 j hj'
    · intro a ha
      simp [x64Touched] at ha
  refine encoderCaseStep (.inst (.fp op)) s1 s2 ms 2 hs2dom hcode ?_ ?_ hq
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
      refine ⟨hokS ms1 hf1, ?_, ?_⟩
      · intro pc _
        rw [hms1mem]
      · rw [hms1pc, st.pc, henc, List.length_append, List.length_append, hlen0, hlen1, hlen2]
        exact mem_allPcs_zero s1.pc (by omega)
    · rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_succ_apply,
        Function.iterate_one, hstep0, hstep1]
      refine ⟨hokS ms2 hf2, ?_, ?_⟩
      · intro pc _
        rw [hms2mem, hms1mem]
      · rw [hms2pc, hms1pc, st.pc, fpAddOffset s1.pc 5 5, henc, List.length_append,
          List.length_append, hlen0, hlen1, hlen2]
        exact mem_allPcs_zero s1.pc (by omega)


/-- The `fpAbs` constructor of `encoder_correct x64Target`: fill the destination
register with ones, shift each 64-bit lane right by one to get the sign mask,
and AND it with the source's low word. -/
theorem case_fpAbs (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpAbs d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpAbs d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpAbs d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hdeq, hd1ok⟩, hd2ok⟩ := hok
  have hne0 : d1 ≠ d2 := by simpa using hdeq
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hne : d1 % 8 ≠ d2 % 8 := by
    rw [Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd2]
    exact hne0
  have hlt1 : ¬ 8 ≤ d1 % 8 := by omega
  have hlen1 : (encodeInsn (.sse (.psrlqImm (d1 % 8) 1))).length = 5 :=
    psrlqImm_length_lt8 _ _ (by omega)
  have hdecShift : decode (byteListReader (encodeInsn (.sse (.psrlqImm (d1 % 8) 1)))) =
      some (.sse (.psrlqImm (d1 % 8) 1), 5) := by
    have hd := decode_psrlqImm (d1 % 8) (by omega) 1
    simpa [hlt1] using hd
  have hshift : ∀ (s : X64State), execSSE (.psrlqImm (d1 % 8) 1) s =
      { s with xmm := fun r => if r = d1 % 8 then psrlqLanes (s.xmm (d1 % 8)) 1 else s.xmm r } := by
    intro s
    rw [execSSE_psrlqImm]
    simp only [Nat.mod_mod, toNat_one]
  have htouchShift : ∀ (s : X64State), x64Touched s (.sse (.psrlqImm (d1 % 8) 1)) = [] := by
    intro s; rfl
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpAbs d1 d2)))).length := by
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
      holFp64Abs (s1.fpRegs d2) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpAbs d1 d2))) =
      encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ++
      encodeInsn (.sse (.psrlqImm (d1 % 8) 1)) ++
      encodeInsn (.sse (.logicPD .sseAnd (d1 % 8) (d2 % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [pcmpeqq_length_lt8 _ _ (by omega) (by omega)] at this
        simp at this
      have h2 := (List.append_eq_nil_iff.mp h').1
      exact ha (List.append_eq_nil_iff.mp h2).1
  exact fpMaskCase (.fpAbs d1 d2) d1 d2 .sseAnd (.psrlqImm (d1 % 8) 1)
    (fun v => psrlqLanes v 1) (BitVec.ofNat 128 (2 ^ 127 - 2 ^ 64 + 2 ^ 63 - 1))
    (BitVec.ofNat 64 (2 ^ 63 - 1)) (holFp64Abs (s1.fpRegs d2))
    s1 s2 ms h hd1 hd2 hne henc hlen1 hdecShift hshift htouchShift
    psrlqLanes_allOnes_one (by decide) (maskApply_abs (s1.fpRegs d2)).symm
    hs2pc hs2mem hs2dom hs2regs hs2fp

/-- The `fpNeg` constructor of `encoder_correct x64Target`: fill the destination
register with ones, shift each 64-bit lane left by 63 to get the sign bit, and
XOR it into the source's low word. -/
theorem case_fpNeg (d1 d2 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.fp (.fpNeg d1 d2))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.fp (.fpNeg d1 d2))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.fp (.fpNeg d1 d2))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  simp only [asmOkExact, asmInstOkExact, asmFpOkExact, x64Config, Bool.and_eq_true] at hok
  obtain ⟨⟨hdeq, hd1ok⟩, hd2ok⟩ := hok
  have hne0 : d1 ≠ d2 := by simpa using hdeq
  have hd1 : d1 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd1ok
  have hd2 : d2 < 8 := by simpa [asmFpRegOkExact, x64Config] using hd2ok
  have hne : d1 % 8 ≠ d2 % 8 := by
    rw [Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd2]
    exact hne0
  have hlt1 : ¬ 8 ≤ d1 % 8 := by omega
  have hlen1 : (encodeInsn (.sse (.psllqImm (d1 % 8) 63))).length = 5 :=
    psllqImm_length_lt8 _ _ (by omega)
  have hdecShift : decode (byteListReader (encodeInsn (.sse (.psllqImm (d1 % 8) 63)))) =
      some (.sse (.psllqImm (d1 % 8) 63), 5) := by
    have hd := decode_psllqImm (d1 % 8) (by omega) 63
    simpa [hlt1] using hd
  have hshift : ∀ (s : X64State), execSSE (.psllqImm (d1 % 8) 63) s =
      { s with xmm := fun r => if r = d1 % 8 then psllqLanes (s.xmm (d1 % 8)) 63 else s.xmm r } := by
    intro s
    rw [execSSE_psllqImm]
    simp only [Nat.mod_mod, toNat_sixtythree]
  have htouchShift : ∀ (s : X64State), x64Touched s (.sse (.psllqImm (d1 % 8) 63)) = [] := by
    intro s; rfl
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.fp (.fpNeg d1 d2)))).length := by
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
      holFp64Negate (s1.fpRegs d2) else s1.fpRegs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, fpUpd, updFpReg, readFpReg]
  have henc : x64Target.config.encode (.inst (.fp (.fpNeg d1 d2))) =
      encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ++
      encodeInsn (.sse (.psllqImm (d1 % 8) 63)) ++
      encodeInsn (.sse (.logicPD .sseXor (d1 % 8) (d2 % 8))) := by
    rw [x64Target_config, x64Config_encode]
    refine x64Enc_of_flatMap _ _ ?_ ?_
    · simp only [x64Ast, x64Inst, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc]
    · intro h'
      have ha : encodeInsn (.sse (.pcmpeqq (d1 % 8) (d1 % 8))) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [pcmpeqq_length_lt8 _ _ (by omega) (by omega)] at this
        simp at this
      have h2 := (List.append_eq_nil_iff.mp h').1
      exact ha (List.append_eq_nil_iff.mp h2).1
  exact fpMaskCase (.fpNeg d1 d2) d1 d2 .sseXor (.psllqImm (d1 % 8) 63)
    (fun v => psllqLanes v 63) (BitVec.ofNat 128 (2 ^ 127 + 2 ^ 63))
    (BitVec.ofNat 64 (2 ^ 63)) (holFp64Negate (s1.fpRegs d2))
    s1 s2 ms h hd1 hd2 hne henc hlen1 hdecShift hshift htouchShift
    psllqLanes_allOnes_63 (by decide) (maskApply_neg (s1.fpRegs d2)).symm
    hs2pc hs2mem hs2dom hs2regs hs2fp

end Flapjack.Compiler.Encoders.X64
