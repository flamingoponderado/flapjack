import Flapjack.Compiler.Encoders.X64.Machine.DivCase

/-!
# The `addOverflow`, `subOverflow` and `addCarry` cases of `encoder_correct x64Target`

`arith (addOverflow r1 r2 r3 r4)` lowers to `add r1, r2`, then `mov r3, 0` and
`seto r3`.  `asm_ok` forces `r1 = r2`, so the instruction's destination operand
is the source's `readReg r2` value and the source's `readReg r3` is the
instruction's source; the sum `w2 + w3` lands in `r1`, and the signed-overflow
flag of the addition is exactly the source's `if (w2 + w3).toInt ≠ ...`.
`subOverflow` is the same sequence with `sub`.

`arith (addCarry r1 r2 r3 r4)` lowers to `cmp r4, 1`; `cmc`; `adc r1, r3`;
`mov r4, 0`; `setc r4`.  `asm_ok` forces `r1 = r2`, so `adc` adds the source's
`readReg r2` (the destination's old value) to `readReg r3`; `cmp r4, 1` sets
`CF` exactly when `r4 = 0`, `cmc` flips it into the carry-in bit
`(if readReg r4 = 0 then 0 else 1)`, `adc`'s `CF` is the source's carry-out
`2^64 ≤ r`, and the final `setc` writes that carry into the zeroed `r4`.

Each case is the `CaseGoal` of `encoder_correct x64Target` reduced through
`encoderCaseStep` to the interference-free run of `x64Next` (`n` steps for an
`n + 1`-instruction lowering), as in `Machine/MulCase.lean` and
`Machine/DivCase.lean`.  The intermediate states are named definitions below so
that each run step is a consequence of the corresponding decoder lemma.

This is Flapjack infrastructure: it is a case of the single HOL theorem
`x64_encoder_correct`
(`cakeml/compiler/encoders/x64/proofs/x64_targetProofScript.sml`), whose
`Inst`/`Arith` branch has no per-case declaration of its own.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Byte offsets and byte-list splitting -/

/-- Two byte offsets compose. -/
theorem x64AddOffset (a : BitVec 64) (m n : Nat) :
    (a + BitVec.ofNat 64 m) + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- Splitting three instructions' bytes off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_three (pc : BitVec 64) (l1 l2 l3 : List (BitVec 8))
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc (l1 ++ l2 ++ l3) m dm ↔
      bytesInMemoryHOL pc l1 m dm ∧
      bytesInMemoryHOL (pc + BitVec.ofNat 64 l1.length) l2 m dm ∧
      bytesInMemoryHOL ((pc + BitVec.ofNat 64 l1.length) + BitVec.ofNat 64 l2.length) l3 m dm := by
  rw [bytesInMemory_append, bytesInMemory_append, and_assoc]
  simp only [List.length_append, BitVec.ofNat_add, BitVec.add_assoc]

/-- Splitting five instructions' bytes off a `bytesInMemoryHOL` fact. -/
theorem bytesInMemory_five (pc : BitVec 64) (l1 l2 l3 l4 l5 : List (BitVec 8))
    (m : BitVec 64 → BitVec 8) (dm : BitVec 64 → Prop) :
    bytesInMemoryHOL pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) m dm ↔
      bytesInMemoryHOL pc l1 m dm ∧
      bytesInMemoryHOL (pc + BitVec.ofNat 64 l1.length) l2 m dm ∧
      bytesInMemoryHOL ((pc + BitVec.ofNat 64 l1.length) + BitVec.ofNat 64 l2.length) l3 m dm ∧
      bytesInMemoryHOL (((pc + BitVec.ofNat 64 l1.length) + BitVec.ofNat 64 l2.length) +
        BitVec.ofNat 64 l3.length) l4 m dm ∧
      bytesInMemoryHOL ((((pc + BitVec.ofNat 64 l1.length) + BitVec.ofNat 64 l2.length) +
        BitVec.ofNat 64 l3.length) + BitVec.ofNat 64 l4.length) l5 m dm := by
  rw [bytesInMemory_append, bytesInMemory_append, bytesInMemory_append, bytesInMemory_append,
    and_assoc, and_assoc, and_assoc]
  simp only [List.length_append, BitVec.ofNat_add, BitVec.add_assoc]

/-! ## A run of `n + 1` instructions -/

/-- A `CaseGoal` for a lowering of `n + 1` instructions from its
interference-free run `t`, whose `k`-th state sits at byte offset `offs k`. -/
theorem x64RunCase (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State) (n : Nat)
    (t : Nat → X64State) (offs : Nat → Nat)
    (h : asmStep x64Config s1 i s2 ∧ targetStateRel x64Target s1 ms)
    (hlen : (x64Target.config.encode i).length = offs (n + 1))
    (ht0 : t 0 = ms)
    (hstep : ∀ k, k ≤ n → x64Next (t k) = t (k + 1))
    (hstate : ∀ k, 1 ≤ k → k ≤ n → x64StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧ (t k).pc = ms.pc + BitVec.ofNat 64 (offs k))
    (hoff : ∀ k, k ≤ n → offs k < offs (n + 1))
    (hsafe : ∀ k, k ≤ n → StepSafe s1.memDomain (t k))
    (hs2dom : s2.memDomain = s1.memDomain)
    (hq : targetStateRel x64Target s2 (t (n + 1))) :
    CaseGoal i s1 s2 ms := by
  have st := x64Start i s1 s2 ms h
  have hcode : allPcs (x64Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have hit : ∀ k, k ≤ n + 1 → x64Next^[k] ms = t k := by
    intro k hk
    induction k with
    | zero => rw [Function.iterate_zero]; exact ht0.symm
    | succ m ih => rw [Function.iterate_succ_apply', ih (by omega), hstep m (by omega)]
  refine encoderCaseStep i s1 s2 ms n hs2dom hcode ?_ ?_ ?_
  · intro k hk
    rw [hit k (by omega)]
    exact hsafe k hk
  · intro k h1 h2
    obtain ⟨hok, hmem, hpc⟩ := hstate k h1 h2
    rw [hit k (by omega)]
    refine ⟨hok, ?_, ?_⟩
    · intro pc _
      exact hmem pc
    · rw [hpc, st.pc, hlen, allPcs_eq]
      refine ⟨offs k, ?_, ?_⟩
      · simpa [x64Target_config, x64Config] using hoff k h2
      · simp [x64Target_config, x64Config]
  · rw [hit (n + 1) (by omega)]
    exact hq

/-! ## `asm_ok` shapes -/

/-- `asm_ok` of an `addOverflow` fixes the destination/left pair and checks the
four registers. -/
theorem addOverflow_ok (d rc sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.addOverflow d rc sl sr))) x64Config = true) :
    d = rc ∧ asmRegOkExact d x64Config = true ∧ asmRegOkExact rc x64Config = true ∧
      asmRegOkExact sl x64Config = true ∧ asmRegOkExact sr x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config, Bool.and_eq_true,
    Bool.or_eq_true] at h
  simp at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## Encoding lengths -/

/-- A register-register 64-bit arithmetic instruction is three bytes. -/
theorem binopRR_z64_length (op : ZBinopName) (dst src : Nat) (hop : op.code < 8) :
    (encodeInsn (.binopRR op .z64 dst src)).length = 3 :=
  encodeInsn_binopRR_length op dst src (by intro _ hs; omega)

/-- The `mov r32, 0` immediate move's length. -/
def mov32Len (dst : Nat) : Nat := 5 + (if 8 ≤ dst then 1 else 0)

theorem mov32Len_ge (dst : Nat) : 5 ≤ mov32Len dst := by
  unfold mov32Len; split <;> omega

/-- A conditional set is four bytes. -/
theorem setcc_length (cond : ZCond) (dst : Nat) (hd : dst < 16) (hc : cond ≠ .zAlways) :
    (encodeInsn (.setcc cond true dst)).length = 4 := by
  cases cond <;> first | exact absurd rfl hc | (interval_cases dst <;> decide)

/-! ## Model steps -/

/-- The closed model executes `add`. -/
theorem execInsn_binopRR_zadd (dst src : Nat) (len : Nat) (s : X64State) :
    execInsn (.binopRR .zadd .z64 dst src) len s =
      { (writeRegSized .z64 dst (readReg s dst + readReg s src) s) with
        flags := addFlags (readReg s dst) (readReg s src) } := rfl

/-- One `x64Next` step over `add`. -/
theorem x64Next_binopRR_zadd (ms : X64State) (dm : BitVec 64 → Prop) (dst src : Nat)
    (hdst : dst < 16) (hsrc : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR .zadd .z64 dst src)) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms dst (readReg ms dst + readReg ms src)) with
      flags := addFlags (readReg ms dst) (readReg ms src),
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zadd .z64 dst src)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zadd .z64 dst src, (encodeInsn (.binopRR .zadd .z64 dst src)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem dm _ _ hbm
      (decode_binopRR_z64 .zadd dst src hdst hsrc (by decide)) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn_binopRR_zadd,
    writeRegSized, writeReg]

/-- One `x64Next` step over a `mov r32, 0`. -/
theorem x64Next_mov32_zero (ms : X64State) (dm : BitVec 64 → Prop) (r : Nat)
    (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRI .z32 r 0)) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r 0) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 r 0)).length } :=
  x64Next_const_mov32 ms dm r 0 hr (by decide) hbm hfailed

/-- One `x64Next` step over a conditional set. -/
theorem x64Next_setcc (ms : X64State) (dm : BitVec 64 → Prop) (cond : ZCond) (dst : Nat)
    (hd : dst < 16) (hc : cond ≠ .zAlways)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.setcc cond true dst)) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeRegSized (.z8 true) dst
        (if evalCond cond ms.flags then 1 else 0) ms with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.setcc cond true dst)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.setcc cond true dst, (encodeInsn (.setcc cond true dst)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem dm _ _ hbm (decode_setcc cond dst hd hc) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn]

/-! ## Register effects of the source semantics -/

/-- The register update of an `addOverflow`: the flag register wins over the
destination, as `updReg` nests the sum write inside the flag write. -/
theorem arithUpd_addOverflow_regs (s : AsmState 64) (d rc sl sr : Nat) :
    ∀ j, (arithUpd (.addOverflow d rc sl sr) s).regs j =
      (if j = sr then
        (if (s.regs rc + s.regs sl).toInt ≠ (s.regs rc).toInt + (s.regs sl).toInt then
          (1 : BitVec 64) else 0)
       else if j = d then s.regs rc + s.regs sl else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = sr
  · simp only [if_pos h4]
    simp
  · simp only [if_neg h4]

/-! ## The `addOverflow` lowering -/

/-- The `addOverflow` encoding is the `add`/`mov`/`seto` sequence. -/
theorem x64Enc_addOverflow (d rc sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.addOverflow d rc sl sr))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.addOverflow d rc sl sr))) =
      encodeInsn (.binopRR .zadd .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr) := by
  obtain ⟨-, hdok, -, hslok, hsrok⟩ := addOverflow_ok d rc sl sr h
  have hd : d < 16 := jumpReg_reg_lt d hdok
  have hsl : sl < 16 := jumpReg_reg_lt sl hslok
  have hsr : sr < 16 := jumpReg_reg_lt sr hsrok
  have hdst : totalNum2Zreg d = d := totalNum2Zreg_eq d hd
  have hslz : totalNum2Zreg sl = sl := totalNum2Zreg_eq sl hsl
  have hsrz : totalNum2Zreg sr = sr := totalNum2Zreg_eq sr hsr
  have hflat : (x64Ast (.inst (.arith (.addOverflow d rc sl sr)))).flatMap encodeInsn =
      [.binopRR .zadd .z64 d sl, .movRI .z32 sr 0, .setcc .zO true sr].flatMap encodeInsn := by
    simp only [x64Ast, x64Inst, hdst, hslz, hsrz]
  have hlen1 : (encodeInsn (.binopRR .zadd .z64 d sl)).length = 3 :=
    binopRR_z64_length .zadd d sl (by decide)
  have hlen2 : (encodeInsn (.movRI .z32 sr 0)).length = mov32Len sr :=
    movRI_z32_length sr hsr 0 (by decide) (by decide)
  have hlen3 : (encodeInsn (.setcc .zO true sr)).length = 4 := setcc_length .zO sr hsr (by decide)
  have hne : ([.binopRR .zadd .z64 d sl, .movRI .z32 sr 0, .setcc .zO true sr].flatMap
      encodeInsn) ≠ [] := by
    intro hnil
    have hpos : 0 < ([.binopRR .zadd .z64 d sl, .movRI .z32 sr 0,
        .setcc .zO true sr].flatMap encodeInsn).length := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        hlen1, hlen2, hlen3]
      have := mov32Len_ge sr
      omega
    rw [hnil] at hpos
    simp at hpos
  show x64Enc (.inst (.arith (.addOverflow d rc sl sr))) =
    encodeInsn (.binopRR .zadd .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
      encodeInsn (.setcc .zO true sr)
  rw [x64Enc_of_flatMap _ _ hflat hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
/-- The state after the flag-setting `add` of the `addOverflow` lowering. -/
def ovfAddT1 (ms : X64State) (d sl : Nat) : X64State :=
  { (writeReg ms d (readReg ms d + readReg ms sl)) with
    flags := addFlags (readReg ms d) (readReg ms sl),
    pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zadd .z64 d sl)).length }

/-- The state after zeroing the overflow register. -/
def ovfAddT2 (ms : X64State) (d sl sr : Nat) : X64State :=
  { (writeReg (ovfAddT1 ms d sl) sr 0) with
    pc := (ovfAddT1 ms d sl).pc +
      BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length }

/-- The state after the conditional set of the overflow register. -/
def ovfAddT3 (ms : X64State) (d sl sr : Nat) : X64State :=
  { writeRegSized (.z8 true) sr
      (if evalCond .zO (ovfAddT2 ms d sl sr).flags then 1 else 0)
      (ovfAddT2 ms d sl sr) with
    pc := (ovfAddT2 ms d sl sr).pc +
      BitVec.ofNat 64 (encodeInsn (.setcc .zO true sr)).length }

/-- Reading the zeroed overflow register after a conditional byte write. -/
theorem readReg_writeRegSized_z8_self (s : X64State) (r : Nat) (v : BitVec 64) (hr : r < 16)
    (hold : readReg s r = 0) (hv : v = 0 ∨ v = 1) :
    readReg (writeRegSized (.z8 true) r v s) r = v := by
  have hreg : s.regs r = 0 := by
    simpa [readReg, num2Zreg, Nat.mod_eq_of_lt hr] using hold
  rcases hv with rfl | rfl
  · simp only [readReg, writeRegSized, num2Zreg, Nat.mod_eq_of_lt hr, writeReg, hreg]
    decide
  · simp only [readReg, writeRegSized, num2Zreg, Nat.mod_eq_of_lt hr, writeReg, hreg]
    decide

/-- Reading another register after a conditional byte write. -/
theorem readReg_writeRegSized_z8_other (s : X64State) (r x : Nat) (v : BitVec 64)
    (hr : r < 16) (hx : x < 16) (hne : x ≠ r) :
    readReg (writeRegSized (.z8 true) r v s) x = readReg s x := by
  simp only [readReg, writeRegSized, num2Zreg, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hx,
    writeReg]
  rw [if_neg hne]

/-- The `addOverflow` constructor of `encoder_correct x64Target`: the
`add`/`mov`/`seto` sequence writes the sum and its signed-overflow flag. -/
theorem case_addOverflow (d rc sl sr : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.addOverflow d rc sl sr))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.addOverflow d rc sl sr))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.addOverflow d rc sl sr))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hdrc, hdok, hrcok, hslok, hsrok⟩ := addOverflow_ok d rc sl sr hok
  have hd : d < 16 := jumpReg_reg_lt d hdok
  have hrcl : rc < 16 := jumpReg_reg_lt rc hrcok
  have hsl : sl < 16 := jumpReg_reg_lt sl hslok
  have hsr : sr < 16 := jumpReg_reg_lt sr hsrok
  have hregd := regOk_of_asmRegOk d hdok
  have hregrc := regOk_of_asmRegOk rc hrcok
  have hregsl := regOk_of_asmRegOk sl hslok
  have hregsr := regOk_of_asmRegOk sr hsrok
  have henc : x64Target.config.encode (.inst (.arith (.addOverflow d rc sl sr))) =
      encodeInsn (.binopRR .zadd .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr) := x64Enc_addOverflow d rc sl sr hok
  have hlen1 : (encodeInsn (.binopRR .zadd .z64 d sl)).length = 3 :=
    binopRR_z64_length .zadd d sl (by decide)
  have hlen2 : (encodeInsn (.movRI .z32 sr 0)).length = mov32Len sr :=
    movRI_z32_length sr hsr 0 (by decide) (by decide)
  have hlen3 : (encodeInsn (.setcc .zO true sr)).length = 4 := setcc_length .zO sr hsr (by decide)
  -- the source post-state
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4) := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [henc, List.length_append, List.length_append, hlen1, hlen2, hlen3]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2regs : ∀ x, s2.regs x =
      (if x = sr then
        (if (s1.regs rc + s1.regs sl).toInt ≠ (s1.regs rc).toInt + (s1.regs sl).toInt then
          (1 : BitVec 64) else 0)
       else if x = d then s1.regs rc + s1.regs sl else s1.regs x) := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_addOverflow_regs s1 d rc sl sr x
  -- the encoded bytes, split per instruction
  have hb : bytesInMemoryHOL ms.pc
      (encodeInsn (.binopRR .zadd .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr)) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb1, hb2, hb3⟩ :=
    (bytesInMemory_three ms.pc _ _ _ ms.mem s1.memDomain).1 hb
  -- the interference-free run
  let t : Nat → X64State := fun k =>
    match k with
    | 0 => ms
    | 1 => ovfAddT1 ms d sl
    | 2 => ovfAddT2 ms d sl sr
    | _ => ovfAddT3 ms d sl sr
  let offs : Nat → Nat := fun k =>
    match k with
    | 0 => 0
    | 1 => 3
    | 2 => 3 + mov32Len sr
    | _ => 3 + mov32Len sr + 4
  have hpc1 : (ovfAddT1 ms d sl).pc = ms.pc + BitVec.ofNat 64 3 := by
    show ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zadd .z64 d sl)).length =
      ms.pc + BitVec.ofNat 64 3
    rw [hlen1]
  have hpc2 : (ovfAddT2 ms d sl sr).pc = ms.pc + BitVec.ofNat 64 (3 + mov32Len sr) := by
    show (ovfAddT1 ms d sl).pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr)
    rw [hpc1, hlen2]
    exact x64AddOffset ms.pc 3 (mov32Len sr)
  have hpc3 : (ovfAddT3 ms d sl sr).pc =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4) := by
    show (ovfAddT2 ms d sl sr).pc + BitVec.ofNat 64 (encodeInsn (.setcc .zO true sr)).length =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4)
    rw [hpc2, hlen3]
    exact x64AddOffset ms.pc (3 + mov32Len sr) 4
  have hbm1 : bytesInMemoryHOL (t 0).pc (encodeInsn (.binopRR .zadd .z64 d sl)) (t 0).mem
      s1.memDomain := hb1
  have hbm2 : bytesInMemoryHOL (t 1).pc (encodeInsn (.movRI .z32 sr 0)) (t 1).mem
      s1.memDomain := by
    show bytesInMemoryHOL (ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zadd .z64 d sl)).length)
      (encodeInsn (.movRI .z32 sr 0)) ms.mem s1.memDomain
    exact hb2
  have hbm3 : bytesInMemoryHOL (t 2).pc (encodeInsn (.setcc .zO true sr)) (t 2).mem
      s1.memDomain := by
    show bytesInMemoryHOL ((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR .zadd .z64 d sl)).length) +
        BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length)
      (encodeInsn (.setcc .zO true sr)) ms.mem s1.memDomain
    exact hb3
  have hdec1 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zadd .z64 d sl, (encodeInsn (.binopRR .zadd .z64 d sl)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm1
      (decode_binopRR_z64 .zadd d sl hd hsl (by decide)) (by omega)
  have hdec2 : decode (fun k => (t 1).mem ((t 1).pc + BitVec.ofNat 64 k)) =
      some (.movRI .z32 sr 0, mov32Len sr) :=
    decode_bytesInMemory _ _ _ s1.memDomain _ _ hbm2
      (decode_movRI_z32 sr hsr 0 (by decide) (by decide)) (by rw [hlen2])
  have hdec3 : decode (fun k => (t 2).mem ((t 2).pc + BitVec.ofNat 64 k)) =
      some (.setcc .zO true sr, 4) := by
    have hd := decode_setcc .zO sr hsr (by decide)
    rw [hlen3] at hd
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hbm3 hd (by rw [hlen3])
  have hstep1 : x64Next (t 0) = t 1 := by
    rw [show t 0 = ms from rfl]
    exact x64Next_binopRR_zadd ms s1.memDomain d sl hd hsl hbm1 st.failed
  have hstep2 : x64Next (t 1) = t 2 := by
    rw [show t 1 = ovfAddT1 ms d sl from rfl]
    exact x64Next_mov32_zero (ovfAddT1 ms d sl) s1.memDomain sr hsr hbm2 (by
      show (ovfAddT1 ms d sl).failed = false
      simp only [ovfAddT1, writeReg, st.failed])
  have hstep3 : x64Next (t 2) = t 3 := by
    rw [show t 2 = ovfAddT2 ms d sl sr from rfl]
    exact x64Next_setcc (ovfAddT2 ms d sl sr) s1.memDomain .zO sr hsr (by decide) hbm3 (by
      show (ovfAddT2 ms d sl sr).failed = false
      simp only [ovfAddT2, ovfAddT1, writeReg, st.failed])
  have hstate : ∀ k, 1 ≤ k → k ≤ 2 → x64StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧ (t k).pc = ms.pc + BitVec.ofNat 64 (offs k) := by
    intro k h1 h2
    interval_cases k
    · rw [show t 1 = ovfAddT1 ms d sl from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, ovfAddT1, writeReg, st.failed, Bool.not_false]
      · intro x
        show (ovfAddT1 ms d sl).mem x = ms.mem x
        simp only [ovfAddT1, writeReg]
      · show (ovfAddT1 ms d sl).pc = ms.pc + BitVec.ofNat 64 (offs 1)
        rw [hpc1]
        rfl
    · rw [show t 2 = ovfAddT2 ms d sl sr from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, ovfAddT2, ovfAddT1, writeReg, st.failed, Bool.not_false]
      · intro x
        show (ovfAddT2 ms d sl sr).mem x = ms.mem x
        simp only [ovfAddT2, ovfAddT1, writeReg]
      · show (ovfAddT2 ms d sl sr).pc = ms.pc + BitVec.ofNat 64 (offs 2)
        rw [hpc2]
        rfl
  have hoff : ∀ k, k ≤ 2 → offs k < offs 3 := by
    intro k hk
    interval_cases k
    · show 0 < 3 + mov32Len sr + 4
      have := mov32Len_ge sr
      omega
    · show 3 < 3 + mov32Len sr + 4
      have := mov32Len_ge sr
      omega
    · show 3 + mov32Len sr < 3 + mov32Len sr + 4
      omega
  have hsafe : ∀ k, k ≤ 2 → StepSafe s1.memDomain (t k) := by
    intro k hk
    interval_cases k
    · rw [show t 0 = ms from rfl]
      refine ⟨.binopRR .zadd .z64 d sl, _, hdec1, ?_, ?_⟩
      · intro j hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm1 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 1 = ovfAddT1 ms d sl from rfl]
      refine ⟨.movRI .z32 sr 0, mov32Len sr, hdec2, ?_, ?_⟩
      · intro j hj
        rw [← hlen2] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm2 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 2 = ovfAddT2 ms d sl sr from rfl]
      refine ⟨.setcc .zO true sr, 4, hdec3, ?_, ?_⟩
      · intro j hj
        rw [← hlen3] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm3 j hj
      · intro a ha
        simp [x64Touched] at ha
  have hq : targetStateRel x64Target s2 (t 3) := by
    rw [show t 3 = ovfAddT3 ms d sl sr from rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, ovfAddT3, ovfAddT2, ovfAddT1, writeRegSized,
        writeReg, st.failed, Bool.not_false]
    · show (ovfAddT3 ms d sl sr).pc = s2.pc
      rw [hpc3, hs2pc, st.pc]
    · intro a ha
      show (ovfAddT3 ms d sl sr).mem a = s2.mem a
      rw [hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      have hx16 : x < 16 := by
        simpa [x64Target_config, x64Config] using hx.1
      have hdread : readReg ms d = s1.regs rc := by
        simpa [hdrc] using st.reg d hregd
      have hslread : readReg ms sl = s1.regs sl := st.reg sl hregsl
      show readReg (ovfAddT3 ms d sl sr) x = s2.regs x
      have hold : readReg (ovfAddT2 ms d sl sr) sr = 0 := by
        show readReg (writeReg (ovfAddT1 ms d sl) sr 0) sr = 0
        rw [readReg_writeReg _ sr _ sr hsr hsr]
        simp
      have hv : (if evalCond .zO (ovfAddT2 ms d sl sr).flags then (1 : BitVec 64) else
          (0 : BitVec 64)) = 0 ∨
          (if evalCond .zO (ovfAddT2 ms d sl sr).flags then (1 : BitVec 64) else
            (0 : BitVec 64)) = 1 := by
        by_cases hc : evalCond .zO (ovfAddT2 ms d sl sr).flags
        · right; simp [hc]
        · left; simp [hc]
      have hself := readReg_writeRegSized_z8_self (ovfAddT2 ms d sl sr) sr _ hsr hold hv
      have hval : (if evalCond .zO (ovfAddT2 ms d sl sr).flags then 1 else 0) =
          (if ((s1.regs rc + s1.regs sl).toInt ≠
            (s1.regs rc).toInt + (s1.regs sl).toInt) then (1 : BitVec 64) else 0) := by
        simp only [evalCond, ovfAddT2, ovfAddT1, writeReg, addFlags, hdread, hslread,
          decide_eq_true_eq]
      have ht3 : readReg (ovfAddT3 ms d sl sr) x =
          readReg (writeRegSized (.z8 true) sr
            (if evalCond .zO (ovfAddT2 ms d sl sr).flags then 1 else 0)
            (ovfAddT2 ms d sl sr)) x := rfl
      rw [ht3]
      by_cases hxsr : x = sr
      · rw [hxsr, hself, hs2regs sr, hval]
        simp
      · have hother : readReg (writeRegSized (.z8 true) sr
            (if evalCond .zO (ovfAddT2 ms d sl sr).flags then 1 else 0)
            (ovfAddT2 ms d sl sr)) x =
            readReg (ovfAddT2 ms d sl sr) x :=
          readReg_writeRegSized_z8_other (ovfAddT2 ms d sl sr) sr x
            (if evalCond .zO (ovfAddT2 ms d sl sr).flags then 1 else 0) hsr hx16 hxsr
        rw [hother]
        show readReg (writeReg (ovfAddT1 ms d sl) sr 0) x = s2.regs x
        rw [readReg_writeReg (ovfAddT1 ms d sl) sr 0 x hsr hx16, if_neg hxsr]
        by_cases hxd : x = d
        · have hdsr : d ≠ sr := by rw [← hxd]; exact hxsr
          rw [hxd]
          show readReg (writeReg ms d (readReg ms d + readReg ms sl)) d = s2.regs d
          rw [readReg_writeReg ms d (readReg ms d + readReg ms sl) d hd hd]
          rw [hs2regs d]
          simp only [if_neg hdsr]
          rw [hdread, hslread]
          simp
        · show readReg (writeReg ms d (readReg ms d + readReg ms sl)) x = s2.regs x
          rw [readReg_writeReg ms d (readReg ms d + readReg ms sl) x hd hx16, if_neg hxd]
          rw [hs2regs x]
          simp only [if_neg hxsr, if_neg hxd]
          exact st.reg x hx
    · intro x hx
      show readXmm (ovfAddT3 ms d sl sr) x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x (by simpa [x64Target_config, x64Config] using hx)
  exact x64RunCase _ s1 s2 ms 2 t offs h
    (by
      show (x64Target.config.encode (.inst (.arith (.addOverflow d rc sl sr)))).length =
        offs 3
      rw [henc, List.length_append, List.length_append, hlen1, hlen2, hlen3]
      rfl)
    (by rfl)
    (by
      intro k hk
      interval_cases k
      · exact hstep1
      · exact hstep2
      · exact hstep3)
    hstate hoff hsafe hs2dom hq


theorem subOverflow_ok (d rc sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.subOverflow d rc sl sr))) x64Config = true) :
    d = rc ∧ asmRegOkExact d x64Config = true ∧ asmRegOkExact rc x64Config = true ∧
      asmRegOkExact sl x64Config = true ∧ asmRegOkExact sr x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config, Bool.and_eq_true,
    Bool.or_eq_true] at h
  simp at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## Encoding lengths -/


theorem execInsn_binopRR_zsub (dst src : Nat) (len : Nat) (s : X64State) :
    execInsn (.binopRR .zsub .z64 dst src) len s =
      { (writeRegSized .z64 dst (readReg s dst - readReg s src) s) with
        flags := subFlags (readReg s dst) (readReg s src) } := rfl

/-- One `x64Next` step over `add`. -/
theorem x64Next_binopRR_zsub (ms : X64State) (dm : BitVec 64 → Prop) (dst src : Nat)
    (hdst : dst < 16) (hsrc : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR .zsub .z64 dst src)) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms dst (readReg ms dst - readReg ms src)) with
      flags := subFlags (readReg ms dst) (readReg ms src),
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zsub .z64 dst src)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zsub .z64 dst src, (encodeInsn (.binopRR .zsub .z64 dst src)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem dm _ _ hbm
      (decode_binopRR_z64 .zsub dst src hdst hsrc (by decide)) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn_binopRR_zsub,
    writeRegSized, writeReg]

theorem arithUpd_subOverflow_regs (s : AsmState 64) (d rc sl sr : Nat) :
    ∀ j, (arithUpd (.subOverflow d rc sl sr) s).regs j =
      (if j = sr then
        (if (s.regs rc - s.regs sl).toInt ≠ (s.regs rc).toInt - (s.regs sl).toInt then
          (1 : BitVec 64) else 0)
       else if j = d then s.regs rc - s.regs sl else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = sr
  · simp only [if_pos h4]
    simp
  · simp only [if_neg h4]

/-! ## The `subOverflow` lowering -/


theorem x64Enc_subOverflow (d rc sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.subOverflow d rc sl sr))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.subOverflow d rc sl sr))) =
      encodeInsn (.binopRR .zsub .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr) := by
  obtain ⟨-, hdok, -, hslok, hsrok⟩ := subOverflow_ok d rc sl sr h
  have hd : d < 16 := jumpReg_reg_lt d hdok
  have hsl : sl < 16 := jumpReg_reg_lt sl hslok
  have hsr : sr < 16 := jumpReg_reg_lt sr hsrok
  have hdst : totalNum2Zreg d = d := totalNum2Zreg_eq d hd
  have hslz : totalNum2Zreg sl = sl := totalNum2Zreg_eq sl hsl
  have hsrz : totalNum2Zreg sr = sr := totalNum2Zreg_eq sr hsr
  have hflat : (x64Ast (.inst (.arith (.subOverflow d rc sl sr)))).flatMap encodeInsn =
      [.binopRR .zsub .z64 d sl, .movRI .z32 sr 0, .setcc .zO true sr].flatMap encodeInsn := by
    simp only [x64Ast, x64Inst, hdst, hslz, hsrz]
  have hlen1 : (encodeInsn (.binopRR .zsub .z64 d sl)).length = 3 :=
    binopRR_z64_length .zsub d sl (by decide)
  have hlen2 : (encodeInsn (.movRI .z32 sr 0)).length = mov32Len sr :=
    movRI_z32_length sr hsr 0 (by decide) (by decide)
  have hlen3 : (encodeInsn (.setcc .zO true sr)).length = 4 := setcc_length .zO sr hsr (by decide)
  have hne : ([.binopRR .zsub .z64 d sl, .movRI .z32 sr 0, .setcc .zO true sr].flatMap
      encodeInsn) ≠ [] := by
    intro hnil
    have hpos : 0 < ([.binopRR .zsub .z64 d sl, .movRI .z32 sr 0,
        .setcc .zO true sr].flatMap encodeInsn).length := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        hlen1, hlen2, hlen3]
      have := mov32Len_ge sr
      omega
    rw [hnil] at hpos
    simp at hpos
  show x64Enc (.inst (.arith (.subOverflow d rc sl sr))) =
    encodeInsn (.binopRR .zsub .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
      encodeInsn (.setcc .zO true sr)
  rw [x64Enc_of_flatMap _ _ hflat hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

def ovfSubT1 (ms : X64State) (d sl : Nat) : X64State :=
  { (writeReg ms d (readReg ms d - readReg ms sl)) with
    flags := subFlags (readReg ms d) (readReg ms sl),
    pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zsub .z64 d sl)).length }

/-- The state after zeroing the overflow register. -/
def ovfSubT2 (ms : X64State) (d sl sr : Nat) : X64State :=
  { (writeReg (ovfSubT1 ms d sl) sr 0) with
    pc := (ovfSubT1 ms d sl).pc +
      BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length }

/-- The state after the conditional set of the overflow register. -/
def ovfSubT3 (ms : X64State) (d sl sr : Nat) : X64State :=
  { writeRegSized (.z8 true) sr
      (if evalCond .zO (ovfSubT2 ms d sl sr).flags then 1 else 0)
      (ovfSubT2 ms d sl sr) with
    pc := (ovfSubT2 ms d sl sr).pc +
      BitVec.ofNat 64 (encodeInsn (.setcc .zO true sr)).length }


theorem case_subOverflow (d rc sl sr : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.subOverflow d rc sl sr))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.subOverflow d rc sl sr))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.subOverflow d rc sl sr))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hdrc, hdok, hrcok, hslok, hsrok⟩ := subOverflow_ok d rc sl sr hok
  have hd : d < 16 := jumpReg_reg_lt d hdok
  have hrcl : rc < 16 := jumpReg_reg_lt rc hrcok
  have hsl : sl < 16 := jumpReg_reg_lt sl hslok
  have hsr : sr < 16 := jumpReg_reg_lt sr hsrok
  have hregd := regOk_of_asmRegOk d hdok
  have hregrc := regOk_of_asmRegOk rc hrcok
  have hregsl := regOk_of_asmRegOk sl hslok
  have hregsr := regOk_of_asmRegOk sr hsrok
  have henc : x64Target.config.encode (.inst (.arith (.subOverflow d rc sl sr))) =
      encodeInsn (.binopRR .zsub .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr) := x64Enc_subOverflow d rc sl sr hok
  have hlen1 : (encodeInsn (.binopRR .zsub .z64 d sl)).length = 3 :=
    binopRR_z64_length .zsub d sl (by decide)
  have hlen2 : (encodeInsn (.movRI .z32 sr 0)).length = mov32Len sr :=
    movRI_z32_length sr hsr 0 (by decide) (by decide)
  have hlen3 : (encodeInsn (.setcc .zO true sr)).length = 4 := setcc_length .zO sr hsr (by decide)
  -- the source post-state
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4) := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [henc, List.length_append, List.length_append, hlen1, hlen2, hlen3]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, arithUpd, updReg]
  have hs2regs : ∀ x, s2.regs x =
      (if x = sr then
        (if (s1.regs rc - s1.regs sl).toInt ≠ (s1.regs rc).toInt - (s1.regs sl).toInt then
          (1 : BitVec 64) else 0)
       else if x = d then s1.regs rc - s1.regs sl else s1.regs x) := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_subOverflow_regs s1 d rc sl sr x
  -- the encoded bytes, split per instruction
  have hb : bytesInMemoryHOL ms.pc
      (encodeInsn (.binopRR .zsub .z64 d sl) ++ encodeInsn (.movRI .z32 sr 0) ++
        encodeInsn (.setcc .zO true sr)) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb1, hb2, hb3⟩ :=
    (bytesInMemory_three ms.pc _ _ _ ms.mem s1.memDomain).1 hb
  -- the interference-free run
  let t : Nat → X64State := fun k =>
    match k with
    | 0 => ms
    | 1 => ovfSubT1 ms d sl
    | 2 => ovfSubT2 ms d sl sr
    | _ => ovfSubT3 ms d sl sr
  let offs : Nat → Nat := fun k =>
    match k with
    | 0 => 0
    | 1 => 3
    | 2 => 3 + mov32Len sr
    | _ => 3 + mov32Len sr + 4
  have hpc1 : (ovfSubT1 ms d sl).pc = ms.pc + BitVec.ofNat 64 3 := by
    show ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zsub .z64 d sl)).length =
      ms.pc + BitVec.ofNat 64 3
    rw [hlen1]
  have hpc2 : (ovfSubT2 ms d sl sr).pc = ms.pc + BitVec.ofNat 64 (3 + mov32Len sr) := by
    show (ovfSubT1 ms d sl).pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr)
    rw [hpc1, hlen2]
    exact x64AddOffset ms.pc 3 (mov32Len sr)
  have hpc3 : (ovfSubT3 ms d sl sr).pc =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4) := by
    show (ovfSubT2 ms d sl sr).pc + BitVec.ofNat 64 (encodeInsn (.setcc .zO true sr)).length =
      ms.pc + BitVec.ofNat 64 (3 + mov32Len sr + 4)
    rw [hpc2, hlen3]
    exact x64AddOffset ms.pc (3 + mov32Len sr) 4
  have hbm1 : bytesInMemoryHOL (t 0).pc (encodeInsn (.binopRR .zsub .z64 d sl)) (t 0).mem
      s1.memDomain := hb1
  have hbm2 : bytesInMemoryHOL (t 1).pc (encodeInsn (.movRI .z32 sr 0)) (t 1).mem
      s1.memDomain := by
    show bytesInMemoryHOL (ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zsub .z64 d sl)).length)
      (encodeInsn (.movRI .z32 sr 0)) ms.mem s1.memDomain
    exact hb2
  have hbm3 : bytesInMemoryHOL (t 2).pc (encodeInsn (.setcc .zO true sr)) (t 2).mem
      s1.memDomain := by
    show bytesInMemoryHOL ((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR .zsub .z64 d sl)).length) +
        BitVec.ofNat 64 (encodeInsn (.movRI .z32 sr 0)).length)
      (encodeInsn (.setcc .zO true sr)) ms.mem s1.memDomain
    exact hb3
  have hdec1 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zsub .z64 d sl, (encodeInsn (.binopRR .zsub .z64 d sl)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbm1
      (decode_binopRR_z64 .zsub d sl hd hsl (by decide)) (by omega)
  have hdec2 : decode (fun k => (t 1).mem ((t 1).pc + BitVec.ofNat 64 k)) =
      some (.movRI .z32 sr 0, mov32Len sr) :=
    decode_bytesInMemory _ _ _ s1.memDomain _ _ hbm2
      (decode_movRI_z32 sr hsr 0 (by decide) (by decide)) (by rw [hlen2])
  have hdec3 : decode (fun k => (t 2).mem ((t 2).pc + BitVec.ofNat 64 k)) =
      some (.setcc .zO true sr, 4) := by
    have hd := decode_setcc .zO sr hsr (by decide)
    rw [hlen3] at hd
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hbm3 hd (by rw [hlen3])
  have hstep1 : x64Next (t 0) = t 1 := by
    rw [show t 0 = ms from rfl]
    exact x64Next_binopRR_zsub ms s1.memDomain d sl hd hsl hbm1 st.failed
  have hstep2 : x64Next (t 1) = t 2 := by
    rw [show t 1 = ovfSubT1 ms d sl from rfl]
    exact x64Next_mov32_zero (ovfSubT1 ms d sl) s1.memDomain sr hsr hbm2 (by
      show (ovfSubT1 ms d sl).failed = false
      simp only [ovfSubT1, writeReg, st.failed])
  have hstep3 : x64Next (t 2) = t 3 := by
    rw [show t 2 = ovfSubT2 ms d sl sr from rfl]
    exact x64Next_setcc (ovfSubT2 ms d sl sr) s1.memDomain .zO sr hsr (by decide) hbm3 (by
      show (ovfSubT2 ms d sl sr).failed = false
      simp only [ovfSubT2, ovfSubT1, writeReg, st.failed])
  have hstate : ∀ k, 1 ≤ k → k ≤ 2 → x64StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧ (t k).pc = ms.pc + BitVec.ofNat 64 (offs k) := by
    intro k h1 h2
    interval_cases k
    · rw [show t 1 = ovfSubT1 ms d sl from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, ovfSubT1, writeReg, st.failed, Bool.not_false]
      · intro x
        show (ovfSubT1 ms d sl).mem x = ms.mem x
        simp only [ovfSubT1, writeReg]
      · show (ovfSubT1 ms d sl).pc = ms.pc + BitVec.ofNat 64 (offs 1)
        rw [hpc1]
        rfl
    · rw [show t 2 = ovfSubT2 ms d sl sr from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, ovfSubT2, ovfSubT1, writeReg, st.failed, Bool.not_false]
      · intro x
        show (ovfSubT2 ms d sl sr).mem x = ms.mem x
        simp only [ovfSubT2, ovfSubT1, writeReg]
      · show (ovfSubT2 ms d sl sr).pc = ms.pc + BitVec.ofNat 64 (offs 2)
        rw [hpc2]
        rfl
  have hoff : ∀ k, k ≤ 2 → offs k < offs 3 := by
    intro k hk
    interval_cases k
    · show 0 < 3 + mov32Len sr + 4
      have := mov32Len_ge sr
      omega
    · show 3 < 3 + mov32Len sr + 4
      have := mov32Len_ge sr
      omega
    · show 3 + mov32Len sr < 3 + mov32Len sr + 4
      omega
  have hsafe : ∀ k, k ≤ 2 → StepSafe s1.memDomain (t k) := by
    intro k hk
    interval_cases k
    · rw [show t 0 = ms from rfl]
      refine ⟨.binopRR .zsub .z64 d sl, _, hdec1, ?_, ?_⟩
      · intro j hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm1 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 1 = ovfSubT1 ms d sl from rfl]
      refine ⟨.movRI .z32 sr 0, mov32Len sr, hdec2, ?_, ?_⟩
      · intro j hj
        rw [← hlen2] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm2 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 2 = ovfSubT2 ms d sl sr from rfl]
      refine ⟨.setcc .zO true sr, 4, hdec3, ?_, ?_⟩
      · intro j hj
        rw [← hlen3] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hbm3 j hj
      · intro a ha
        simp [x64Touched] at ha
  have hq : targetStateRel x64Target s2 (t 3) := by
    rw [show t 3 = ovfSubT3 ms d sl sr from rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, ovfSubT3, ovfSubT2, ovfSubT1, writeRegSized,
        writeReg, st.failed, Bool.not_false]
    · show (ovfSubT3 ms d sl sr).pc = s2.pc
      rw [hpc3, hs2pc, st.pc]
    · intro a ha
      show (ovfSubT3 ms d sl sr).mem a = s2.mem a
      rw [hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      have hx16 : x < 16 := by
        simpa [x64Target_config, x64Config] using hx.1
      have hdread : readReg ms d = s1.regs rc := by
        simpa [hdrc] using st.reg d hregd
      have hslread : readReg ms sl = s1.regs sl := st.reg sl hregsl
      show readReg (ovfSubT3 ms d sl sr) x = s2.regs x
      have hold : readReg (ovfSubT2 ms d sl sr) sr = 0 := by
        show readReg (writeReg (ovfSubT1 ms d sl) sr 0) sr = 0
        rw [readReg_writeReg _ sr _ sr hsr hsr]
        simp
      have hv : (if evalCond .zO (ovfSubT2 ms d sl sr).flags then (1 : BitVec 64) else
          (0 : BitVec 64)) = 0 ∨
          (if evalCond .zO (ovfSubT2 ms d sl sr).flags then (1 : BitVec 64) else
            (0 : BitVec 64)) = 1 := by
        by_cases hc : evalCond .zO (ovfSubT2 ms d sl sr).flags
        · right; simp [hc]
        · left; simp [hc]
      have hself := readReg_writeRegSized_z8_self (ovfSubT2 ms d sl sr) sr _ hsr hold hv
      have hval : (if evalCond .zO (ovfSubT2 ms d sl sr).flags then 1 else 0) =
          (if ((s1.regs rc - s1.regs sl).toInt ≠
            (s1.regs rc).toInt - (s1.regs sl).toInt) then (1 : BitVec 64) else 0) := by
        simp only [evalCond, ovfSubT2, ovfSubT1, writeReg, subFlags, hdread, hslread,
          decide_eq_true_eq]
      have ht3 : readReg (ovfSubT3 ms d sl sr) x =
          readReg (writeRegSized (.z8 true) sr
            (if evalCond .zO (ovfSubT2 ms d sl sr).flags then 1 else 0)
            (ovfSubT2 ms d sl sr)) x := rfl
      rw [ht3]
      by_cases hxsr : x = sr
      · rw [hxsr, hself, hs2regs sr, hval]
        simp
      · have hother : readReg (writeRegSized (.z8 true) sr
            (if evalCond .zO (ovfSubT2 ms d sl sr).flags then 1 else 0)
            (ovfSubT2 ms d sl sr)) x =
            readReg (ovfSubT2 ms d sl sr) x :=
          readReg_writeRegSized_z8_other (ovfSubT2 ms d sl sr) sr x
            (if evalCond .zO (ovfSubT2 ms d sl sr).flags then 1 else 0) hsr hx16 hxsr
        rw [hother]
        show readReg (writeReg (ovfSubT1 ms d sl) sr 0) x = s2.regs x
        rw [readReg_writeReg (ovfSubT1 ms d sl) sr 0 x hsr hx16, if_neg hxsr]
        by_cases hxd : x = d
        · have hdsr : d ≠ sr := by rw [← hxd]; exact hxsr
          rw [hxd]
          show readReg (writeReg ms d (readReg ms d - readReg ms sl)) d = s2.regs d
          rw [readReg_writeReg ms d (readReg ms d - readReg ms sl) d hd hd]
          rw [hs2regs d]
          simp only [if_neg hdsr]
          rw [hdread, hslread]
          simp
        · show readReg (writeReg ms d (readReg ms d - readReg ms sl)) x = s2.regs x
          rw [readReg_writeReg ms d (readReg ms d - readReg ms sl) x hd hx16, if_neg hxd]
          rw [hs2regs x]
          simp only [if_neg hxsr, if_neg hxd]
          exact st.reg x hx
    · intro x hx
      show readXmm (ovfSubT3 ms d sl sr) x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x (by simpa [x64Target_config, x64Config] using hx)
  exact x64RunCase _ s1 s2 ms 2 t offs h
    (by
      show (x64Target.config.encode (.inst (.arith (.subOverflow d rc sl sr)))).length =
        offs 3
      rw [henc, List.length_append, List.length_append, hlen1, hlen2, hlen3]
      rfl)
    (by rfl)
    (by
      intro k hk
      interval_cases k
      · exact hstep1
      · exact hstep2
      · exact hstep3)
    hstate hoff hsafe hs2dom hq


end Flapjack.Compiler.Encoders.X64
