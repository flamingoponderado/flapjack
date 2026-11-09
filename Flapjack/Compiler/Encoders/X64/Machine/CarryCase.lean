module

public import Flapjack.Compiler.Encoders.X64.Machine.DivCase

@[expose] public section

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
/-! ## The `addCarry` lowering -/

/-- `asm_ok` of an `addCarry` fixes the destination/result pair and checks the
four registers. -/
theorem addCarry_ok (d rs sl sr : Nat)
    (h : asmOkExact (.inst (.arith (.addCarry d rs sl sr))) x64Config = true) :
    d = rs ∧ asmRegOkExact d x64Config = true ∧ asmRegOkExact rs x64Config = true ∧
      asmRegOkExact sl x64Config = true ∧ asmRegOkExact sr x64Config = true := by
  simp only [asmOkExact, asmInstOkExact, asmArithOkExact, x64Config, Bool.and_eq_true,
    Bool.or_eq_true] at h
  simp at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ### Model steps and flag facts -/

/-- The closed model executes a 64-bit `cmp` by setting the subtraction flags
only. -/
theorem execInsn_binopRI_zcmp (dst : Nat) (imm : BitVec 64) (len : Nat) (s : X64State) :
    execInsn (.binopRI .zcmp .z64 dst imm) len s =
      { s with flags := subFlags (readReg s dst) imm } := rfl

/-- One `x64Next` step over a 64-bit `cmp`. -/
theorem x64Next_binopRI_zcmp (ms : X64State) (_dm : BitVec 64 → Prop) (dst : Nat)
    (imm : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRI .zcmp .z64 dst imm, len))
    (hlen : (encodeInsn (.binopRI .zcmp .z64 dst imm)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with
      flags := subFlags (readReg ms dst) imm,
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRI .zcmp .z64 dst imm)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec,
    execInsn_binopRI_zcmp]

/-- The closed model executes `cmc` by flipping the carry flag. -/
theorem execInsn_cmc (len : Nat) (s : X64State) :
    execInsn .cmc len s = { s with flags := { s.flags with cf := !s.flags.cf } } := rfl

/-- One `x64Next` step over `cmc`. -/
theorem x64Next_cmc (ms : X64State) (dm : BitVec 64 → Prop)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn .cmc) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { ms with
      flags := { ms.flags with cf := !ms.flags.cf },
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn .cmc).length } := by
  have hlen : (encodeInsn .cmc).length = 1 := by simp [encodeInsn]
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) = some (.cmc, 1) :=
    decode_bytesInMemory _ ms.pc ms.mem dm _ _ hbm decode_cmc (by rw [hlen])
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn_cmc]

/-- The closed model executes `adc`, adding the incoming carry flag. -/
theorem execInsn_binopRR_zadc (dst src : Nat) (len : Nat) (s : X64State) :
    execInsn (.binopRR .zadc .z64 dst src) len s =
      { (writeReg s dst (readReg s dst + readReg s src +
          BitVec.ofNat 64 (if s.flags.cf then 1 else 0))) with
        flags := adcFlags (readReg s dst) (readReg s src) s.flags.cf } := rfl

/-- One `x64Next` step over `adc`. -/
theorem x64Next_binopRR_zadc (ms : X64State) (dm : BitVec 64 → Prop) (dst src : Nat)
    (hdst : dst < 16) (hsrc : src < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR .zadc .z64 dst src)) ms.mem dm)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms dst (readReg ms dst + readReg ms src +
        BitVec.ofNat 64 (if ms.flags.cf then 1 else 0))) with
      flags := adcFlags (readReg ms dst) (readReg ms src) ms.flags.cf,
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zadc .z64 dst src)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zadc .z64 dst src, (encodeInsn (.binopRR .zadc .z64 dst src)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem dm _ _ hbm
      (decode_binopRR_z64 .zadc dst src hdst hsrc (by decide)) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn_binopRR_zadc]

/-! ### The source semantics of `addCarry` -/

/-- The register update of an `addCarry`: the carry register wins over the
destination, as `updReg` nests the sum write inside the carry write. -/
theorem arithUpd_addCarry_regs (s : AsmState 64) (r1 r2 r3 r4 : Nat) :
    ∀ j, (arithUpd (.addCarry r1 r2 r3 r4) s).regs j =
      (if j = r4 then
        (if 2 ^ 64 ≤ (s.regs r2).toNat + (s.regs r3).toNat +
          (if s.regs r4 = 0 then 0 else 1) then (1 : BitVec 64) else 0)
       else if j = r1 then
        BitVec.ofNat 64 ((s.regs r2).toNat + (s.regs r3).toNat +
          (if s.regs r4 = 0 then 0 else 1))
       else s.regs j) := by
  intro j
  simp only [arithUpd, updReg, Flapjack.Compiler.Encoders.AsmSem.readReg]
  by_cases h4 : j = r4
  · simp only [if_pos h4]
    rfl
  · simp only [if_neg h4]
    rfl

/-! ### BitVec and flag bridging facts -/

/-- Adding a natural carry is the natural-number sum modulo `2^64`. -/
theorem ofNat_add_carry (a b : BitVec 64) (c : Nat) :
    a + b + BitVec.ofNat 64 c = BitVec.ofNat 64 (a.toNat + b.toNat + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `cmp r, 1` leaves `CF` set exactly when `r = 0`. -/
theorem subFlags_cf_one (a : BitVec 64) : (subFlags a 1).cf = decide (a = 0) := by
  have h1 : ((1 : BitVec 64)).toNat = 1 := by decide
  by_cases h : a = 0
  · subst h; simp [subFlags]
  · have hpos : a.toNat ≠ 0 := by
      intro hz
      exact h (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
    have hlt : ¬ a.toNat < 1 := by omega
    simp only [subFlags, h1]
    rw [show decide (a.toNat < 1) = false by simp [hlt]]
    exact (decide_eq_false_iff_not.mpr h).symm

/-- After `cmp r, 1; cmc`, the carry-in bit is `1` exactly when `r ≠ 0`. -/
theorem carryIn_eq (a : BitVec 64) :
    (if !(subFlags a 1).cf then (1 : Nat) else 0) = (if a = 0 then 0 else 1) := by
  rw [subFlags_cf_one]
  by_cases h : a = 0 <;> simp [h]

/-! ### The `addCarry` lowering -/

/-- The `addCarry` encoding is the `cmp`/`cmc`/`adc`/`mov`/`setc` sequence. -/
theorem x64Enc_addCarry (r1 r2 r3 r4 : Nat)
    (h : asmOkExact (.inst (.arith (.addCarry r1 r2 r3 r4))) x64Config = true) :
    x64Target.config.encode (.inst (.arith (.addCarry r1 r2 r3 r4))) =
      encodeInsn (.binopRI .zcmp .z64 r4 1) ++ encodeInsn .cmc ++
        encodeInsn (.binopRR .zadc .z64 r1 r3) ++ encodeInsn (.movRI .z32 r4 0) ++
        encodeInsn (.setcc .zB true r4) := by
  obtain ⟨hr12, hr1ok, hrok, hr3ok, hr4ok⟩ := addCarry_ok r1 r2 r3 r4 h
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hr3 : r3 < 16 := jumpReg_reg_lt r3 hr3ok
  have hr4 : r4 < 16 := jumpReg_reg_lt r4 hr4ok
  have hz1 : totalNum2Zreg r1 = r1 := totalNum2Zreg_eq r1 hr1
  have hz3 : totalNum2Zreg r3 = r3 := totalNum2Zreg_eq r3 hr3
  have hz4 : totalNum2Zreg r4 = r4 := totalNum2Zreg_eq r4 hr4
  have hflat : (x64Ast (.inst (.arith (.addCarry r1 r2 r3 r4)))).flatMap encodeInsn =
      [.binopRI .zcmp .z64 r4 1, .cmc, .binopRR .zadc .z64 r1 r3,
        .movRI .z32 r4 0, .setcc .zB true r4].flatMap encodeInsn := by
    simp only [x64Ast, x64Inst, hz1, hz3, hz4]
  have hlen1 : (encodeInsn (.binopRI .zcmp .z64 r4 1)).length = 4 := by
    have hs : -128 ≤ (1 : BitVec 64).toInt ∧ (1 : BitVec 64).toInt ≤ 127 := by decide
    rw [encodeInsn_binopRI_83 .zcmp r4 hr4 1 (by decide) (by decide) hs]
    simp [binopRI83Bytes]
  have hlen2 : (encodeInsn .cmc).length = 1 := by simp [encodeInsn]
  have hlen3 : (encodeInsn (.binopRR .zadc .z64 r1 r3)).length = 3 :=
    binopRR_z64_length .zadc r1 r3 (by decide)
  have hlen4 : (encodeInsn (.movRI .z32 r4 0)).length = mov32Len r4 :=
    movRI_z32_length r4 hr4 0 (by decide) (by decide)
  have hlen5 : (encodeInsn (.setcc .zB true r4)).length = 4 := setcc_length .zB r4 hr4 (by decide)
  have hne : ([.binopRI .zcmp .z64 r4 1, .cmc, .binopRR .zadc .z64 r1 r3,
      .movRI .z32 r4 0, .setcc .zB true r4].flatMap encodeInsn) ≠ [] := by
    intro hnil
    have hpos : 0 < ([.binopRI .zcmp .z64 r4 1, .cmc, .binopRR .zadc .z64 r1 r3,
        .movRI .z32 r4 0, .setcc .zB true r4].flatMap encodeInsn).length := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        hlen1, hlen2, hlen3, hlen4, hlen5]
      have := mov32Len_ge r4
      omega
    rw [hnil] at hpos
    simp at hpos
  show x64Enc (.inst (.arith (.addCarry r1 r2 r3 r4))) =
    encodeInsn (.binopRI .zcmp .z64 r4 1) ++ encodeInsn .cmc ++
      encodeInsn (.binopRR .zadc .z64 r1 r3) ++ encodeInsn (.movRI .z32 r4 0) ++
      encodeInsn (.setcc .zB true r4)
  rw [x64Enc_of_flatMap _ _ hflat hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The state after the `cmp r4, 1` of the `addCarry` lowering. -/
def carryT1 (ms : X64State) (r4 : Nat) : X64State :=
  { ms with
    flags := subFlags (readReg ms r4) 1,
    pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRI .zcmp .z64 r4 1)).length }

/-- The state after the `cmc` of the `addCarry` lowering. -/
def carryT2 (ms : X64State) (r4 : Nat) : X64State :=
  { (carryT1 ms r4) with
    flags := { (carryT1 ms r4).flags with cf := !(carryT1 ms r4).flags.cf },
    pc := (carryT1 ms r4).pc + BitVec.ofNat 64 (encodeInsn .cmc).length }

/-- The state after the `adc r1, r3` of the `addCarry` lowering. -/
def carryT3 (ms : X64State) (r1 r3 r4 : Nat) : X64State :=
  { (writeReg (carryT2 ms r4) r1
      (readReg (carryT2 ms r4) r1 + readReg (carryT2 ms r4) r3 +
        BitVec.ofNat 64 (if (carryT2 ms r4).flags.cf then 1 else 0))) with
    flags := adcFlags (readReg (carryT2 ms r4) r1) (readReg (carryT2 ms r4) r3)
      (carryT2 ms r4).flags.cf,
    pc := (carryT2 ms r4).pc + BitVec.ofNat 64
      (encodeInsn (.binopRR .zadc .z64 r1 r3)).length }

/-- The state after zeroing the carry register. -/
def carryT4 (ms : X64State) (r1 r3 r4 : Nat) : X64State :=
  { (writeReg (carryT3 ms r1 r3 r4) r4 0) with
    pc := (carryT3 ms r1 r3 r4).pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 r4 0)).length }

/-- The state after the conditional set of the carry register. -/
def carryT5 (ms : X64State) (r1 r3 r4 : Nat) : X64State :=
  { writeRegSized (.z8 true) r4
      (if evalCond .zB (carryT4 ms r1 r3 r4).flags then 1 else 0)
      (carryT4 ms r1 r3 r4) with
    pc := (carryT4 ms r1 r3 r4).pc + BitVec.ofNat 64 (encodeInsn (.setcc .zB true r4)).length }

/-- The `addCarry` constructor of `encoder_correct x64Target`: the
`cmp`/`cmc`/`adc`/`mov`/`setc` sequence writes the sum and its carry-out. -/
theorem case_addCarry (r1 r2 r3 r4 : Nat) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.arith (.addCarry r1 r2 r3 r4))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.arith (.addCarry r1 r2 r3 r4))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.arith (.addCarry r1 r2 r3 r4))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hr12, hr1ok, hrok, hr3ok, hr4ok⟩ := addCarry_ok r1 r2 r3 r4 hok
  have hr1 : r1 < 16 := jumpReg_reg_lt r1 hr1ok
  have hr3 : r3 < 16 := jumpReg_reg_lt r3 hr3ok
  have hr4 : r4 < 16 := jumpReg_reg_lt r4 hr4ok
  have hreg1 := regOk_of_asmRegOk r1 hr1ok
  have hreg3 := regOk_of_asmRegOk r3 hr3ok
  have hreg4 := regOk_of_asmRegOk r4 hr4ok
  have henc : x64Target.config.encode (.inst (.arith (.addCarry r1 r2 r3 r4))) =
      encodeInsn (.binopRI .zcmp .z64 r4 1) ++ encodeInsn .cmc ++
        encodeInsn (.binopRR .zadc .z64 r1 r3) ++ encodeInsn (.movRI .z32 r4 0) ++
        encodeInsn (.setcc .zB true r4) := x64Enc_addCarry r1 r2 r3 r4 hok
  have hlen1 : (encodeInsn (.binopRI .zcmp .z64 r4 1)).length = 4 := by
    have hs : -128 ≤ (1 : BitVec 64).toInt ∧ (1 : BitVec 64).toInt ≤ 127 := by decide
    rw [encodeInsn_binopRI_83 .zcmp r4 hr4 1 (by decide) (by decide) hs]
    simp [binopRI83Bytes]
  have hlen2 : (encodeInsn .cmc).length = 1 := by simp [encodeInsn]
  have hlen3 : (encodeInsn (.binopRR .zadc .z64 r1 r3)).length = 3 :=
    binopRR_z64_length .zadc r1 r3 (by decide)
  have hlen4 : (encodeInsn (.movRI .z32 r4 0)).length = mov32Len r4 :=
    movRI_z32_length r4 hr4 0 (by decide) (by decide)
  have hlen5 : (encodeInsn (.setcc .zB true r4)).length = 4 := setcc_length .zB r4 hr4 (by decide)
  -- the source post-state
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (4 + 1 + 3 + mov32Len r4 + 4) := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [henc, List.length_append, List.length_append, List.length_append, List.length_append,
      hlen1, hlen2, hlen3, hlen4, hlen5]
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
      (if x = r4 then
        (if 2 ^ 64 ≤ (s1.regs r2).toNat + (s1.regs r3).toNat +
          (if s1.regs r4 = 0 then 0 else 1) then (1 : BitVec 64) else 0)
       else if x = r1 then
        BitVec.ofNat 64 ((s1.regs r2).toNat + (s1.regs r3).toNat +
          (if s1.regs r4 = 0 then 0 else 1))
       else s1.regs x) := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    exact arithUpd_addCarry_regs s1 r1 r2 r3 r4 x
  -- the encoded bytes, split per instruction
  have hb : bytesInMemoryHOL ms.pc
      (encodeInsn (.binopRI .zcmp .z64 r4 1) ++ encodeInsn .cmc ++
        encodeInsn (.binopRR .zadc .z64 r1 r3) ++ encodeInsn (.movRI .z32 r4 0) ++
        encodeInsn (.setcc .zB true r4)) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
    (bytesInMemory_five ms.pc _ _ _ _ _ ms.mem s1.memDomain).1 hb
  -- the interference-free run
  let t : Nat → X64State := fun k =>
    match k with
    | 0 => ms
    | 1 => carryT1 ms r4
    | 2 => carryT2 ms r4
    | 3 => carryT3 ms r1 r3 r4
    | 4 => carryT4 ms r1 r3 r4
    | _ => carryT5 ms r1 r3 r4
  let offs : Nat → Nat := fun k =>
    match k with
    | 0 => 0
    | 1 => 4
    | 2 => 5
    | 3 => 8
    | 4 => 8 + mov32Len r4
    | _ => 8 + mov32Len r4 + 4
  have hpc1 : (carryT1 ms r4).pc = ms.pc + BitVec.ofNat 64 4 := by
    show ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRI .zcmp .z64 r4 1)).length =
      ms.pc + BitVec.ofNat 64 4
    rw [hlen1]
  have hpc2 : (carryT2 ms r4).pc = ms.pc + BitVec.ofNat 64 5 := by
    show (carryT1 ms r4).pc + BitVec.ofNat 64 (encodeInsn .cmc).length =
      ms.pc + BitVec.ofNat 64 5
    rw [hpc1, hlen2]
    exact x64AddOffset ms.pc 4 1
  have hpc3 : (carryT3 ms r1 r3 r4).pc = ms.pc + BitVec.ofNat 64 8 := by
    show (carryT2 ms r4).pc + BitVec.ofNat 64
        (encodeInsn (.binopRR .zadc .z64 r1 r3)).length = ms.pc + BitVec.ofNat 64 8
    rw [hpc2, hlen3]
    exact x64AddOffset ms.pc 5 3
  have hpc4 : (carryT4 ms r1 r3 r4).pc = ms.pc + BitVec.ofNat 64 (8 + mov32Len r4) := by
    show (carryT3 ms r1 r3 r4).pc + BitVec.ofNat 64
        (encodeInsn (.movRI .z32 r4 0)).length = ms.pc + BitVec.ofNat 64 (8 + mov32Len r4)
    rw [hpc3, hlen4]
    exact x64AddOffset ms.pc 8 (mov32Len r4)
  have hpc5 : (carryT5 ms r1 r3 r4).pc = ms.pc + BitVec.ofNat 64 (8 + mov32Len r4 + 4) := by
    show (carryT4 ms r1 r3 r4).pc + BitVec.ofNat 64
        (encodeInsn (.setcc .zB true r4)).length = ms.pc + BitVec.ofNat 64 (8 + mov32Len r4 + 4)
    rw [hpc4, hlen5]
    exact x64AddOffset ms.pc (8 + mov32Len r4) 4
  have hs1 : -128 ≤ (1 : BitVec 64).toInt ∧ (1 : BitVec 64).toInt ≤ 127 := by decide
  have hdec1 : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRI .zcmp .z64 r4 1, 4) :=
    decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hb1
      (decode_binopRI_83 .zcmp r4 hr4 1 (by decide) (by decide) hs1) (by rw [hlen1])
  have hdec2 : decode (fun k => (t 1).mem ((t 1).pc + BitVec.ofNat 64 k)) =
      some (.cmc, 1) := by
    show decode (fun k => ms.mem ((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI .zcmp .z64 r4 1)).length) + BitVec.ofNat 64 k)) = some (.cmc, 1)
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hb2 decode_cmc (by rw [hlen2])
  have hdec3 : decode (fun k => (t 2).mem ((t 2).pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zadc .z64 r1 r3, (encodeInsn (.binopRR .zadc .z64 r1 r3)).length) := by
    show decode (fun k => ms.mem (((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI .zcmp .z64 r4 1)).length) + BitVec.ofNat 64
        (encodeInsn .cmc).length) + BitVec.ofNat 64 k)) =
      some (.binopRR .zadc .z64 r1 r3, (encodeInsn (.binopRR .zadc .z64 r1 r3)).length)
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hb3
      (decode_binopRR_z64 .zadc r1 r3 hr1 hr3 (by decide)) (by omega)
  have hdec4 : decode (fun k => (t 3).mem ((t 3).pc + BitVec.ofNat 64 k)) =
      some (.movRI .z32 r4 0, mov32Len r4) := by
    show decode (fun k => ms.mem ((((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI .zcmp .z64 r4 1)).length) + BitVec.ofNat 64
        (encodeInsn .cmc).length) + BitVec.ofNat 64
        (encodeInsn (.binopRR .zadc .z64 r1 r3)).length) + BitVec.ofNat 64 k)) =
      some (.movRI .z32 r4 0, mov32Len r4)
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hb4
      (decode_movRI_z32 r4 hr4 0 (by decide) (by decide)) (by rw [hlen4])
  have hdec5 : decode (fun k => (t 4).mem ((t 4).pc + BitVec.ofNat 64 k)) =
      some (.setcc .zB true r4, 4) := by
    show decode (fun k => ms.mem (((((ms.pc + BitVec.ofNat 64
        (encodeInsn (.binopRI .zcmp .z64 r4 1)).length) + BitVec.ofNat 64
        (encodeInsn .cmc).length) + BitVec.ofNat 64
        (encodeInsn (.binopRR .zadc .z64 r1 r3)).length) + BitVec.ofNat 64
        (encodeInsn (.movRI .z32 r4 0)).length) + BitVec.ofNat 64 k)) =
      some (.setcc .zB true r4, 4)
    have hd := decode_setcc .zB r4 hr4 (by decide)
    rw [hlen5] at hd
    exact decode_bytesInMemory _ _ _ s1.memDomain _ _ hb5 hd (by rw [hlen5])
  have hstep1 : x64Next (t 0) = t 1 := by
    rw [show t 0 = ms from rfl]
    exact x64Next_binopRI_zcmp ms s1.memDomain r4 1 4 hdec1 (by rw [hlen1]) st.failed
  have hstep2 : x64Next (t 1) = t 2 := by
    rw [show t 1 = carryT1 ms r4 from rfl]
    exact x64Next_cmc (carryT1 ms r4) s1.memDomain hb2 (by
      show (carryT1 ms r4).failed = false
      simp only [carryT1, st.failed])
  have hstep3 : x64Next (t 2) = t 3 := by
    rw [show t 2 = carryT2 ms r4 from rfl]
    exact x64Next_binopRR_zadc (carryT2 ms r4) s1.memDomain r1 r3 hr1 hr3 hb3 (by
      show (carryT2 ms r4).failed = false
      simp only [carryT2, carryT1, st.failed])
  have hstep4 : x64Next (t 3) = t 4 := by
    rw [show t 3 = carryT3 ms r1 r3 r4 from rfl]
    exact x64Next_mov32_zero (carryT3 ms r1 r3 r4) s1.memDomain r4 hr4 hb4 (by
      show (carryT3 ms r1 r3 r4).failed = false
      simp only [carryT3, carryT2, carryT1, writeReg, st.failed])
  have hstep5 : x64Next (t 4) = t 5 := by
    rw [show t 4 = carryT4 ms r1 r3 r4 from rfl]
    exact x64Next_setcc (carryT4 ms r1 r3 r4) s1.memDomain .zB r4 hr4 (by decide) hb5 (by
      show (carryT4 ms r1 r3 r4).failed = false
      simp only [carryT4, carryT3, carryT2, carryT1, writeReg, st.failed])
  have hstate : ∀ k, 1 ≤ k → k ≤ 4 → x64StateOk (t k) = true ∧
      (∀ x, (t k).mem x = ms.mem x) ∧ (t k).pc = ms.pc + BitVec.ofNat 64 (offs k) := by
    intro k h1 h2
    interval_cases k
    · rw [show t 1 = carryT1 ms r4 from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, carryT1, st.failed, Bool.not_false]
      · intro x
        show (carryT1 ms r4).mem x = ms.mem x
        simp only [carryT1]
      · show (carryT1 ms r4).pc = ms.pc + BitVec.ofNat 64 (offs 1)
        rw [hpc1]
        rfl
    · rw [show t 2 = carryT2 ms r4 from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, carryT2, carryT1, st.failed, Bool.not_false]
      · intro x
        show (carryT2 ms r4).mem x = ms.mem x
        simp only [carryT2, carryT1]
      · show (carryT2 ms r4).pc = ms.pc + BitVec.ofNat 64 (offs 2)
        rw [hpc2]
        rfl
    · rw [show t 3 = carryT3 ms r1 r3 r4 from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, carryT3, carryT2, carryT1, writeReg, st.failed, Bool.not_false]
      · intro x
        show (carryT3 ms r1 r3 r4).mem x = ms.mem x
        simp only [carryT3, carryT2, carryT1, writeReg]
      · show (carryT3 ms r1 r3 r4).pc = ms.pc + BitVec.ofNat 64 (offs 3)
        rw [hpc3]
        rfl
    · rw [show t 4 = carryT4 ms r1 r3 r4 from rfl]
      refine ⟨?_, ?_, ?_⟩
      · simp only [x64StateOk, carryT4, carryT3, carryT2, carryT1, writeReg, st.failed,
          Bool.not_false]
      · intro x
        show (carryT4 ms r1 r3 r4).mem x = ms.mem x
        simp only [carryT4, carryT3, carryT2, carryT1, writeReg]
      · show (carryT4 ms r1 r3 r4).pc = ms.pc + BitVec.ofNat 64 (offs 4)
        rw [hpc4]
        rfl
  have hoff : ∀ k, k ≤ 4 → offs k < offs 5 := by
    intro k hk
    interval_cases k
    · show 0 < 8 + mov32Len r4 + 4
      have := mov32Len_ge r4; omega
    · show 4 < 8 + mov32Len r4 + 4
      have := mov32Len_ge r4; omega
    · show 5 < 8 + mov32Len r4 + 4
      have := mov32Len_ge r4; omega
    · show 8 < 8 + mov32Len r4 + 4
      have := mov32Len_ge r4; omega
    · show 8 + mov32Len r4 < 8 + mov32Len r4 + 4
      omega
  have hsafe : ∀ k, k ≤ 4 → StepSafe s1.memDomain (t k) := by
    intro k hk
    interval_cases k
    · rw [show t 0 = ms from rfl]
      refine ⟨.binopRI .zcmp .z64 r4 1, 4, hdec1, ?_, ?_⟩
      · intro j hj
        rw [← hlen1] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hb1 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 1 = carryT1 ms r4 from rfl]
      refine ⟨.cmc, 1, hdec2, ?_, ?_⟩
      · intro j hj
        rw [← hlen2] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hb2 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 2 = carryT2 ms r4 from rfl]
      refine ⟨.binopRR .zadc .z64 r1 r3, _, hdec3, ?_, ?_⟩
      · intro j hj
        exact bytesInMemoryHOL_domain _ _ _ _ hb3 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 3 = carryT3 ms r1 r3 r4 from rfl]
      refine ⟨.movRI .z32 r4 0, mov32Len r4, hdec4, ?_, ?_⟩
      · intro j hj
        rw [← hlen4] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hb4 j hj
      · intro a ha
        simp [x64Touched] at ha
    · rw [show t 4 = carryT4 ms r1 r3 r4 from rfl]
      refine ⟨.setcc .zB true r4, 4, hdec5, ?_, ?_⟩
      · intro j hj
        rw [← hlen5] at hj
        exact bytesInMemoryHOL_domain _ _ _ _ hb5 j hj
      · intro a ha
        simp [x64Touched] at ha
  have hq : targetStateRel x64Target s2 (t 5) := by
    rw [show t 5 = carryT5 ms r1 r3 r4 from rfl]
    have hdread1 : readReg ms r1 = s1.regs r1 := st.reg r1 hreg1
    have hdread2 : readReg ms r1 = s1.regs r2 := by rw [hdread1, hr12]
    have hr3read : readReg ms r3 = s1.regs r3 := st.reg r3 hreg3
    have hr4read : readReg ms r4 = s1.regs r4 := st.reg r4 hreg4
    have hreadT2 : ∀ r, readReg (carryT2 ms r4) r = readReg ms r := fun r => rfl
    have hadcval : readReg (carryT3 ms r1 r3 r4) r1 =
        BitVec.ofNat 64 ((s1.regs r2).toNat + (s1.regs r3).toNat +
          (if s1.regs r4 = 0 then 0 else 1)) := by
      have hc := carryIn_eq (readReg ms r4)
      rw [show readReg (carryT3 ms r1 r3 r4) r1 =
          readReg (writeReg (carryT2 ms r4) r1
            (readReg (carryT2 ms r4) r1 + readReg (carryT2 ms r4) r3 +
              BitVec.ofNat 64 (if (carryT2 ms r4).flags.cf then 1 else 0))) r1 from rfl]
      rw [readReg_writeReg (carryT2 ms r4) r1 _ r1 hr1 hr1, if_pos rfl]
      rw [hreadT2 r1, hreadT2 r3]
      rw [show (carryT2 ms r4).flags.cf = !(subFlags (readReg ms r4) 1).cf from rfl]
      rw [hdread2, hr3read, hc, hr4read]
      exact ofNat_add_carry (s1.regs r2) (s1.regs r3) _
    have hval : (if evalCond .zB (carryT4 ms r1 r3 r4).flags then (1 : BitVec 64) else 0) =
        (if 2 ^ 64 ≤ (s1.regs r2).toNat + (s1.regs r3).toNat +
          (if s1.regs r4 = 0 then 0 else 1) then (1 : BitVec 64) else 0) := by
      have hc := carryIn_eq (readReg ms r4)
      have hcf : (carryT4 ms r1 r3 r4).flags.cf =
          decide (2 ^ 64 ≤ (readReg ms r1).toNat + (readReg ms r3).toNat +
            (if !(subFlags (readReg ms r4) 1).cf then 1 else 0)) := by
        show (adcFlags (readReg (carryT2 ms r4) r1) (readReg (carryT2 ms r4) r3)
            (carryT2 ms r4).flags.cf).cf = _
        rw [hreadT2 r1, hreadT2 r3,
          show (carryT2 ms r4).flags.cf = !(subFlags (readReg ms r4) 1).cf from rfl]
        rfl
      show (if (carryT4 ms r1 r3 r4).flags.cf then (1 : BitVec 64) else 0) =
        (if 2 ^ 64 ≤ (s1.regs r2).toNat + (s1.regs r3).toNat +
          (if s1.regs r4 = 0 then 0 else 1) then (1 : BitVec 64) else 0)
      rw [hcf, hdread2, hr3read, hc, hr4read]
      simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, carryT5, carryT4, carryT3, carryT2, carryT1,
        writeRegSized, writeReg, st.failed, Bool.not_false]
    · show (carryT5 ms r1 r3 r4).pc = s2.pc
      rw [hpc5, hs2pc, st.pc]
    · intro a ha
      show (carryT5 ms r1 r3 r4).mem a = s2.mem a
      rw [hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      have hx16 : x < 16 := by
        simpa [x64Target_config, x64Config] using hx.1
      show readReg (carryT5 ms r1 r3 r4) x = s2.regs x
      have hold : readReg (carryT4 ms r1 r3 r4) r4 = 0 := by
        show readReg (writeReg (carryT3 ms r1 r3 r4) r4 0) r4 = 0
        rw [readReg_writeReg _ r4 _ r4 hr4 hr4]
        simp
      have hv : (if evalCond .zB (carryT4 ms r1 r3 r4).flags then (1 : BitVec 64) else
          (0 : BitVec 64)) = 0 ∨
          (if evalCond .zB (carryT4 ms r1 r3 r4).flags then (1 : BitVec 64) else
            (0 : BitVec 64)) = 1 := by
        by_cases hc : evalCond .zB (carryT4 ms r1 r3 r4).flags
        · right; simp [hc]
        · left; simp [hc]
      have hself := readReg_writeRegSized_z8_self (carryT4 ms r1 r3 r4) r4
        (if evalCond .zB (carryT4 ms r1 r3 r4).flags then 1 else 0) hr4 hold hv
      have ht5 : readReg (carryT5 ms r1 r3 r4) x =
          readReg (writeRegSized (.z8 true) r4
            (if evalCond .zB (carryT4 ms r1 r3 r4).flags then 1 else 0)
            (carryT4 ms r1 r3 r4)) x := rfl
      rw [ht5]
      by_cases hx4 : x = r4
      · rw [hx4, hself, hs2regs r4, hval]
        simp
      · have hother : readReg (writeRegSized (.z8 true) r4
            (if evalCond .zB (carryT4 ms r1 r3 r4).flags then 1 else 0)
            (carryT4 ms r1 r3 r4)) x =
            readReg (carryT4 ms r1 r3 r4) x :=
          readReg_writeRegSized_z8_other (carryT4 ms r1 r3 r4) r4 x
            (if evalCond .zB (carryT4 ms r1 r3 r4).flags then 1 else 0) hr4 hx16 hx4
        rw [hother]
        show readReg (writeReg (carryT3 ms r1 r3 r4) r4 0) x = s2.regs x
        rw [readReg_writeReg (carryT3 ms r1 r3 r4) r4 0 x hr4 hx16, if_neg hx4]
        by_cases hx1 : x = r1
        · have hr14 : ¬ r1 = r4 := by rw [← hx1]; exact hx4
          rw [hx1, hadcval, hs2regs r1]
          simp only [if_neg hr14]
          rfl
        · have h3 : readReg (carryT3 ms r1 r3 r4) x = readReg ms x := by
            rw [show readReg (carryT3 ms r1 r3 r4) x =
                readReg (writeReg (carryT2 ms r4) r1
                  (readReg (carryT2 ms r4) r1 + readReg (carryT2 ms r4) r3 +
                    BitVec.ofNat 64 (if (carryT2 ms r4).flags.cf then 1 else 0))) x from rfl]
            rw [readReg_writeReg (carryT2 ms r4) r1 _ x hr1 hx16, if_neg hx1]
            exact hreadT2 x
          rw [h3, hs2regs x]
          simp only [if_neg hx4, if_neg hx1]
          exact st.reg x hx
    · intro x hx
      show readXmm (carryT5 ms r1 r3 r4) x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x (by simpa [x64Target_config, x64Config] using hx)
  exact x64RunCase _ s1 s2 ms 4 t offs h
    (by
      show (x64Target.config.encode (.inst (.arith (.addCarry r1 r2 r3 r4)))).length =
        offs 5
      rw [henc, List.length_append, List.length_append, List.length_append, List.length_append,
        hlen1, hlen2, hlen3, hlen4, hlen5]
      rfl)
    (by rfl)
    (by
      intro k hk
      interval_cases k
      · exact hstep1
      · exact hstep2
      · exact hstep3
      · exact hstep4
      · exact hstep5)
    hstate hoff hsafe hs2dom hq

end Flapjack.Compiler.Encoders.X64
