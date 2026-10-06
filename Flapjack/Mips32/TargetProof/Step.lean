import Flapjack.Mips32.TargetProof.Simulate
import Flapjack.Misc.BytesInMemory

/-! # Straight-line runs

The machine code of an asm instruction sits in the source memory domain
(`asm_step`'s `bytes_in_memory`). A "plain" instruction advances `pc` by 4 without leaving
the sequential state, so `mips32Next` runs a sequence of them one instruction per step;
`straightCase` turns such a sequence into the corresponding constructor of
`encoder_correct`, leaving only the effect of the whole sequence to be related to the asm
post-state. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

/-- `prog` is encoded in memory `m` from `pc`, and its bytes lie in `d`. -/
def CodeIn (m : Mem) (d : W → Prop) (pc : W) : List Insn → Prop
  | [] => True
  | i :: is => m.readWord pc = encodeInsn i ∧ (∀ x ∈ wordAt pc, d x) ∧ CodeIn m d (pc + 4) is

theorem codeIn_of_bytes (d : W → Prop) (mem : W → BitVec 8) (m : Mem)
    (hm : ∀ a, d a → m.readByte a = mem a) :
    ∀ (prog : List Insn) (pc : W), bytesInMemoryHOL pc (prog.flatMap mips32Encode) mem d →
      CodeIn m d pc prog := by
  intro prog
  induction prog with
  | nil => intros; trivial
  | cons i is ih =>
    intro pc hb
    rw [List.flatMap_cons, bytesInMemory_append] at hb
    obtain ⟨hi, hrest⟩ := hb
    simp only [mips32Encode, wordBytes, bytesInMemoryHOL] at hi
    obtain ⟨h0, d0, h1, d1, h2, d2, h3, d3, -⟩ := hi
    have e2 : pc + 1 + 1 = pc + 2 := by bv_omega
    have e3 : pc + 1 + 1 + 1 = pc + 3 := by bv_omega
    rw [e2] at h2 d2; rw [e3] at h3 d3
    refine ⟨?_, ?_, ?_⟩
    · apply readWord_of_bytes
      · rw [hm _ d0, h0]
      · rw [hm _ d1, h1]
      · rw [hm _ d2, h2]
      · rw [hm _ d3, h3]
    · simp only [wordAt, List.mem_cons, List.mem_nil_iff, or_false]
      rintro x (rfl | rfl | rfl | rfl) <;> assumption
    · apply ih
      simpa [mips32Encode, wordBytes] using hrest

theorem codeIn_cons {m : Mem} {d : W → Prop} {pc : W} {i : Insn} {is : List Insn} :
    CodeIn m d pc (i :: is) ↔
      m.readWord pc = encodeInsn i ∧ (∀ x ∈ wordAt pc, d x) ∧ CodeIn m d (pc + 4) is := Iff.rfl

/-- An instruction that, from a sequential state, moves on to the next instruction and does
not stop the machine. -/
def Plain (i : Insn) : Prop :=
  ∀ s : State, s.nextPc = s.pc + 4 →
    (exec s i).pc = s.pc + 4 ∧ (exec s i).nextPc = s.pc + 8 ∧ (exec s i).trapped = s.trapped

/-- An instruction that does not write memory. -/
def NoWrite (i : Insn) : Prop := ∀ s : State, (exec s i).mem = s.mem

/-- The instructions that are neither branches, jumps nor traps. -/
def insnSequential : Insn → Bool
  | .beq .. | .bne .. | .bgez .. | .bgtz .. | .blez .. | .bltz .. | .bal .. | .j .. | .jal ..
  | .jr .. | .jalr .. | .teq .. => false
  | _ => true

/-- The instructions that write memory. -/
def insnWrites : Insn → Bool
  | .sb .. | .sh .. | .sw .. | .sc .. | .swl .. | .swr .. => true
  | _ => false

theorem setReg_pc (s : State) (r : Fin 32) (v : W) : (s.setReg r v).pc = s.pc := by
  unfold State.setReg; split <;> rfl
theorem setReg_nextPc (s : State) (r : Fin 32) (v : W) : (s.setReg r v).nextPc = s.nextPc := by
  unfold State.setReg; split <;> rfl
theorem setReg_trapped (s : State) (r : Fin 32) (v : W) : (s.setReg r v).trapped = s.trapped := by
  unfold State.setReg; split <;> rfl
theorem setReg_hi (s : State) (r : Fin 32) (v : W) : (s.setReg r v).hi = s.hi := by
  unfold State.setReg; split <;> rfl
theorem setReg_lo (s : State) (r : Fin 32) (v : W) : (s.setReg r v).lo = s.lo := by
  unfold State.setReg; split <;> rfl

@[simp] theorem reg_zero (s : State) : s.reg 0 = 0 := by simp [State.reg]

/-- A state built from another state's register file reads the same registers. -/
@[simp] theorem reg_mk_gpr (s : State) (pc nextPc hi lo : W) (mem : Mem) (trapped : Bool)
    (x : Fin 32) : (State.mk pc nextPc s.gpr hi lo mem trapped).reg x = s.reg x := rfl

@[simp] theorem reg_setReg (s : State) (r x : Fin 32) (v : W) :
    (s.setReg r v).reg x = if x = 0 then 0 else if x = r then v else s.reg x := by
  unfold State.setReg State.reg
  by_cases hr : r = 0
  · subst hr; by_cases hx : x = 0 <;> simp [hx]
  · by_cases hx : x = 0 <;> simp [hr, hx]

set_option maxHeartbeats 400000 in
theorem plain_of_sequential (i : Insn) (h : insnSequential i = true) : Plain i := by
  intro s hs
  cases i <;> simp [insnSequential] at h <;>
    simp only [exec, setReg_pc, setReg_nextPc, setReg_trapped, setHiLo] <;>
    (try split) <;> simp only [setReg_pc, setReg_nextPc, setReg_trapped, hs] <;>
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | bv_omega

theorem plain_bal_one : Plain (.bal 1) := by
  intro s hs
  simp only [exec, setReg_pc, setReg_nextPc, setReg_trapped]
  simp [hs, boff]
  bv_omega

set_option maxHeartbeats 400000 in
theorem noWrite_of_writes (i : Insn) (h : insnWrites i = false) : NoWrite i := by
  intro s
  cases i <;> simp [insnWrites] at h <;>
    simp only [exec, setReg_mem, setHiLo] <;> (try split) <;> simp only [setReg_mem]

theorem next_exec {s : State} {i : Insn} (ht : s.trapped = false)
    (hd : decode (s.mem.readWord s.pc) = some i) (ht' : (exec s i).trapped = false)
    (hn : (exec s i).nextPc = (exec s i).pc + 4) : mips32Next s = exec s i := by
  simp [mips32Next, fetchExec, ht, hd, ht', hn]

theorem next_exec_plain {s : State} {i : Insn} (hp : Plain i) (ht : s.trapped = false)
    (hn : s.nextPc = s.pc + 4) (hd : decode (s.mem.readWord s.pc) = some i) :
    mips32Next s = exec s i := by
  obtain ⟨h1, h2, h3⟩ := hp s hn
  exact next_exec ht hd (h3.trans ht) (by rw [h1, h2]; bv_omega)

/-- The run of a sequence of plain instructions, of which only the last may write memory. -/
theorem run_plain (d : W → Prop) :
    ∀ (prog : List Insn) (s : State), CodeIn s.mem d s.pc prog → s.nextPc = s.pc + 4 →
      s.trapped = false → (∀ i ∈ prog, Plain i ∧ decode (encodeInsn i) = some i) →
      (∀ i ∈ prog.dropLast, NoWrite i) →
      ∀ k ≤ prog.length, mips32Next^[k] s = (prog.take k).foldl exec s := by
  intro prog
  induction prog with
  | nil => intro s _ _ _ _ _ k hk; simp at hk; subst hk; rfl
  | cons i is ih =>
    intro s hc hn ht hp hw k hk
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hpl, hdec⟩ := hp i (by simp)
      have hstep : mips32Next s = exec s i :=
        next_exec_plain hpl ht hn (by rw [hc.1]; exact hdec)
      rw [Function.iterate_succ_apply, hstep, List.take_succ_cons, List.foldl_cons]
      cases is with
      | nil => simp at hk; subst hk; rfl
      | cons j js =>
        obtain ⟨e1, e2, e3⟩ := hpl s hn
        have hmem : (exec s i).mem = s.mem := hw i (by simp) s
        apply ih
        · rw [hmem, e1]; exact hc.2.2
        · rw [e1, e2]; bv_omega
        · rw [e3, ht]
        · intro x hx; exact hp x (List.mem_cons_of_mem _ hx)
        · intro x hx; exact hw x (by simp only [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hx)
        · simpa using hk

end Flapjack.Mips32.TargetProof

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem codeIn_drop {m : Mem} {d : W → Prop} :
    ∀ (prog : List Insn) (pc : W) (k : Nat), CodeIn m d pc prog →
      CodeIn m d (pc + BitVec.ofNat 32 (4 * k)) (prog.drop k) := by
  intro prog
  induction prog with
  | nil => intro pc k _; simp [CodeIn]
  | cons i is ih =>
    intro pc k hc
    cases k with
    | zero => simpa using hc
    | succ k =>
      have := ih (pc + 4) k hc.2.2
      simp only [List.drop_succ_cons]
      have e : pc + 4 + BitVec.ofNat 32 (4 * k) = pc + BitVec.ofNat 32 (4 * (k + 1)) := by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
      rwa [e] at this

/-- Control facts of a run of plain instructions. -/
theorem foldl_plain : ∀ (prog : List Insn) (s : State), (∀ i ∈ prog, Plain i) →
    s.nextPc = s.pc + 4 →
    (prog.foldl exec s).pc = s.pc + BitVec.ofNat 32 (4 * prog.length) ∧
    (prog.foldl exec s).nextPc = (prog.foldl exec s).pc + 4 ∧
    (prog.foldl exec s).trapped = s.trapped := by
  intro prog
  induction prog with
  | nil => intro s _ hn; simp [hn]
  | cons i is ih =>
    intro s hp hn
    obtain ⟨e1, e2, e3⟩ := hp i (by simp) s hn
    obtain ⟨f1, f2, f3⟩ := ih (exec s i) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      (by rw [e1, e2]; bv_omega)
    refine ⟨?_, f2, f3.trans e3⟩
    rw [List.foldl_cons, f1, e1, List.length_cons, BitVec.add_assoc]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem foldl_noWrite : ∀ (prog : List Insn) (s : State), (∀ i ∈ prog, NoWrite i) →
    (prog.foldl exec s).mem = s.mem := by
  intro prog
  induction prog with
  | nil => intros; rfl
  | cons i is ih =>
    intro s hw
    rw [List.foldl_cons, ih _ (fun x hx => hw x (List.mem_cons_of_mem _ hx)), hw i (by simp) s]

theorem mips32Enc_length (i : HolAsm 32) : (mips32Enc i).length = 4 * (mips32Ast i).length := by
  simp only [mips32Enc, List.length_flatMap, mips32Encode, wordBytes, List.length_cons,
    List.length_nil]
  induction mips32Ast i with
  | nil => rfl
  | cons _ _ ih => simp [ih]; omega

theorem mem_allPcs (pc : W) (len k : Nat) (hk : k < len) :
    pc + BitVec.ofNat 32 (4 * k) ∈ allPcs (4 * len) pc 2 := by
  rw [allPcs_eq]
  exact ⟨k, by simp; omega, by simp [Nat.mul_comm]⟩

theorem aligned_add_four (pc : W) (k : Nat) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + BitVec.ofNat 32 (4 * k)) = true := by
  rw [(alignedAddSub 2 pc _ (by rw [holAligned_iff]; simp)).1, h]

/-- The facts every case reads off `asm_step` and the initial target relation. -/
structure Start (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State) : Prop where
  code : CodeIn ms.mem s1.memDomain ms.pc (mips32Ast i)
  pcs : allPcs (mips32Enc i).length s1.pc 0 ⊆ s1.memDomain
  pc : ms.pc = s1.pc
  nextPc : ms.nextPc = ms.pc + 4
  trapped : ms.trapped = false
  aligned : holAligned 2 ms.pc = true
  mem : ∀ a, s1.memDomain a → ms.mem.readByte a = s1.mem a
  reg : ∀ r, r < 32 → r ∉ mips32Config.avoidRegs → ms.reg (regOf r) = s1.regs r
  lr : s1.lr = 31
  be : s1.be = false
  align : s1.align = 2
  upd : asmUpd i (s1.pc + BitVec.ofNat 32 (mips32Enc i).length) s1 = s2
  ok : ¬ s2.failed
  asmOk : asmOkExact i mips32Config = true

theorem start (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State)
    (h : asmStep mips32Target.config s1 i s2 ∧ targetStateRel mips32Target s1 ms) :
    Start i s1 s2 ms := by
  obtain ⟨⟨hb, hlr, hbe, hal, hupd, hfail, hok⟩, hok', hpc, hmem, hreg, -⟩ := h
  change ms.pc = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.mem.readByte a = s1.mem a at hmem
  change ∀ r, r < 32 ∧ mips32Config.avoidRegs.contains r = false → ms.reg (regOf r) = s1.regs r
    at hreg
  change bytesInMemoryHOL s1.pc (mips32Enc i) s1.mem s1.memDomain at hb
  have hok'' : mips32Ok ms = true := hok'
  simp only [mips32Ok, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok''
  obtain ⟨⟨hn, ht⟩, ha⟩ := hok''
  exact {
    code := by
      rw [hpc]
      exact codeIn_of_bytes _ _ _ hmem _ _ hb
    pcs := bytesInMemory_allPcs _ _ _ _ 0 hb
    pc := hpc
    nextPc := hn
    trapped := ht
    aligned := ha
    mem := hmem
    reg := fun r hr ha => hreg r ⟨hr, by simpa using ha⟩
    lr := hlr
    be := hbe
    align := hal
    upd := hupd
    ok := hfail
    asmOk := hok }

/-- A straight-line constructor: every instruction is plain, only the last may write memory,
and the whole sequence relates the start state to the asm post-state. -/
theorem straightCase (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State)
    (st : Start i s1 s2 ms)
    (hdom : s2.memDomain = s1.memDomain)
    (hne : mips32Ast i ≠ [])
    (hp : ∀ x ∈ mips32Ast i, Plain x ∧ decode (encodeInsn x) = some x)
    (hw : ∀ x ∈ (mips32Ast i).dropLast, NoWrite x)
    (htouch : ∀ k (hk : k < (mips32Ast i).length),
      ∀ x ∈ touched (((mips32Ast i).take k).foldl exec ms) ((mips32Ast i)[k]), s1.memDomain x)
    (hq : targetStateRel mips32Target s2 ((mips32Ast i).foldl exec ms)) :
    CaseGoal i s1 s2 ms := by
  have hlen : 0 < (mips32Ast i).length := List.length_pos_iff.mpr hne
  have hrun := run_plain s1.memDomain (mips32Ast i) ms st.code st.nextPc st.trapped hp hw
  have hplain : ∀ x ∈ mips32Ast i, Plain x := fun x hx => (hp x hx).1
  -- facts about the state after `k` instructions, `k < (mips32Ast i).length`
  have hstate : ∀ k, k < (mips32Ast i).length →
      let s := ((mips32Ast i).take k).foldl exec ms
      s.pc = ms.pc + BitVec.ofNat 32 (4 * k) ∧ s.nextPc = s.pc + 4 ∧ s.trapped = false ∧
        s.mem = ms.mem := by
    intro k hk
    obtain ⟨f1, f2, f3⟩ := foldl_plain ((mips32Ast i).take k) ms
      (fun x hx => hplain x (List.mem_of_mem_take hx)) st.nextPc
    refine ⟨by rw [f1, List.length_take, Nat.min_eq_left (by omega)], f2, f3.trans st.trapped, ?_⟩
    apply foldl_noWrite
    intro x hx
    apply hw
    rw [List.dropLast_eq_take]
    exact List.take_subset_take_left _ (by omega) hx
  refine encoderCase i s1 s2 ms ((mips32Ast i).length - 1) hdom st.pcs ?_ ?_ ?_
  · intro k hk
    rw [hrun k (by omega)]
    obtain ⟨e1, e2, e3, e4⟩ := hstate k (by omega)
    intro _
    have hc := codeIn_drop (mips32Ast i) ms.pc k st.code
    rw [List.drop_eq_getElem_cons (by omega)] at hc
    obtain ⟨hword, hdomw, -⟩ := hc
    rw [← e1, ← e4] at hword
    rw [← e1] at hdomw
    have hdec : decode ((((mips32Ast i).take k).foldl exec ms).mem.readWord
        (((mips32Ast i).take k).foldl exec ms).pc) = some (mips32Ast i)[k] := by
      rw [hword]; exact (hp _ (List.getElem_mem _)).2
    refine ⟨⟨hdomw, fun j hj => ?_⟩, fun _ hn => ?_⟩
    · rw [hdec] at hj; cases hj; exact htouch k (by omega)
    · exfalso; apply hn
      simp only [fetchExec, hdec]
      obtain ⟨g1, g2, -⟩ := (hp _ (List.getElem_mem _)).1 _ e2
      rw [g1, g2]; bv_omega
  · intro k hk1 hk2
    rw [hrun k (by omega)]
    obtain ⟨e1, e2, e3, e4⟩ := hstate k (by omega)
    refine ⟨?_, fun pc _ => by rw [e4], ?_⟩
    · simp only [mips32Ok, e2, e3, beq_self_eq_true, Bool.not_false, Bool.and_self,
        Bool.true_and, e1]
      exact aligned_add_four _ _ st.aligned
    · rw [e1, st.pc, mips32Enc_length]; exact mem_allPcs _ _ _ (by omega)
  · rw [hrun _ (by omega), show (mips32Ast i).length - 1 + 1 = (mips32Ast i).length by omega, List.take_length]
    exact hq

end Flapjack.Mips32.TargetProof

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem regOf_eq {r : Nat} (h : r < 32) : regOf r = ⟨r, h⟩ := by
  simp [regOf, Nat.mod_eq_of_lt h]

theorem regOf_inj {a b : Nat} (ha : a < 32) (hb : b < 32) : regOf a = regOf b ↔ a = b := by
  rw [regOf_eq ha, regOf_eq hb]; simp

theorem regOf_ne_zero {a : Nat} (ha : a < 32) (h0 : a ≠ 0) : regOf a ≠ 0 := by
  rw [regOf_eq ha]; intro h; apply h0; simpa using congrArg Fin.val h

/-- A register the source program may name. -/
structure RegOk (r : Nat) : Prop where
  lt : r < 32
  avoid : r ∉ mips32Config.avoidRegs

theorem RegOk.ne_zero {r : Nat} (h : RegOk r) : r ≠ 0 := by
  intro h0; subst h0; exact h.avoid (by simp [mips32Config])
theorem RegOk.ne_tmp {r : Nat} (h : RegOk r) : regOf r ≠ tmp := by
  intro h1; apply h.avoid
  have := (regOf_inj h.lt (by decide : 1 < 32)).1 (by rw [h1]; rfl); subst this
  simp [mips32Config]
theorem RegOk.ne_tmp2 {r : Nat} (h : RegOk r) : regOf r ≠ tmp2 := by
  intro h1; apply h.avoid
  have := (regOf_inj h.lt (by decide : 30 < 32)).1 (by rw [h1]; rfl); subst this
  simp [mips32Config]
theorem RegOk.regOf_ne_zero {r : Nat} (h : RegOk r) : regOf r ≠ 0 :=
  Flapjack.Mips32.TargetProof.regOf_ne_zero h.lt h.ne_zero

theorem RegOk.tmp_ne {r : Nat} (h : RegOk r) : tmp ≠ regOf r := fun e => h.ne_tmp e.symm
theorem RegOk.tmp2_ne {r : Nat} (h : RegOk r) : tmp2 ≠ regOf r := fun e => h.ne_tmp2 e.symm

theorem regOf_ne {a b : Nat} (ha : RegOk a) (hb : RegOk b) (h : a ≠ b) : regOf a ≠ regOf b :=
  fun e => h ((regOf_inj ha.lt hb.lt).1 e)

theorem regOk_of_asm {r : Nat} (h : asmRegOkExact r mips32Config = true) : RegOk r := by
  simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine ⟨by simpa [mips32Config] using h.1, fun hm => ?_⟩
  have := h.2
  simp [mips32Config] at this hm
  omega

theorem targetStateRel_of (s2 : AsmState 32) (F : State) (hok : mips32Ok F = true)
    (hpc : F.pc = s2.pc) (hmem : ∀ a, s2.memDomain a → F.mem.readByte a = s2.mem a)
    (hreg : ∀ r, RegOk r → F.reg (regOf r) = s2.regs r) :
    targetStateRel mips32Target s2 F := by
  refine ⟨hok, hpc, hmem, fun r ⟨hr, ha⟩ => hreg r ⟨by simpa [mips32Target, mips32Config] using hr,
    by simpa [mips32Target, mips32Config] using ha⟩, fun r hr => ?_⟩
  simp [mips32Target, mips32Config] at hr

/-! Ziren's register-form ALU at the opcodes the backend uses. -/
@[simp] theorem alu_add (b c : W) : alu Opc.ADD b c = b + c := by simp [alu, Opc.ADD]
@[simp] theorem alu_sub (b c : W) : alu Opc.SUB b c = b - c := by simp [alu, Opc.ADD, Opc.SUB]
@[simp] theorem alu_and (b c : W) : alu Opc.AND b c = b &&& c := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND]
@[simp] theorem alu_or (b c : W) : alu Opc.OR b c = b ||| c := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR]
@[simp] theorem alu_xor (b c : W) : alu Opc.XOR b c = b ^^^ c := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR]
@[simp] theorem alu_nor (b c : W) : alu Opc.NOR b c = ~~~(b ||| c) := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR]
@[simp] theorem alu_slt (b c : W) : alu Opc.SLT b c = if b.slt c then 1 else 0 := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT]
@[simp] theorem alu_sltu (b c : W) : alu Opc.SLTU b c = if b.ult c then 1 else 0 := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT, Opc.SLTU]
@[simp] theorem alu_sll (b c : W) : alu Opc.SLL b c = b <<< (c.extractLsb' 0 5).toNat := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT, Opc.SLTU, Opc.MUL,
    Opc.SLL]
@[simp] theorem alu_srl (b c : W) : alu Opc.SRL b c = b >>> (c.extractLsb' 0 5).toNat := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT, Opc.SLTU, Opc.MUL,
    Opc.SLL, Opc.SRL]
@[simp] theorem alu_sra (b c : W) :
    alu Opc.SRA b c = b.sshiftRight (c.extractLsb' 0 5).toNat := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT, Opc.SLTU, Opc.MUL,
    Opc.SLL, Opc.SRL, Opc.SRA]
@[simp] theorem alu_ror (b c : W) :
    alu Opc.ROR b c = b.rotateRight (c.extractLsb' 0 5).toNat := by
  simp [alu, Opc.ADD, Opc.SUB, Opc.AND, Opc.OR, Opc.XOR, Opc.NOR, Opc.SLT, Opc.SLTU, Opc.MUL,
    Opc.SLL, Opc.SRL, Opc.SRA, Opc.ROR]

/-- The instructions that do not access memory. -/
def insnNoMem : Insn → Bool
  | .lb .. | .lbu .. | .sb .. | .lh .. | .lhu .. | .sh .. | .lw .. | .ll .. | .sw .. | .sc ..
  | .lwl .. | .lwr .. | .swl .. | .swr .. => false
  | _ => true

theorem touched_nil (x : Insn) (h : insnNoMem x = true) (s : State) : touched s x = [] := by
  cases x <;> simp_all [insnNoMem, touched]

theorem htouch_of_noMem {prog : List Insn} (h : ∀ x ∈ prog, insnNoMem x = true) (ms : State)
    (d : W → Prop) :
    ∀ k (hk : k < prog.length), ∀ x ∈ touched ((prog.take k).foldl exec ms) prog[k], d x := by
  intro k hk x hx
  rw [touched_nil _ (h _ (List.getElem_mem _))] at hx
  simp at hx

theorem mips32Ast_ne_nil (i : HolAsm 32) : mips32Ast i ≠ [] := by
  unfold mips32Ast
  repeat' split
  all_goals simp

/-- Ziren's decoder reads back every instruction the backend emits. -/
theorem decode_mips32Ast (i : HolAsm 32) :
    ∀ x ∈ mips32Ast i, decode (encodeInsn x) = some x := by
  unfold mips32Ast
  repeat' split
  all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  all_goals (try unfold cmpBranch)
  all_goals (try split)
  all_goals simp [nop]

/-- `straightCase` with the target relation of the final state unfolded: the final `pc`,
memory and source registers. -/
theorem straightCase' (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State)
    (st : Start i s1 s2 ms)
    (hdom : s2.memDomain = s1.memDomain)
    (hp : ∀ x ∈ mips32Ast i, Plain x)
    (hw : ∀ x ∈ (mips32Ast i).dropLast, NoWrite x)
    (htouch : ∀ k (hk : k < (mips32Ast i).length),
      ∀ x ∈ touched (((mips32Ast i).take k).foldl exec ms) ((mips32Ast i)[k]), s1.memDomain x)
    (hpc : s2.pc = s1.pc + BitVec.ofNat 32 (mips32Enc i).length)
    (hmem : ∀ a, s2.memDomain a → ((mips32Ast i).foldl exec ms).mem.readByte a = s2.mem a)
    (hreg : ∀ r, RegOk r → ((mips32Ast i).foldl exec ms).reg (regOf r) = s2.regs r) :
    CaseGoal i s1 s2 ms := by
  apply straightCase i s1 s2 ms st hdom (mips32Ast_ne_nil i)
    (fun x hx => ⟨hp x hx, decode_mips32Ast i x hx⟩) hw htouch
  obtain ⟨f1, f2, f3⟩ := foldl_plain (mips32Ast i) ms hp st.nextPc
  apply targetStateRel_of _ _ _ _ hmem hreg
  · simp only [mips32Ok, f2, f3, st.trapped, beq_self_eq_true, Bool.not_false, Bool.and_self,
      Bool.true_and, f1]
    exact aligned_add_four _ _ st.aligned
  · rw [f1, hpc, st.pc, mips32Enc_length]

end Flapjack.Mips32.TargetProof
