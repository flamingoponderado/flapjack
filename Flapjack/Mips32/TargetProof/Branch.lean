import Flapjack.Mips32.TargetProof.Step
import Mathlib.Tactic.Set

/-! # Sequences ending in a branch and its delay slot

The control-flow constructors end in a branch or jump followed by a `nop` in its delay slot.
`mips32Next` runs the branch and its delay slot in one step when the branch leaves the
sequential path, and in two steps otherwise; either way the state after the delay slot is
`exec (exec t br) nop`, where `t` is the state at the branch, so `branchCase` asks only for
that state to be related to the asm post-state. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

/-- An instruction that, from any state, moves on to the instruction at `nextPc`. -/
def Seq (i : Insn) : Prop :=
  ∀ s : State, (exec s i).pc = s.nextPc ∧ (exec s i).nextPc = s.nextPc + 4 ∧
    (exec s i).trapped = s.trapped

set_option maxHeartbeats 400000 in
theorem seq_of_sequential (i : Insn) (h : insnSequential i = true) : Seq i := by
  intro s
  cases i <;> simp [insnSequential] at h <;>
    simp only [exec, setReg_pc, setReg_nextPc, setReg_trapped, setHiLo] <;>
    (try split) <;> (try simp only [setReg_pc, setReg_nextPc, setReg_trapped]) <;>
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem Seq.plain {i : Insn} (h : Seq i) : Plain i := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s
  refine ⟨by rw [h1, hs], by rw [h2, hs]; bv_omega, h3⟩

theorem plain_nop : Plain nop := plain_of_sequential _ rfl
theorem noWrite_nop : NoWrite nop := noWrite_of_writes _ rfl
theorem decode_nop : decode (encodeInsn nop) = some nop := decode_sll 0 0 0

theorem exec_nop (s : State) :
    exec s nop = { s with pc := s.nextPc, nextPc := s.nextPc + 4 } := by
  simp [nop, exec, State.setReg]

theorem codeIn_append {m : Mem} {d : W → Prop} :
    ∀ (pre post : List Insn) (pc : W), CodeIn m d pc (pre ++ post) →
      CodeIn m d pc pre ∧ CodeIn m d (pc + BitVec.ofNat 32 (4 * pre.length)) post := by
  intro pre
  induction pre with
  | nil => intro post pc h; simpa [CodeIn] using h
  | cons i is ih =>
    intro post pc h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨g1, g2⟩ := ih post (pc + 4) h3
    refine ⟨⟨h1, h2, g1⟩, ?_⟩
    have e : pc + 4 + BitVec.ofNat 32 (4 * is.length) =
        pc + BitVec.ofNat 32 (4 * (i :: is).length) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rwa [e] at g2

/-- A constructor encoded as a plain prefix, a branch `br` and a sequential delay-slot
instruction `ds` without memory accesses. -/
theorem branchCase (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State)
    (st : Start i s1 s2 ms) (pre : List Insn) (br ds : Insn)
    (hsplit : mips32Ast i = pre ++ [br, ds])
    (hdom : s2.memDomain = s1.memDomain)
    (hp : ∀ x ∈ pre, Plain x ∧ decode (encodeInsn x) = some x ∧ NoWrite x)
    (htouch : ∀ k (hk : k < pre.length), touched ((pre.take k).foldl exec ms) pre[k] = [])
    (hbr : decode (encodeInsn br) = some br)
    (hbrPc : ∀ t : State, (exec t br).pc = t.nextPc ∧ (exec t br).trapped = t.trapped ∧
      (exec t br).mem = t.mem ∧ touched t br = [])
    (hds : Seq ds) (hdsw : NoWrite ds) (hdsm : insnNoMem ds = true)
    (hdsd : decode (encodeInsn ds) = some ds)
    (hpc : (exec (exec (pre.foldl exec ms) br) ds).pc = s2.pc)
    (hal : holAligned 2 s2.pc = true)
    (hmem : ∀ a, s2.memDomain a →
      (exec (exec (pre.foldl exec ms) br) ds).mem.readByte a = s2.mem a)
    (hreg : ∀ r, RegOk r → (exec (exec (pre.foldl exec ms) br) ds).reg (regOf r) = s2.regs r) :
    CaseGoal i s1 s2 ms := by
  have hplain : ∀ x ∈ pre, Plain x := fun x hx => (hp x hx).1
  have hcode := st.code
  rw [hsplit] at hcode
  obtain ⟨hcpre, hcpost⟩ := codeIn_append pre [br, ds] ms.pc hcode
  obtain ⟨hwbr, hdbr, hwnop, hdnop, -⟩ := hcpost
  have hrun := run_plain s1.memDomain pre ms hcpre st.nextPc st.trapped
    (fun x hx => ⟨(hp x hx).1, (hp x hx).2.1⟩)
    (fun x hx => (hp x (List.dropLast_subset _ hx)).2.2)
  set t := pre.foldl exec ms with ht
  obtain ⟨t1, t2, t3⟩ := foldl_plain pre ms hplain st.nextPc
  have t4 : t.mem = ms.mem := foldl_noWrite pre ms (fun x hx => (hp x hx).2.2)
  try rw [← ht] at t1 t2 t3
  set u := exec t br with hu
  obtain ⟨u1, u2, u3, u4⟩ := hbrPc t
  try rw [← hu] at u1 u2 u3 u4
  have hlen : (mips32Enc i).length = 4 * (pre.length + 2) := by
    rw [mips32Enc_length, hsplit]; simp
  -- the state before each prefix instruction
  have hstate : ∀ k, k ≤ pre.length →
      ((pre.take k).foldl exec ms).pc = ms.pc + BitVec.ofNat 32 (4 * k) ∧
      ((pre.take k).foldl exec ms).nextPc = ((pre.take k).foldl exec ms).pc + 4 ∧
      ((pre.take k).foldl exec ms).trapped = false ∧ ((pre.take k).foldl exec ms).mem = ms.mem := by
    intro k hk
    obtain ⟨f1, f2, f3⟩ := foldl_plain (pre.take k) ms
      (fun x hx => hplain x (List.mem_of_mem_take hx)) st.nextPc
    refine ⟨by rw [f1, List.length_take, Nat.min_eq_left hk], f2, f3.trans st.trapped,
      foldl_noWrite _ _ (fun x hx => (hp x (List.mem_of_mem_take hx)).2.2)⟩
  have tpc : t.pc = ms.pc + BitVec.ofNat 32 (4 * pre.length) := t1
  have hdecbr : decode (t.mem.readWord t.pc) = some br := by rw [t4, tpc, hwbr]; exact hbr
  have upc : u.pc = ms.pc + BitVec.ofNat 32 (4 * (pre.length + 1)) := by
    rw [u1, t2, tpc, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  have hwnop' : u.mem.readWord u.pc = encodeInsn ds := by
    rw [u3, t4, upc]
    have e : ms.pc + BitVec.ofNat 32 (4 * pre.length) + 4 =
        ms.pc + BitVec.ofNat 32 (4 * (pre.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [← e]; exact hwnop
  have hdomnop : ∀ x ∈ wordAt u.pc, s1.memDomain x := by
    rw [upc]
    have e : ms.pc + BitVec.ofNat 32 (4 * pre.length) + 4 =
        ms.pc + BitVec.ofNat 32 (4 * (pre.length + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [← e]; exact hdnop
  have hdecnop : decode (u.mem.readWord u.pc) = some ds := by rw [hwnop']; exact hdsd
  have utr : u.trapped = false := u2.trans (t3.trans st.trapped)
  have hprefix : ∀ k, k < pre.length → NextSafe s1.memDomain (mips32Next^[k] ms) := by
    intro k hk
    rw [hrun k (by omega)]
    obtain ⟨e1, e2, e3, e4⟩ := hstate k (by omega)
    intro _
    have hc := codeIn_drop pre ms.pc k hcpre
    rw [List.drop_eq_getElem_cons hk] at hc
    obtain ⟨hword, hdomw, -⟩ := hc
    rw [← e1, ← e4] at hword
    rw [← e1] at hdomw
    have hdec : decode (((pre.take k).foldl exec ms).mem.readWord
        ((pre.take k).foldl exec ms).pc) = some pre[k] := by
      rw [hword]; exact (hp _ (List.getElem_mem _)).2.1
    refine ⟨⟨hdomw, fun j hj => ?_⟩, fun _ hn => ?_⟩
    · rw [hdec] at hj; cases hj; rw [htouch k hk]; simp
    · exfalso; apply hn
      simp only [fetchExec, hdec]
      obtain ⟨g1, g2, -⟩ := (hp _ (List.getElem_mem _)).1 _ e2
      rw [g1, g2]; bv_omega
  have hprefixP : ∀ k, 1 ≤ k → k ≤ pre.length →
      mips32Ok (mips32Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (mips32Enc i).length s1.pc 0 →
        (mips32Next^[k] ms).mem.readByte pc = ms.mem.readByte pc) ∧
      (mips32Next^[k] ms).pc ∈ allPcs (mips32Enc i).length s1.pc 2 := by
    intro k hk1 hk2
    rw [hrun k hk2]
    obtain ⟨e1, e2, e3, e4⟩ := hstate k hk2
    refine ⟨?_, fun pc _ => by rw [e4], ?_⟩
    · simp only [mips32Ok, e2, e3, beq_self_eq_true, Bool.not_false, Bool.and_self,
        Bool.true_and, e1]
      exact aligned_add_four _ _ st.aligned
    · rw [e1, st.pc, hlen]; exact mem_allPcs _ _ _ (by omega)
  have htsafe : StepSafe s1.memDomain t := by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [tpc]; exact hdbr
    · rw [hdecbr] at hj; cases hj; rw [u4]; simp
  have husafe : StepSafe s1.memDomain u :=
    ⟨hdomnop, fun j hj => by rw [hdecnop] at hj; cases hj; rw [touched_nil _ hdsm]; simp⟩
  obtain ⟨f1, f2, f3⟩ := hds u
  have hrel : targetStateRel mips32Target s2 (exec u ds) := by
    apply targetStateRel_of _ _ _ hpc hmem hreg
    simp only [mips32Ok, f1, f2, f3, utr, beq_self_eq_true, Bool.not_false, Bool.and_self,
      Bool.true_and]
    rw [f1] at hpc
    rw [hpc]; exact hal
  by_cases hmerge : u.nextPc = u.pc + 4
  · -- branch then delay slot as two steps
    have hnext_t : mips32Next t = u := next_exec (t3.trans st.trapped) hdecbr utr hmerge
    have hnext_u : mips32Next u = exec u ds :=
      next_exec_plain hds.plain utr hmerge hdecnop
    have hit : ∀ k, k ≤ pre.length → mips32Next^[k] ms = (pre.take k).foldl exec ms := hrun
    refine encoderCase i s1 s2 ms (pre.length + 1) hdom st.pcs ?_ ?_ ?_
    · intro k hk
      rcases Nat.lt_or_ge k pre.length with h | h
      · exact hprefix k h
      rcases Nat.eq_or_lt_of_le h with h | h
      · subst h
        rw [hit _ (Nat.le_refl _), List.take_length, ← ht]
        intro _
        refine ⟨htsafe, fun _ hn => ?_⟩
        exfalso; apply hn
        simp only [fetchExec, hdecbr]; exact hmerge
      · have hk' : k = pre.length + 1 := by omega
        subst hk'
        rw [Function.iterate_succ_apply', hit _ (Nat.le_refl _), List.take_length, ← ht, hnext_t]
        intro _
        refine ⟨husafe, fun _ hn => ?_⟩
        exfalso; apply hn
        simp only [fetchExec, hdecnop]
        obtain ⟨g1, g2, -⟩ := hds.plain u hmerge
        rw [g1, g2]; bv_omega
    · intro k hk1 hk2
      rcases Nat.lt_or_ge pre.length k with h | h
      · have hk' : k = pre.length + 1 := by omega
        subst hk'
        rw [Function.iterate_succ_apply', hit _ (Nat.le_refl _), List.take_length, ← ht, hnext_t]
        refine ⟨?_, fun pc _ => by rw [u3, t4], ?_⟩
        · simp only [mips32Ok, hmerge, utr, beq_self_eq_true, Bool.not_false, Bool.and_self,
            Bool.true_and, upc]
          exact aligned_add_four _ _ st.aligned
        · rw [upc, st.pc, hlen]; exact mem_allPcs _ _ _ (by omega)
      · exact hprefixP k hk1 h
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hit _ (Nat.le_refl _),
        List.take_length, ← ht, hnext_t, hnext_u]
      exact hrel
  · -- branch and delay slot as one step
    have hnext_t : mips32Next t = exec u ds := by
      simp [mips32Next, fetchExec, t3, st.trapped, hdecbr, ← hu, utr, hdecnop]
      exact fun h => absurd h hmerge
    have hit : ∀ k, k ≤ pre.length → mips32Next^[k] ms = (pre.take k).foldl exec ms := hrun
    refine encoderCase i s1 s2 ms pre.length hdom st.pcs ?_ ?_ ?_
    · intro k hk
      rcases Nat.lt_or_ge k pre.length with h | h
      · exact hprefix k h
      · have hk' : k = pre.length := by omega
        subst hk'
        rw [hit _ (Nat.le_refl _), List.take_length, ← ht]
        intro _
        refine ⟨htsafe, fun _ _ => ?_⟩
        simp only [fetchExec, hdecbr]; exact husafe
    · intro k hk1 hk2
      exact hprefixP k hk1 hk2
    · rw [Function.iterate_succ_apply', hit _ (Nat.le_refl _), List.take_length, ← ht, hnext_t]
      exact hrel

end Flapjack.Mips32.TargetProof
