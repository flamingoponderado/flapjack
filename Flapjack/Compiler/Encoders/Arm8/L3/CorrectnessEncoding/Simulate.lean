import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.Bytes
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

set_option maxHeartbeats 4000000

/-!
# From an interference-free run to `encoder_correct arm8TargetL3`

The L3 analogue of `Flapjack/Compiler/Encoders/Arm8/Machine/Simulate.lean`:
`Arm8L3Agree` records agreement on everything `arm8Proj` observes, and
`arm8Proj_eq_iff` identifies it with equality of the projection.  The
congruence lemmas let a case proof transfer the intermediate assertions and
the post-state relation across an interference environment.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- Agreement of two L3 ARMv8 states on every component `arm8_proj` observes,
plus memory on the source domain. -/
structure Arm8L3Agree (d : BitVec 64 → Prop) (s t : arm8_state) : Prop where
  pc : s.PC = t.PC
  reg : s.REG = t.REG
  pstate : s.PSTATE = t.PSTATE
  sctlr : s.SCTLR_EL1 = t.SCTLR_EL1
  tcr : s.TCR_EL1 = t.TCR_EL1
  exc : s.exception = t.exception
  mem : ∀ a, d a → s.MEM a = t.MEM a

theorem Arm8L3Agree.refl (d : BitVec 64 → Prop) (s : arm8_state) : Arm8L3Agree d s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Arm8L3Agree.symm {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) : Arm8L3Agree d t s :=
  ⟨h.pc.symm, h.reg.symm, h.pstate.symm, h.sctlr.symm, h.tcr.symm, h.exc.symm,
    fun a ha => (h.mem a ha).symm⟩

theorem Arm8L3Agree.trans {d : BitVec 64 → Prop} {s t u : arm8_state}
    (h1 : Arm8L3Agree d s t) (h2 : Arm8L3Agree d t u) : Arm8L3Agree d s u :=
  ⟨h1.pc.trans h2.pc, h1.reg.trans h2.reg, h1.pstate.trans h2.pstate,
    h1.sctlr.trans h2.sctlr, h1.tcr.trans h2.tcr, h1.exc.trans h2.exc,
    fun a ha => (h1.mem a ha).trans (h2.mem a ha)⟩

/-- Equal projections are exactly agreement on the observed components. -/
theorem arm8Proj_eq_iff (d : BitVec 64 → Prop) (s t : arm8_state) :
    arm8Proj d s = arm8Proj d t ↔ Arm8L3Agree d s t := by
  constructor
  · intro h
    have hp : s.PSTATE = t.PSTATE := congrArg (fun p => p.1) h
    have hs : s.SCTLR_EL1 = t.SCTLR_EL1 := congrArg (fun p => p.2.1) h
    have ht : s.TCR_EL1 = t.TCR_EL1 := congrArg (fun p => p.2.2.1) h
    have he : s.exception = t.exception := congrArg (fun p => p.2.2.2.1) h
    have hr : s.REG = t.REG := congrArg (fun p => p.2.2.2.2.1) h
    have hm : (arm8Proj d s).2.2.2.2.2.1 = (arm8Proj d t).2.2.2.2.2.1 :=
      congrArg (fun p => p.2.2.2.2.2.1) h
    have hpc : s.PC = t.PC := congrArg (fun p => p.2.2.2.2.2.2) h
    refine ⟨hpc, hr, hp, hs, ht, he, fun a ha => ?_⟩
    have hleft : (arm8Proj d s).2.2.2.2.2.1 (a, s.MEM a) := by
      rw [arm8Proj_memory]; exact ⟨rfl, ha⟩
    rw [hm, arm8Proj_memory] at hleft
    exact hleft.1.symm
  · intro h
    obtain ⟨hpc, hr, hp, hs, ht, he, hm⟩ := h
    have hmem : SetSep.fun2Set (s.MEM, d) = SetSep.fun2Set (t.MEM, d) := by
      funext p
      obtain ⟨a, b⟩ := p
      apply propext
      rw [SetSep.fun2SetThm, SetSep.fun2SetThm]
      by_cases ha : d a
      · rw [hm a ha]
      · simp [ha]
    simp only [arm8Proj, hp, hs, ht, he, hr, hpc, hmem]

/-- The four instruction bytes at the PC of a state carry over to any state
agreeing with it on a domain containing them (Flapjack infrastructure). -/
theorem Arm8L3Agree.word {d : BitVec 64 → Prop} {u t : arm8_state} (h : Arm8L3Agree d u t)
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j)) (w : BitVec 32)
    (h0 : t.MEM t.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (h1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (h2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (h3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat)) :
    u.MEM u.PC = BitVec.ofNat 8 ((w >>> 0).toNat) ∧
      u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) ∧
      u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) ∧
      u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
  rw [h.pc]
  exact ⟨(h.mem _ (by simpa using hf 0 (by omega))).trans h0,
    (h.mem _ (by simpa using hf 1 (by omega))).trans h1,
    (h.mem _ (by simpa using hf 2 (by omega))).trans h2,
    (h.mem _ (by simpa using hf 3 (by omega))).trans h3⟩

/-- `arm8Ok` only reads the components `Arm8L3Agree` fixes. -/
theorem arm8Ok_congr {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) : arm8Ok s = arm8Ok t := by
  simp only [arm8Ok, h.pstate, h.sctlr, h.tcr, h.exc, h.pc]

/-- `targetStateRel arm8TargetL3` is invariant under agreement on the source
domain. -/
theorem targetStateRel_congr {s2 : AsmState 64} {s t : arm8_state}
    (h : Arm8L3Agree s2.memDomain s t)
    (ht : targetStateRel arm8TargetL3 s2 t) : targetStateRel arm8TargetL3 s2 s := by
  obtain ⟨hok, hp, hmem, hreg, hfp⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hok]; exact arm8Ok_congr h
  · rw [← hp]; exact h.pc
  · intro a ha; rw [← hmem a ha]; exact h.mem a ha
  · intro i hi; simpa only [arm8TargetL3_getReg, h.reg] using hreg i hi
  · intro i hi
    simp [arm8ConfigL3] at hi

/-- `arm8Next` respects agreement for any instruction word whose step has an
explicit equation `arm8Next u = F u` (Flapjack infrastructure): the word is
read from the same in-domain bytes in both states, so both step by `F`, and
`hF` says `F` maps the agreeing pair to an agreeing pair.  `hnext` takes the
standard `arm8Next_*` premises in their usual order. -/
theorem arm8L3Agree_next {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) (hok : arm8Ok s = true) (w : BitVec 32)
    (F : arm8_state → arm8_state)
    (hnext : ∀ u : arm8_state, u.exception = exception.NoException →
      u.MEM u.PC = BitVec.ofNat 8 ((w >>> 0).toNat) →
      u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) →
      u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) →
      u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) →
      Aligned (TN := 64) (u.PC, 4) = true →
      u.SCTLR_EL1.E0E = false → u.PSTATE.EL = (0 : BitVec 2) → arm8Next u = F u)
    (hF : Arm8L3Agree d (F s) (F t))
    (hf : ∀ j, j < 4 → d (t.PC + BitVec.ofNat 64 j))
    (hb0 : t.MEM t.PC = BitVec.ofNat 8 ((w >>> 0).toNat))
    (hb1 : t.MEM (t.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat))
    (hb2 : t.MEM (t.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat))
    (hb3 : t.MEM (t.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat)) :
    Arm8L3Agree d (arm8Next s) (arm8Next t) := by
  have hokt : arm8Ok t = true := by rw [← arm8Ok_congr h]; exact hok
  obtain ⟨hel, he0, _, _, _, hexc0, halign⟩ := (arm8Ok_iff s).mp hok
  obtain ⟨helt, he0t, _, _, _, hexc0t, halignt⟩ := (arm8Ok_iff t).mp hokt
  have hal : Aligned (TN := 64) (s.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 s.PC).mp halign
  have halt : Aligned (TN := 64) (t.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 t.PC).mp halignt
  obtain ⟨hs0, hs1, hs2, hs3⟩ := h.word hf w hb0 hb1 hb2 hb3
  rw [hnext s hexc0 hs0 hs1 hs2 hs3 hal he0 hel, hnext t hexc0t hb0 hb1 hb2 hb3 halt he0t helt]
  exact hF

/-- The conclusion of `encoder_correct` for one source instruction, at
`arm8TargetL3`. -/
def CaseGoal (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : arm8_state) : Prop :=
  ∃ n : Nat, ∀ env : Nat → arm8_state → arm8_state,
    interferenceOk env (arm8Proj s1.memDomain) →
    let pcs := allPcs (arm8ConfigL3.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (arm8Next s)) ms
        (fun ms' => arm8Ok ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → ms'.MEM pc = ms.MEM pc) ∧
          ms'.PC ∈ pcs arm8ConfigL3.codeAlignment)
        (fun ms' => targetStateRel arm8TargetL3 s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) arm8Next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → ms1.MEM x = ms2.MEM x)

/-- One constructor of `encoder_correct arm8TargetL3` from any one-instruction
lowering: the single `arm8Next` step executes `i`, which writes `v` into the
destination register `r` and changes nothing else (Flapjack infrastructure;
the `const` and `arith` one-instruction shapes both use it).  The source-state
update facts are hypotheses because `asmUpd` inspects the instruction. -/
theorem asmCaseOne (inst : HolInst 64) (r : Nat) (v : BitVec 64)
    (t : arm8_state) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst inst) s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hnext : arm8Next ms = t)
    (htpc : t.PC = ms.PC + 4)
    (htmem : ∀ x, t.MEM x = ms.MEM x)
    (htreg : ∀ k, k < 32 → k ≠ r → t.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k))
    (htval : t.REG (BitVec.ofNat 5 r) = v)
    (htok : arm8Ok t = true)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4)
    (hs2mem : ∀ x, s2.mem x = s1.mem x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, s2.regs k = if k = r then v else s1.regs k) :
    CaseGoal (.inst inst) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hq : targetStateRel arm8TargetL3 s2 t := by
    refine ⟨htok, ?_, ?_, ?_, ?_⟩
    · change t.PC = s2.pc
      rw [htpc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → t.MEM a = s2.mem a
      intro a ha
      rw [htmem, hs2mem]
      exact hmem a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        t.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      by_cases hkr : k = r
      · rw [hkr, htval, hs2regs r, if_pos rfl]
      · rw [htreg k hk.1 hkr, hs2regs k, if_neg hkr]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hnext]
    have hagree : Arm8L3Agree s2.memDomain (env 0 t) t := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 t
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x _ => ?_, trivial⟩
    rw [hnext]
    exact (htmem x).symm

/-- One constructor of `encoder_correct arm8TargetL3` for a one-instruction
lowering that writes `v` into the destination register `r` and may change
memory (Flapjack infrastructure; the `Mem` store form needs it because
`asmCaseOne` assumes the instruction leaves memory unchanged).  Memory inside
the source domain follows the source update, memory outside it is preserved. -/
theorem asmCaseOneMem (inst : HolInst 64) (r : Nat) (v : BitVec 64)
    (t : arm8_state) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst inst) s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hnext : arm8Next ms = t)
    (htpc : t.PC = ms.PC + 4)
    (htmemIn : ∀ x, s1.memDomain x → t.MEM x = s2.mem x)
    (htmemOut : ∀ x, ¬ s1.memDomain x → t.MEM x = ms.MEM x)
    (htreg : ∀ k, k < 32 → k ≠ r → t.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k))
    (htval : t.REG (BitVec.ofNat 5 r) = v)
    (htok : arm8Ok t = true)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, s2.regs k = if k = r then v else s1.regs k) :
    CaseGoal (.inst inst) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, _hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hq : targetStateRel arm8TargetL3 s2 t := by
    refine ⟨htok, ?_, ?_, ?_, ?_⟩
    · change t.PC = s2.pc
      rw [htpc, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → t.MEM a = s2.mem a
      intro a ha
      exact htmemIn a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        t.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      by_cases hkr : k = r
      · rw [hkr, htval, hs2regs r, if_pos rfl]
      · rw [htreg k hk.1 hkr, hs2regs k, if_neg hkr]
        exact hreg k hk
    · intro k hk
      simp [arm8ConfigL3] at hk
  refine ⟨0, ?_⟩
  intro env henv
  constructor
  · change targetStateRel arm8TargetL3 s2 (env 0 (arm8Next ms))
    rw [hnext]
    have hagree : Arm8L3Agree s2.memDomain (env 0 t) t := by
      rw [← arm8Proj_eq_iff]
      have hh := henv 0 t
      rw [hs2dom]
      exact hh
    exact targetStateRel_congr hagree hq
  · refine ⟨fun x hx => ?_, trivial⟩
    rw [hnext]
    exact (htmemOut x hx).symm


/-- The two PCs covered by an 8-byte, 4-byte-aligned code window. -/
theorem mem_allPcs_eight_l3 (p : BitVec 64) (i : Nat) (hi : i < 2) :
    p + BitVec.ofNat 64 (i * 4) ∈ allPcs 8 p 2 := by
  rw [allPcs_eq]
  refine ⟨i, ?_, rfl⟩
  have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
  omega

/-- The states a straight-line simulation may reach before its `k`-th
step: the start state itself before the first step, and afterwards anything
agreeing with the expected state `T k` (Flapjack infrastructure). -/
def ChainAt (d : BitVec 64 → Prop) (s0 : arm8_state) (T : Nat → arm8_state) (k : Nat)
    (u : arm8_state) : Prop :=
  (k = 0 → u = s0) ∧ (k ≠ 0 → Arm8L3Agree d u (T k))

/-- The `asserts` half of `CaseGoal` for a straight-line lowering of `n + 1`
instructions (Flapjack infrastructure): if every state reachable before step
`k` steps to a state agreeing with `T (k + 1)`, the intermediate assertion
holds on everything agreeing with `T 1`, ..., `T n`, and the final one on
everything agreeing with `T (n + 1)`, then the interleaving of `arm8Next` with
the interference environment satisfies `asserts`. -/
theorem asserts_chain {d : BitVec 64 → Prop} (n : Nat) (env : Nat → arm8_state → arm8_state)
    (s0 : arm8_state) (T : Nat → arm8_state) (P Q : arm8_state → Prop)
    (henv : ∀ k x, Arm8L3Agree d (env k x) x)
    (hstep : ∀ k, k ≤ n → ∀ u, ChainAt d s0 T k u → Arm8L3Agree d (arm8Next u) (T (k + 1)))
    (hP : ∀ k, 1 ≤ k → k ≤ n → ∀ u, Arm8L3Agree d u (T k) → P u)
    (hQ : ∀ u, Arm8L3Agree d u (T (n + 1)) → Q u) :
    ∀ m, m ≤ n → ∀ s, ChainAt d s0 T (n - m) s →
      asserts m (fun k s => env (n - k) (arm8Next s)) s P Q := by
  intro m
  induction m with
  | zero =>
    intro _ s hs
    show Q (env (n - 0) (arm8Next s))
    apply hQ
    have h1 := hstep n le_rfl s (by simpa using hs)
    exact (henv _ _).trans h1
  | succ m ih =>
    intro hm s hs
    have h1 : Arm8L3Agree d (env (n - (m + 1)) (arm8Next s)) (T (n - m)) := by
      have h2 := hstep (n - (m + 1)) (by omega) s hs
      rw [show n - (m + 1) + 1 = n - m by omega] at h2
      exact (henv _ _).trans h2
    exact ⟨hP (n - m) (by omega) (by omega) _ h1,
      ih (by omega) _ ⟨fun h => absurd h (by omega), fun _ => h1⟩⟩

/-- The `asserts2` half of `CaseGoal` for a straight-line lowering of `n + 1`
instructions (Flapjack infrastructure): every step relates its pre- and
post-state by `R`. -/
theorem asserts2_chain {d : BitVec 64 → Prop} (n : Nat) (env : Nat → arm8_state → arm8_state)
    (s0 : arm8_state) (T : Nat → arm8_state) (R : arm8_state → arm8_state → Prop)
    (henv : ∀ k x, Arm8L3Agree d (env k x) x)
    (hstep : ∀ k, k ≤ n → ∀ u, ChainAt d s0 T k u → Arm8L3Agree d (arm8Next u) (T (k + 1)))
    (hR : ∀ k, k ≤ n → ∀ u, ChainAt d s0 T k u → R u (arm8Next u)) :
    ∀ m, m ≤ n + 1 → ∀ s, ChainAt d s0 T (n + 1 - m) s →
      asserts2 m (fun k => env (n + 1 - k)) arm8Next s R := by
  intro m
  induction m with
  | zero => intro _ _ _; trivial
  | succ m ih =>
    intro hm s hs
    have h1 : Arm8L3Agree d (env (n + 1 - (m + 1)) (arm8Next s)) (T (n + 1 - m)) := by
      have h2 := hstep (n + 1 - (m + 1)) (by omega) s hs
      rw [show n + 1 - (m + 1) + 1 = n + 1 - m by omega] at h2
      exact (henv _ _).trans h2
    exact ⟨hR (n + 1 - (m + 1)) (by omega) s hs,
      ih (by omega) _ ⟨fun h => absurd h (by omega), fun _ => h1⟩⟩

/-- `encoder_correct`'s case obligation for a straight-line lowering of
`n + 1` instructions that leaves memory outside the source domain alone
(Flapjack infrastructure, the counterpart of HOL's repeated
`next_state_tacN` steps).  `T k` is the machine state expected after `k`
steps; `hstep` steps every state `ChainAt` admits before step `k` (the start
state itself for the first step), `hok`/`hpc`/`hcode` are the intermediate
assertions, and `hfinal` is the post-state relation. -/
theorem asmCaseChain (i : HolAsm 64) (n : Nat) (T : Nat → arm8_state)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 i s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hlen : (arm8Enc i).length = 4 * (n + 1))
    (hstep : ∀ k, k ≤ n → ∀ u, ChainAt s1.memDomain ms T k u →
      Arm8L3Agree s1.memDomain (arm8Next u) (T (k + 1)))
    (hstepMem : ∀ k, k ≤ n → ∀ u, ChainAt s1.memDomain ms T k u →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x)
    (hok : ∀ k, 1 ≤ k → k ≤ n → arm8Ok (T k) = true)
    (hpc : ∀ k, 1 ≤ k → k ≤ n → (T k).PC = ms.PC + BitVec.ofNat 64 (4 * k))
    (hcode : ∀ k, 1 ≤ k → k ≤ n → ∀ x, s1.memDomain x → (T k).MEM x = ms.MEM x)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hfinal : targetStateRel arm8TargetL3 s2 (T (n + 1))) :
    CaseGoal i s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hpc0 : ms.PC = s1.pc := hr.2.1
  have hcodeDom : allPcs (arm8Enc i).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs (arm8Enc i) s1.pc s1.mem s1.memDomain 0 hs.1
  have hstart : ∀ k, k = 0 → ChainAt s1.memDomain ms T k ms :=
    fun k hk => ⟨fun _ => rfl, fun h => absurd hk h⟩
  refine ⟨n, ?_⟩
  intro env henv
  have henv' : ∀ k x, Arm8L3Agree s1.memDomain (env k x) x := fun k x =>
    (arm8Proj_eq_iff s1.memDomain _ _).mp (henv k x)
  constructor
  · refine asserts_chain n env ms T _ _ henv' hstep ?_ ?_ n le_rfl ms (hstart _ (by omega))
    · intro k hk1 hkn u hu
      refine ⟨?_, ?_, ?_⟩
      · rw [arm8Ok_congr hu]
        exact hok k hk1 hkn
      · intro pc hpc'
        have hd := hcodeDom hpc'
        exact (hu.mem pc hd).trans (hcode k hk1 hkn pc hd)
      · change u.PC ∈ allPcs (arm8Enc i).length s1.pc 2
        rw [hu.pc, hpc k hk1 hkn, hpc0, hlen, allPcs_eq]
        refine ⟨k, ?_, ?_⟩
        · have h4 : (2 : Nat) ^ 2 = 4 := by norm_num
          rw [h4]
          omega
        · congr 1
          congr 1
          norm_num
          omega
    · intro u hu
      have hu' : Arm8L3Agree s2.memDomain u (T (n + 1)) := by rw [hs2dom]; exact hu
      exact targetStateRel_congr hu' hfinal
  · refine asserts2_chain n env ms T _ henv' hstep ?_ (n + 1) le_rfl ms
      (hstart _ (by omega))
    intro k hk u hu x hx
    exact (hstepMem k hk u hu x hx).symm

/-- Two `arm8Next` steps for a two-instruction lowering: the first step leaves
memory alone outside the source domain, the second may write inside it, and
the final state's allocatable registers are the source post-state's
(`htregs`).  The interference environment is applied between the steps, so the
second step is taken on an arbitrary agreeing state (`hnext2`, `hnext2_out`). -/
theorem asmCaseTwoRegs (inst : HolInst 64)
    (t1 t2 : arm8_state) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst inst) s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hnext1 : arm8Next ms = t1)
    (hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2)
    (hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x)
    (hlen : (arm8Enc (.inst inst)).length = 8)
    (htok1 : arm8Ok t1 = true)
    (htpc1 : t1.PC = ms.PC + 4)
    (htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x)
    (htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst inst)).length s1.pc 0 →
      t1.MEM pc = ms.MEM pc)
    (htok2 : arm8Ok t2 = true)
    (htpc2 : t2.PC = ms.PC + 8)
    (htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x)
    (htregs : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false →
      t2.REG (BitVec.ofNat 5 k) = s2.regs k)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8)
    (hs2dom : s2.memDomain = s1.memDomain) :
    CaseGoal (.inst inst) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, _hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hq : targetStateRel arm8TargetL3 s2 t2 := by
    refine ⟨htok2, ?_, ?_, ?_, ?_⟩
    · change t2.PC = s2.pc
      rw [htpc2, hs2pc, hpc]
      simp
    · change ∀ a, s2.memDomain a → t2.MEM a = s2.mem a
      intro a ha
      exact htmemIn a (hs2dom ▸ ha)
    · change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
        t2.REG (BitVec.ofNat 5 k) = s2.regs k
      intro k hk
      exact htregs k hk.1 hk.2
    · intro k hk
      simp [arm8ConfigL3] at hk
  have hcode : allPcs (arm8Enc (.inst inst)).length s1.pc 0 ⊆ s1.memDomain :=
    bytesInMemory_allPcs (arm8Enc (.inst inst)) s1.pc s1.mem s1.memDomain 0 hs.1
  refine ⟨1, ?_⟩
  intro env henv
  have hagree0 : Arm8L3Agree s1.memDomain (env 0 t1) t1 := by
    rw [← arm8Proj_eq_iff]
    exact henv 0 t1
  constructor
  · change (arm8Ok (env 0 (arm8Next ms)) = true ∧
        (∀ pc, pc ∈ allPcs (arm8Enc (.inst inst)).length s1.pc 0 →
          (env 0 (arm8Next ms)).MEM pc = ms.MEM pc) ∧
        (env 0 (arm8Next ms)).PC ∈ allPcs (arm8Enc (.inst inst)).length s1.pc 2) ∧
      targetStateRel arm8TargetL3 s2 (env 1 (arm8Next (env 0 (arm8Next ms))))
    rw [hnext1]
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · rw [arm8Ok_congr hagree0]; exact htok1
      · intro pc hpc'
        exact (hagree0.mem pc (hcode hpc')).trans (htcode1 pc hpc')
      · rw [hagree0.pc, htpc1, hpc, hlen]
        simpa using mem_allPcs_eight_l3 s1.pc 1 (by norm_num)
    · have hmid : Arm8L3Agree s2.memDomain (env 1 (arm8Next (env 0 t1)))
          (arm8Next (env 0 t1)) := by
        rw [← arm8Proj_eq_iff, hs2dom]
        exact henv 1 _
      have hstep : Arm8L3Agree s2.memDomain (arm8Next (env 0 t1)) t2 := by
        rw [hs2dom]
        exact hnext2 (env 0 t1) hagree0
      exact targetStateRel_congr (hmid.trans hstep) hq
  · change (∀ x, ¬ s1.memDomain x → ms.MEM x = (arm8Next ms).MEM x) ∧
      (∀ x, ¬ s1.memDomain x →
        (env 0 (arm8Next ms)).MEM x = (arm8Next (env 0 (arm8Next ms))).MEM x) ∧ True
    rw [hnext1]
    refine ⟨?_, ?_, trivial⟩
    · intro x hx
      exact (htmem1 x hx).symm
    · intro x hx
      exact (hnext2_out (env 0 t1) hagree0 x hx).symm

/-- `asmCaseTwoRegs` when the lowering writes `v` into the single destination
register `r`. -/
theorem asmCaseTwoMem (inst : HolInst 64) (r : Nat) (v : BitVec 64)
    (t1 t2 : arm8_state) (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst inst) s2 ∧ targetStateRel arm8TargetL3 s1 ms)
    (hnext1 : arm8Next ms = t1)
    (hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2)
    (hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x)
    (hlen : (arm8Enc (.inst inst)).length = 8)
    (htok1 : arm8Ok t1 = true)
    (htpc1 : t1.PC = ms.PC + 4)
    (htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x)
    (htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst inst)).length s1.pc 0 →
      t1.MEM pc = ms.MEM pc)
    (htok2 : arm8Ok t2 = true)
    (htpc2 : t2.PC = ms.PC + 8)
    (htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x)
    (htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ r →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k))
    (htval : t2.REG (BitVec.ofNat 5 r) = v)
    (hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, s2.regs k = if k = r then v else s1.regs k) :
    CaseGoal (.inst inst) s1 s2 ms := by
  refine asmCaseTwoRegs inst t1 t2 s1 s2 ms h hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1
    htcode1 htok2 htpc2 htmemIn ?_ hs2pc hs2dom
  have hreg := h.2.2.2.2.1
  rw [arm8TargetL3_getReg] at hreg
  intro k hk hav
  by_cases hkr : k = r
  · rw [hkr, htval, hs2regs r, if_pos rfl]
  · rw [htreg k hk hav hkr, hs2regs k, if_neg hkr]
    exact hreg k ⟨hk, hav⟩
/-- `X` of the zero register is zero. -/
theorem arm8X_zero (st : arm8_state) : X (TN := 64) 31#5 st = (0 : BitVec 64) := by
  simp [X]

/-- Reading a non-`SP` register commutes with `Arm8L3Agree`. -/
theorem arm8X_congr {d : BitVec 64 → Prop} {s t : arm8_state} (h : Arm8L3Agree d s t)
    {n : BitVec 5} (hn : n ≠ 31#5) : X (TN := 64) n s = X (TN := 64) n t := by
  simp [X, h.reg, hn]

/-- The zero register reads as zero in every state, so `X` agrees there without
a register-agreement hypothesis. -/
theorem arm8X_congr_or_zero {d : BitVec 64 → Prop} {s t : arm8_state}
    (h : Arm8L3Agree d s t) (n : BitVec 5) : X (TN := 64) n s = X (TN := 64) n t := by
  by_cases hn : n = 31#5
  · rw [hn, arm8X_zero, arm8X_zero]
  · exact arm8X_congr h hn

/-- The zero register, written as the plain `31` numeral at width 5, reads as
zero. `rw` needs this form: the literal that `arm8_ast` puts into the state is
`OfNat.ofNat 31`, which is definitionally but not syntactically
`BitVec.ofNat 5 31`. -/
theorem arm8X_zero_ofNat (st : arm8_state) :
    X (TN := 64) (31 : BitVec 5) st = (0 : BitVec 64) := by
  show X (TN := 64) (BitVec.ofNat 5 31) st = (0 : BitVec 64)
  simp [X]

/-- `BitVec.ofNat 5` is injective on register numbers below 32. -/
theorem arm8Reg_eq {a b : Nat} (ha : a < 32) (hb : b < 32) :
    (BitVec.ofNat 5 a = BitVec.ofNat 5 b) ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
    have ha' : a % 2 ^ 5 = a := Nat.mod_eq_of_lt (by omega)
    have hb' : b % 2 ^ 5 = b := Nat.mod_eq_of_lt (by omega)
    omega
  · intro h; rw [h]

/-- The plain `0` numeral at width 64 is the additive identity, in the form `rw`
matches. -/
theorem arm8Zero_add (x : BitVec 64) : (0 : BitVec 64) + x = x := by
  show BitVec.ofNat 64 0 + x = x
  exact BitVec.zero_add x

/-- Splitting a wrapped address sum at a literal offset. -/
theorem bv_add_split (a : BitVec 64) (m k : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (m + k) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

end Flapjack.Compiler.Encoders.Arm8.L3

