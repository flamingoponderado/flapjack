import Flapjack.Compiler.Encoders.X64.Machine.StepAgree
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-!
# From an interference-free run to `encoder_correct` for the closed x86-64 target

This is the x86-64 analogue of `Flapjack/Mips32/TargetProof/Simulate.lean` and
`Flapjack/Compiler/Encoders/Arm8/Machine/Simulate.lean`.

`encoderCase` reduces one constructor of `encoder_correct x64Target` to facts
about the interference-free trajectory `x64Next^[k] ms`: every step stays
inside the source memory domain, the intermediate states satisfy the original
intermediate assertion, and the last state is related to the asm post-state.
Interference environments that preserve `x64Proj` are then handled once: a
projection-preserving step yields an agreeing state (`proj_eq_iff`), and
`next_agree'`/`x64Next_frame` carry agreement along the run.

The closed x86-64 model has no `trapped` field and no delay slot.  A single
`x64Next` step decodes and executes one instruction; a failed decode sets
`failed := true`, and a failed state stays failed.  `NextSafe` therefore asks
that the current state and its successor both stay inside the domain, which is
what the two-step `jumpCmp` expansion needs.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Congruence of the state predicate and the target relation -/

/-- `x64StateOk` only looks at the failure flag. -/
theorem x64StateOk_congr {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t) :
    x64StateOk s = x64StateOk t := by
  simp only [x64StateOk, h.failed]

/-- `targetStateRel x64Target` is invariant under agreement on `s2.memDomain`. -/
theorem targetStateRel_congr {s2 : AsmState 64} {s t : X64State}
    (h : X64Agree s2.memDomain s t)
    (ht : targetStateRel x64Target s2 t) : targetStateRel x64Target s2 s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact x64StateOk_congr h
  · rw [← h2]; exact h.pc
  · intro a ha; rw [← h3 a ha]; exact h.mem a ha
  · intro i hi
    have h4' : t.regs (num2Zreg i) = s2.regs i := by
      have := h4 i hi
      rw [x64Target_getReg] at this
      exact this
    show readReg s i = s2.regs i
    rw [readReg, h.regs (num2Zreg i)]
    exact h4'
  · intro i hi
    have h5' : (t.xmm (i % 8)).setWidth 64 = s2.fpRegs i := by
      have := h5 i hi
      rw [x64Target_getFpReg] at this
      exact this
    show (s.xmm (i % 8)).setWidth 64 = s2.fpRegs i
    rw [h.xmm (i % 8)]
    exact h5'

/-! ## `StepSafe` and the machine step -/

/-- The byte addresses an instruction touches depend only on the agreeing
state. -/
theorem x64Touched_congr {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (i : X64Insn) : x64Touched s i = x64Touched t i := by
  cases i with
  | nop n => rfl
  | movRR sz dst src => rfl
  | movRI sz dst imm => rfl
  | movRM sz dst base disp =>
      simp only [x64Touched, readReg]
      rw [h.regs (num2Zreg base)]
  | movMR sz src base disp =>
      simp only [x64Touched, readReg]
      rw [h.regs (num2Zreg base)]
  | movzxRM sz1 sz2 dst base disp =>
      simp only [x64Touched, readReg]
      rw [h.regs (num2Zreg base)]
  | binopRI op sz dst imm => rfl
  | binopRR op sz dst src => rfl
  | monop op sz dst => rfl
  | mul sz src => rfl
  | div sz src => rfl
  | cmc => rfl
  | setcc cond haveRex dst => rfl
  | jcc cond imm => rfl
  | jmp dst => rfl
  | lea sz dst disp => rfl
  | sse op =>
      cases op with
      | comisd dst src => rfl
      | movsd dst src => rfl
      | pcmpeqq dst src => rfl
      | psrlqImm dst imm => rfl
      | psllqImm dst imm => rfl
      | logicPD lop dst src => rfl
      | sqrtsd dst src => rfl
      | binSD bop dst src => rfl
      | movDQ toXmm quad xmm rm =>
          simp only [x64Touched]
          rw [effectiveAddress_congr h 0 rm]
      | cvtpd2dq truncate dst src => rfl
      | pslldq dst imm => rfl
      | psrldq dst imm => rfl
      | cvtdq2pd dst src => rfl

/-- `StepSafe` is preserved when the state is replaced by an agreeing one. -/
theorem StepSafe.of_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (hs : StepSafe d t) : StepSafe d s := by
  obtain ⟨insn, len, hdec_t, hfetch_t, htouch_t⟩ := hs
  have hmem : ∀ j, j < len →
      s.mem (s.pc + BitVec.ofNat 64 j) = t.mem (t.pc + BitVec.ofNat 64 j) := by
    intro j hj
    show s.mem (s.pc + BitVec.ofNat 64 j) = t.mem (t.pc + BitVec.ofNat 64 j)
    rw [h.pc]
    exact h.mem _ (hfetch_t j hj)
  have hdec_s : decode (fun k => s.mem (s.pc + BitVec.ofNat 64 k)) = some (insn, len) :=
    decode_congr_upto (fun k => t.mem (t.pc + BitVec.ofNat 64 k))
      (fun k => s.mem (s.pc + BitVec.ofNat 64 k)) insn len hdec_t
      (fun j hj => (hmem j hj).symm)
  refine ⟨insn, len, hdec_s, ?_, ?_⟩
  · intro j hj
    have hd_t : d (t.pc + BitVec.ofNat 64 j) := hfetch_t j hj
    rw [h.pc]
    exact hd_t
  · intro a ha
    rw [x64Touched_congr h insn] at ha
    exact htouch_t a ha

/-- A run stays inside `d`: the current state and its successor both stay
inside `d`. -/
def NextSafe (d : BitVec 64 → Prop) (s : X64State) : Prop :=
  StepSafe d s ∧ StepSafe d (x64Next s)

/-- `NextSafe` is preserved when the state is replaced by an agreeing one. -/
theorem NextSafe.of_agree {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (hs : NextSafe d t) : NextSafe d s := by
  have ha : X64Agree d (x64Next s) (x64Next t) := (x64Next_agree h.symm hs.1).symm
  exact ⟨StepSafe.of_agree h hs.1, StepSafe.of_agree ha hs.2⟩

/-- One `x64Next` step preserves agreement on `d` when the run stays inside `d`. -/
theorem next_agree' {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (hs : NextSafe d t) : X64Agree d (x64Next s) (x64Next t) :=
  (x64Next_agree h.symm hs.1).symm

/-! ## The assertion chains along a run -/

/-- The assertion chain of `encoder_correct`, along any step function that
agrees with `x64Next`, from a state agreeing with the start of an
interference-free run. -/
theorem asserts_of_run {d : BitVec 64 → Prop} {P Q : X64State → Prop}
    (hP : ∀ s t, X64Agree d s t → P t → P s) (hQ : ∀ s t, X64Agree d s t → Q t → Q s)
    (f : Nat → X64State → X64State) (hf : ∀ k x, X64Agree d (f k x) (x64Next x)) :
    ∀ (m : Nat) (u t : X64State), X64Agree d u t →
      (∀ k ≤ m, NextSafe d (x64Next^[k] t)) →
      (∀ k, 1 ≤ k → k ≤ m → P (x64Next^[k] t)) → Q (x64Next^[m + 1] t) →
      asserts m f u P Q := by
  intro m
  induction m with
  | zero =>
    intro u t hut hsafe _ hq
    exact hQ _ _ ((hf 0 u).trans (next_agree' hut (hsafe 0 (Nat.le_refl 0)))) hq
  | succ m ih =>
    intro u t hut hsafe hp hq
    have h1 : X64Agree d (f (m + 1) u) (x64Next t) :=
      (hf (m + 1) u).trans (next_agree' hut (hsafe 0 (Nat.zero_le _)))
    refine ⟨hP _ _ h1 (hp 1 (Nat.le_refl 1) (by omega)), ?_⟩
    apply ih _ _ h1
    · intro k hk
      have := hsafe (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · intro k hk1 hk2
      have := hp (k + 1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · rwa [← Function.iterate_succ_apply]

/-- The frame chain of `encoder_correct`: no step writes outside `d`. -/
theorem asserts2_of_run {d : BitVec 64 → Prop}
    (fi : Nat → X64State → X64State) (hfi : ∀ k x, X64Agree d (fi k x) x) :
    ∀ (m : Nat) (u t : X64State), X64Agree d u t →
      (∀ k < m, NextSafe d (x64Next^[k] t)) →
      asserts2 m fi x64Next u
        (fun ms1 ms2 => ∀ x, ¬ d x → ms1.mem x = ms2.mem x) := by
  intro m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro u t hut hsafe
    have hs0 := hsafe 0 (Nat.zero_lt_succ _)
    refine ⟨fun x hx => (x64Next_frame (NextSafe.of_agree hut hs0).1 x hx).symm, ?_⟩
    apply ih _ (x64Next t) ((hfi (m + 1) _).trans (next_agree' hut hs0))
    intro k hk
    have := hsafe (k + 1) (by omega)
    rwa [Function.iterate_succ_apply] at this

/-! ## The per-instruction goal -/

/-- The conclusion of `encoder_correct` for one source instruction (the body of
`encoderCorrect`, at `x64Target`). -/
def CaseGoal (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State) : Prop :=
  ∃ n : Nat, ∀ env : Nat → X64State → X64State,
    interferenceOk env (x64Target.proj s1.memDomain) →
    let pcs := allPcs (x64Target.config.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (x64Target.next s)) ms
        (fun ms' => x64Target.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → x64Target.getByte ms' pc = x64Target.getByte ms pc) ∧
          x64Target.getPc ms' ∈ pcs x64Target.config.codeAlignment)
        (fun ms' => targetStateRel x64Target s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) x64Target.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          x64Target.getByte ms1 x = x64Target.getByte ms2 x)

/-- One constructor of `encoder_correct x64Target`, from its interference-free
run of `n + 1` steps. -/
theorem encoderCase (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State) (n : Nat)
    (hdom : s2.memDomain = s1.memDomain)
    (hcode : allPcs (x64Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain)
    (hsafe : ∀ k ≤ n, NextSafe s1.memDomain (x64Next^[k] ms))
    (hp : ∀ k, 1 ≤ k → k ≤ n →
      x64StateOk (x64Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (x64Target.config.encode i).length s1.pc 0 →
        (x64Next^[k] ms).mem pc = ms.mem pc) ∧
      (x64Next^[k] ms).pc ∈
        allPcs (x64Target.config.encode i).length s1.pc x64Target.config.codeAlignment)
    (hq : targetStateRel x64Target s2 (x64Next^[n + 1] ms)) :
    CaseGoal i s1 s2 ms := by
  refine ⟨n, fun env henv => ?_⟩
  have hagree : ∀ k x, X64Agree s1.memDomain (env k x) x :=
    fun k x => (proj_eq_iff _ _ _).1 (henv k x)
  constructor
  · apply asserts_of_run (d := s1.memDomain) _ _ _ _ n ms ms (X64Agree.refl _ _) hsafe hp
    · exact hq
    · rintro s t hst ⟨h1, h2, h3⟩
      refine ⟨?_, fun pc hpc => ?_, ?_⟩
      · change x64StateOk s = true
        rw [x64StateOk_congr hst]; exact h1
      · change s.mem pc = ms.mem pc
        rw [hst.mem pc (hcode hpc)]; exact h2 pc hpc
      · change s.pc ∈ _
        rw [hst.pc]; exact h3
    · intro s t hst ht
      exact targetStateRel_congr (hdom ▸ hst) ht
    · intro k x
      exact hagree _ _
  · exact asserts2_of_run (d := s1.memDomain) _ (fun k x => hagree _ _) (n + 1) ms ms
      (X64Agree.refl _ _) (fun k hk => hsafe k (by omega))


/-- One `x64Next` step preserves agreement on `d` from a state that steps
inside `d`. -/
theorem next_agree_step {d : BitVec 64 → Prop} {s t : X64State} (h : X64Agree d s t)
    (hs : StepSafe d t) : X64Agree d (x64Next s) (x64Next t) :=
  (x64Next_agree h.symm hs).symm

/-! ## The `StepSafe` chain used by the control-flow and multi-step cases -/

/-- The assertion chain of `encoder_correct`, along any step function that
agrees with `x64Next`, from a state agreeing with the start of an
interference-free run that is `StepSafe` at every simulated step. -/
theorem asserts_of_run_step {d : BitVec 64 → Prop} {P Q : X64State → Prop}
    (hP : ∀ s t, X64Agree d s t → P t → P s) (hQ : ∀ s t, X64Agree d s t → Q t → Q s)
    (f : Nat → X64State → X64State) (hf : ∀ k x, X64Agree d (f k x) (x64Next x)) :
    ∀ (m : Nat) (u t : X64State), X64Agree d u t →
      (∀ k ≤ m, StepSafe d (x64Next^[k] t)) →
      (∀ k, 1 ≤ k → k ≤ m → P (x64Next^[k] t)) → Q (x64Next^[m + 1] t) →
      asserts m f u P Q := by
  intro m
  induction m with
  | zero =>
    intro u t hut hsafe _ hq
    exact hQ _ _ ((hf 0 u).trans (next_agree_step hut (hsafe 0 (Nat.le_refl 0)))) hq
  | succ m ih =>
    intro u t hut hsafe hp hq
    have h1 : X64Agree d (f (m + 1) u) (x64Next t) :=
      (hf (m + 1) u).trans (next_agree_step hut (hsafe 0 (Nat.zero_le _)))
    refine ⟨hP _ _ h1 (hp 1 (Nat.le_refl 1) (by omega)), ?_⟩
    apply ih _ _ h1
    · intro k hk
      have := hsafe (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · intro k hk1 hk2
      have := hp (k + 1) (by omega) (by omega)
      rwa [Function.iterate_succ_apply] at this
    · rwa [← Function.iterate_succ_apply]

/-- `asserts2_of_run` with `StepSafe` along the run instead of `NextSafe`. -/
theorem asserts2_of_run_step {d : BitVec 64 → Prop}
    (fi : Nat → X64State → X64State) (hfi : ∀ k x, X64Agree d (fi k x) x) :
    ∀ (m : Nat) (u t : X64State), X64Agree d u t →
      (∀ k < m, StepSafe d (x64Next^[k] t)) →
      asserts2 m fi x64Next u
        (fun ms1 ms2 => ∀ x, ¬ d x → ms1.mem x = ms2.mem x) := by
  intro m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro u t hut hsafe
    have hs0 := hsafe 0 (Nat.zero_lt_succ _)
    refine ⟨fun x hx => (x64Next_frame (StepSafe.of_agree hut hs0) x hx).symm, ?_⟩
    exact ih _ (x64Next t) ((hfi (m + 1) _).trans (next_agree_step hut hs0))
      (fun k hk => by
        have := hsafe (k + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)

/-- One constructor of `encoder_correct x64Target` from its interference-free
run of `n + 1` steps, with `StepSafe` (not `NextSafe`) along the run.  This is
what control flow and multi-instruction lowerings use: their successor's bytes
need not be in the source domain. -/
theorem encoderCaseStep (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : X64State) (n : Nat)
    (hdom : s2.memDomain = s1.memDomain)
    (hcode : allPcs (x64Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain)
    (hsafe : ∀ k ≤ n, StepSafe s1.memDomain (x64Next^[k] ms))
    (hp : ∀ k, 1 ≤ k → k ≤ n →
      x64StateOk (x64Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (x64Target.config.encode i).length s1.pc 0 →
        (x64Next^[k] ms).mem pc = ms.mem pc) ∧
      (x64Next^[k] ms).pc ∈
        allPcs (x64Target.config.encode i).length s1.pc x64Target.config.codeAlignment)
    (hq : targetStateRel x64Target s2 (x64Next^[n + 1] ms)) :
    CaseGoal i s1 s2 ms := by
  refine ⟨n, fun env henv => ?_⟩
  have hagree : ∀ k x, X64Agree s1.memDomain (env k x) x :=
    fun k x => (proj_eq_iff _ _ _).1 (henv k x)
  constructor
  · apply asserts_of_run_step (d := s1.memDomain) _ _ _ _ n ms ms (X64Agree.refl _ _) hsafe hp
    · exact hq
    · rintro s t hst ⟨h1, h2, h3⟩
      refine ⟨?_, fun pc hpc => ?_, ?_⟩
      · change x64StateOk s = true
        rw [x64StateOk_congr hst]; exact h1
      · change s.mem pc = ms.mem pc
        rw [hst.mem pc (hcode hpc)]; exact h2 pc hpc
      · change s.pc ∈ _
        rw [hst.pc]; exact h3
    · intro s t hst ht
      exact targetStateRel_congr (hdom ▸ hst) ht
    · intro k x
      exact hagree _ _
  · exact asserts2_of_run_step (d := s1.memDomain) _ (fun k x => hagree _ _) (n + 1) ms ms
      (X64Agree.refl _ _) (fun k hk => hsafe k (by omega))

end Flapjack.Compiler.Encoders.X64
