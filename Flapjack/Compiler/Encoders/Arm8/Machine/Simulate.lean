import Flapjack.Compiler.Encoders.Arm8.Machine.StepAgree
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-! # From an interference-free run to `encoder_correct` for the closed ARMv8 target

This is the ARM8 analogue of `Flapjack/Mips32/TargetProof/Simulate.lean`. The
closed ARM8 model has no `trapped` field and no delay slot: `arm8Next` performs
exactly one decode-and-execute step, and a state that cannot decode simply gets
`failed := true`. MIPS's `NextSafe` guards its `StepSafe` conjunct by
`s.trapped = false` because a stopped MIPS machine stays put, so the step fact
is not needed there. `arm8Next` always steps, so the ARM8 analogue keeps the
step-safety conjunct unconditional; guarding it would make `next_agree'`
unprovable at `failed` states and would lose the facts the run needs. The
delay-slot conjunct is kept with the analogous `failed` control condition even
though it is vacuous for the one-instruction ARM8 step. See `NextSafe` below.

`encoderCase` reduces one constructor of `encoder_correct arm8Target` to facts
about the interference-free trajectory `arm8Next^[k] ms`: every step stays
inside the source memory domain, the intermediate states satisfy the original
intermediate assertion, and the last state is related to the asm post-state.
Interference environments that preserve `arm8Proj` are then handled once: a
projection-preserving step yields an agreeing state (`arm8Proj_eq_iff`), and
`next_agree'`/`arm8Next_frame` carry agreement along the run. -/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## Congruence of the state predicate and the target relation -/

/-- `arm8StateOk` only looks at the PC and the failure flag. -/
theorem arm8StateOk_congr {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t) :
    arm8StateOk s = arm8StateOk t := by
  simp only [arm8StateOk, h.pc, h.failed]

/-- `targetStateRel arm8Target` is invariant under agreement on `s2.memDomain`. -/
theorem targetStateRel_congr {s2 : AsmState 64} {s t : Arm8State}
    (h : Arm8Agree s2.memDomain s t)
    (ht : targetStateRel arm8Target s2 t) : targetStateRel arm8Target s2 s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact arm8StateOk_congr h
  · rw [← h2]; exact h.pc
  · intro a ha; rw [← h3 a ha]; exact h.mem a ha
  · intro i hi; simpa only [arm8Target_getReg, h.regs] using h4 i hi
  · intro i hi
    simp [arm8Config] at hi

/-! ## `StepSafe` and the machine step -/

/-- Register reads only depend on the register file. -/
theorem readReg_congr {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (r : Nat) : readReg s r = readReg t r := by
  simp only [readReg, h.regs]

/-- The bytes an instruction touches only depend on the register file. -/
theorem arm8Touched_congr {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (i : Insn) : arm8Touched s i = arm8Touched t i := by
  cases i <;> simp only [arm8Touched, readReg_congr h]

/-- `StepSafe` is preserved when the state is replaced by an agreeing one. -/
theorem StepSafe.of_agree {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : StepSafe d t) : StepSafe d s := by
  refine ⟨?_, fun i hi x hx => ?_⟩
  · simpa only [FetchSafe, arm8FetchBytes, h.pc] using hs.1
  · have hw : fetchWord t = fetchWord s := fetchWord_congr h.symm hs.1
    exact hs.2 i (by rw [hw]; exact hi) x (arm8Touched_congr h i ▸ hx)

/-- `arm8Next` stays inside `d`.  This is the ARM8 analogue of the MIPS
`NextSafe`, with two documented differences.  MIPS guards `StepSafe` by
`s.trapped = false` because a stopped MIPS machine stays put; the closed ARM8
machine has no stopped state (`arm8Next` always decodes and executes, and a
failed decode merely sets `failed`), so a guarded step-safety fact would say
nothing about `failed` states and `next_agree'` would be unprovable there.
The first conjunct is therefore unconditional.  The MIPS delay-slot conjunct is
kept verbatim with the analogous `failed` control condition, although it is
vacuous for the one-instruction ARM8 step. -/
def NextSafe (d : BitVec 64 → Prop) (s : Arm8State) : Prop :=
  StepSafe d s ∧
    ((arm8Next s).failed = false → (arm8Next s).pc ≠ s.pc + 4 →
      StepSafe d (arm8Next s))

/-- The literal MIPS-shaped guarded reading of `NextSafe`: whenever the state has
not failed, the step-safety conjunct and the delay-slot conjunct hold.  This is
the exact shape MIPS's `NextSafe` has under `trapped = false`; the definition
above carries the first conjunct unconditionally because the closed ARM8 machine
never stops. -/
theorem NextSafe.guarded {d : BitVec 64 → Prop} {s : Arm8State} (hs : NextSafe d s) :
    s.failed = false → StepSafe d s ∧
      ((arm8Next s).failed = false → (arm8Next s).pc ≠ s.pc + 4 →
        StepSafe d (arm8Next s)) :=
  fun _ => ⟨hs.1, hs.2⟩

/-- `NextSafe` is preserved when the state is replaced by an agreeing one. -/
theorem NextSafe.of_agree {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : NextSafe d t) : NextSafe d s := by
  have ha : Arm8Agree d (arm8Next s) (arm8Next t) := (arm8Next_agree h.symm hs.1).symm
  refine ⟨StepSafe.of_agree h hs.1, fun ht hn => ?_⟩
  refine StepSafe.of_agree ha (hs.2 (ha.failed ▸ ht) ?_)
  rw [← ha.pc, ← h.pc]
  exact hn

/-- One `arm8Next` step preserves agreement on `d` when the run stays inside `d`. -/
theorem next_agree' {d : BitVec 64 → Prop} {s t : Arm8State} (h : Arm8Agree d s t)
    (hs : NextSafe d t) : Arm8Agree d (arm8Next s) (arm8Next t) :=
  (arm8Next_agree h.symm hs.1).symm

/-! ## The assertion chains along a run -/

/-- The assertion chain of `encoder_correct`, along any step function that agrees with
`arm8Next`, from a state agreeing with the start of an interference-free run. -/
theorem asserts_of_run {d : BitVec 64 → Prop} {P Q : Arm8State → Prop}
    (hP : ∀ s t, Arm8Agree d s t → P t → P s) (hQ : ∀ s t, Arm8Agree d s t → Q t → Q s)
    (f : Nat → Arm8State → Arm8State) (hf : ∀ k x, Arm8Agree d (f k x) (arm8Next x)) :
    ∀ (m : Nat) (u t : Arm8State), Arm8Agree d u t →
      (∀ k ≤ m, NextSafe d (arm8Next^[k] t)) →
      (∀ k, 1 ≤ k → k ≤ m → P (arm8Next^[k] t)) → Q (arm8Next^[m + 1] t) →
      asserts m f u P Q := by
  intro m
  induction m with
  | zero =>
    intro u t hut hsafe _ hq
    exact hQ _ _ ((hf 0 u).trans (next_agree' hut (hsafe 0 (Nat.le_refl 0)))) hq
  | succ m ih =>
    intro u t hut hsafe hp hq
    have h1 : Arm8Agree d (f (m + 1) u) (arm8Next t) :=
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
    (fi : Nat → Arm8State → Arm8State) (hfi : ∀ k x, Arm8Agree d (fi k x) x) :
    ∀ (m : Nat) (u t : Arm8State), Arm8Agree d u t →
      (∀ k < m, NextSafe d (arm8Next^[k] t)) →
      asserts2 m fi arm8Next u
        (fun ms1 ms2 => ∀ x, ¬ d x → ms1.mem x = ms2.mem x) := by
  intro m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro u t hut hsafe
    have hs0 := hsafe 0 (Nat.zero_lt_succ _)
    refine ⟨fun x hx => (arm8Next_frame u (NextSafe.of_agree hut hs0).1 x hx).symm, ?_⟩
    apply ih _ (arm8Next t) ((hfi (m + 1) _).trans (next_agree' hut hs0))
    intro k hk
    have := hsafe (k + 1) (by omega)
    rwa [Function.iterate_succ_apply] at this

/-! ## The per-instruction goal -/

/-- The conclusion of `encoder_correct` for one source instruction (the body of
`encoderCorrect`, at `arm8Target`). -/
def CaseGoal (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State) : Prop :=
  ∃ n : Nat, ∀ env : Nat → Arm8State → Arm8State,
    interferenceOk env (arm8Target.proj s1.memDomain) →
    let pcs := allPcs (arm8Target.config.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (arm8Target.next s)) ms
        (fun ms' => arm8Target.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → arm8Target.getByte ms' pc = arm8Target.getByte ms pc) ∧
          arm8Target.getPc ms' ∈ pcs arm8Target.config.codeAlignment)
        (fun ms' => targetStateRel arm8Target s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) arm8Target.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          arm8Target.getByte ms1 x = arm8Target.getByte ms2 x)

/-- One constructor of `encoder_correct arm8Target`, from its interference-free run of
`n + 1` steps. -/
theorem encoderCase (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : Arm8State) (n : Nat)
    (hdom : s2.memDomain = s1.memDomain)
    (hcode : allPcs (arm8Target.config.encode i).length s1.pc 0 ⊆ s1.memDomain)
    (hsafe : ∀ k ≤ n, NextSafe s1.memDomain (arm8Next^[k] ms))
    (hp : ∀ k, 1 ≤ k → k ≤ n →
      arm8StateOk (arm8Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (arm8Target.config.encode i).length s1.pc 0 →
        (arm8Next^[k] ms).mem pc = ms.mem pc) ∧
      (arm8Next^[k] ms).pc ∈
        allPcs (arm8Target.config.encode i).length s1.pc arm8Target.config.codeAlignment)
    (hq : targetStateRel arm8Target s2 (arm8Next^[n + 1] ms)) :
    CaseGoal i s1 s2 ms := by
  refine ⟨n, fun env henv => ?_⟩
  have hagree : ∀ k x, Arm8Agree s1.memDomain (env k x) x :=
    fun k x => (arm8Proj_eq_iff _ _ _).1 (henv k x)
  constructor
  · apply asserts_of_run (d := s1.memDomain) _ _ _ _ n ms ms (Arm8Agree.refl _ _) hsafe hp
    · exact hq
    · rintro s t hst ⟨h1, h2, h3⟩
      refine ⟨?_, fun pc hpc => ?_, ?_⟩
      · change arm8StateOk s = true
        rw [arm8StateOk_congr hst]; exact h1
      · change s.mem pc = ms.mem pc
        rw [hst.mem pc (hcode hpc)]; exact h2 pc hpc
      · change s.pc ∈ _
        rw [hst.pc]; exact h3
    · intro s t hst ht
      exact targetStateRel_congr (hdom ▸ hst) ht
    · intro k x
      exact hagree _ _
  · exact asserts2_of_run (d := s1.memDomain) _ (fun k x => hagree _ _) (n + 1) ms ms
      (Arm8Agree.refl _ _) (fun k hk => hsafe k (by omega))

end Flapjack.Compiler.Encoders.Arm8
