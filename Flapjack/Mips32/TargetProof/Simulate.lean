import Flapjack.Mips32.TargetProof.Agree
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-! # From an interference-free run to `encoder_correct`

`encoderCase` reduces one constructor of `encoder_correct mips32Target` to facts about the
interference-free trajectory `mips32Next^[k] ms`: every step stays inside the source memory
domain, the intermediate states satisfy the original intermediate assertion, and the last
state is related to the asm post-state. Interference environments that preserve
`mips32Proj` are then handled once: a projection-preserving step yields an agreeing state
(`proj_eq_iff`), and `next_agree`/`next_frame` carry agreement along the run. -/

namespace Flapjack.Mips32.TargetProof
open ZirenDet.Isa Flapjack Flapjack.Mips32 Flapjack.Compiler.Encoders.Mips32
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps

theorem StepSafe.of_agree {d : W → Prop} {s t : State} (h : Agree d s t) (hs : StepSafe d t) :
    StepSafe d s := by
  have hw : s.mem.readWord s.pc = t.mem.readWord t.pc := by
    rw [h.pc]; exact readWord_congr t.pc (fun a ha => h.mem a ha) hs.1
  refine ⟨h.pc ▸ hs.1, fun i hi => ?_⟩
  have hreg : s.reg = t.reg := funext h.reg
  have ht : touched s i = touched t i := by cases i <;> simp [touched, hreg]
  rw [ht]; exact hs.2 i (hw ▸ hi)

theorem NextSafe.of_agree {d : W → Prop} {s t : State} (h : Agree d s t) (hs : NextSafe d t) :
    NextSafe d s := by
  intro hs'
  obtain ⟨h1, h2⟩ := hs (h.trapped ▸ hs')
  have ha := fetchExec_agree h.symm h1
  refine ⟨StepSafe.of_agree h h1, fun ht hn => ?_⟩
  exact StepSafe.of_agree ha.symm (h2 (ha.trapped ▸ ht) (ha.nextPc ▸ ha.pc ▸ hn))

theorem next_agree' {d : W → Prop} {s t : State} (h : Agree d s t) (hs : NextSafe d t) :
    Agree d (mips32Next s) (mips32Next t) :=
  (next_agree h.symm hs).symm

/-- The assertion chain of `encoder_correct`, along any step function that agrees with
`mips32Next`, from a state agreeing with the start of an interference-free run. -/
theorem asserts_of_run {d : W → Prop} {P Q : State → Prop}
    (hP : ∀ s t, Agree d s t → P t → P s) (hQ : ∀ s t, Agree d s t → Q t → Q s)
    (f : Nat → State → State) (hf : ∀ k x, Agree d (f k x) (mips32Next x)) :
    ∀ (m : Nat) (u t : State), Agree d u t →
      (∀ k ≤ m, NextSafe d (mips32Next^[k] t)) →
      (∀ k, 1 ≤ k → k ≤ m → P (mips32Next^[k] t)) → Q (mips32Next^[m + 1] t) →
      asserts m f u P Q := by
  intro m
  induction m with
  | zero =>
    intro u t hut hsafe _ hq
    exact hQ _ _ ((hf 0 u).trans (next_agree' hut (hsafe 0 (Nat.le_refl 0)))) hq
  | succ m ih =>
    intro u t hut hsafe hp hq
    have h1 : Agree d (f (m + 1) u) (mips32Next t) :=
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
theorem asserts2_of_run {d : W → Prop}
    (fi : Nat → State → State) (hfi : ∀ k x, Agree d (fi k x) x) :
    ∀ (m : Nat) (u t : State), Agree d u t →
      (∀ k < m, NextSafe d (mips32Next^[k] t)) →
      asserts2 m fi mips32Next u
        (fun ms1 ms2 => ∀ x, ¬ d x → ms1.mem.readByte x = ms2.mem.readByte x) := by
  intro m
  induction m with
  | zero => intros; trivial
  | succ m ih =>
    intro u t hut hsafe
    have hs0 := hsafe 0 (Nat.zero_lt_succ _)
    refine ⟨fun x hx => (next_frame u (NextSafe.of_agree hut hs0) x hx).symm, ?_⟩
    apply ih _ (mips32Next t) ((hfi (m + 1) _).trans (next_agree' hut hs0))
    intro k hk
    have := hsafe (k + 1) (by omega)
    rwa [Function.iterate_succ_apply] at this

/-- The conclusion of `encoder_correct` for one source instruction (the body of
`encoderCorrect`, at `mips32Target`). -/
def CaseGoal (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State) : Prop :=
  ∃ n : Nat, ∀ env : Nat → State → State,
    interferenceOk env (mips32Target.proj s1.memDomain) →
    let pcs := allPcs (mips32Target.config.encode i).length s1.pc
    asserts n (fun k s => env (n - k) (mips32Target.next s)) ms
        (fun ms' => mips32Target.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → mips32Target.getByte ms' pc = mips32Target.getByte ms pc) ∧
          mips32Target.getPc ms' ∈ pcs mips32Target.config.codeAlignment)
        (fun ms' => targetStateRel mips32Target s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) mips32Target.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          mips32Target.getByte ms1 x = mips32Target.getByte ms2 x)

theorem mips32Ok_congr {d : W → Prop} {s t : State} (h : Agree d s t) :
    mips32Ok s = mips32Ok t := by
  simp [mips32Ok, h.pc, h.nextPc, h.trapped]

theorem targetStateRel_congr {s2 : AsmState 32} {s t : State} (h : Agree s2.memDomain s t)
    (ht : targetStateRel mips32Target s2 t) : targetStateRel mips32Target s2 s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1]; exact mips32Ok_congr h
  · rw [← h2]; exact h.pc
  · intro a ha; rw [← h3 a ha]; exact h.mem a ha
  · intro i hi; rw [← h4 i hi]; exact h.reg _
  · exact h5

/-- One constructor of `encoder_correct mips32Target`, from its interference-free run of
`n + 1` steps. -/
theorem encoderCase (i : HolAsm 32) (s1 s2 : AsmState 32) (ms : State) (n : Nat)
    (hdom : s2.memDomain = s1.memDomain)
    (hcode : allPcs (mips32Enc i).length s1.pc 0 ⊆ s1.memDomain)
    (hsafe : ∀ k ≤ n, NextSafe s1.memDomain (mips32Next^[k] ms))
    (hp : ∀ k, 1 ≤ k → k ≤ n →
      mips32Ok (mips32Next^[k] ms) = true ∧
      (∀ pc, pc ∈ allPcs (mips32Enc i).length s1.pc 0 →
        (mips32Next^[k] ms).mem.readByte pc = ms.mem.readByte pc) ∧
      (mips32Next^[k] ms).pc ∈ allPcs (mips32Enc i).length s1.pc 2)
    (hq : targetStateRel mips32Target s2 (mips32Next^[n + 1] ms)) :
    CaseGoal i s1 s2 ms := by
  refine ⟨n, fun env henv => ?_⟩
  have hagree : ∀ k x, Agree s1.memDomain (env k x) x :=
    fun k x => (proj_eq_iff _ _ _).1 (henv k x)
  constructor
  · apply asserts_of_run (d := s1.memDomain) _ _ _ _ n ms ms (Agree.refl _ _) hsafe hp
    · exact hq
    · rintro s t hst ⟨h1, h2, h3⟩
      refine ⟨?_, fun pc hpc => ?_, ?_⟩
      · change mips32Ok s = true; rw [mips32Ok_congr hst]; exact h1
      · change s.mem.readByte pc = ms.mem.readByte pc
        rw [hst.mem pc (hcode hpc)]; exact h2 pc hpc
      · change s.pc ∈ _; rw [hst.pc]; exact h3
    · intro s t hst ht
      exact targetStateRel_congr (hdom ▸ hst) ht
    · intro k x
      exact hagree _ _
  · exact asserts2_of_run (d := s1.memDomain) _ (fun k x => hagree _ _) (n + 1) ms ms
      (Agree.refl _ _) (fun k hk => hsafe k (by omega))

end Flapjack.Mips32.TargetProof
