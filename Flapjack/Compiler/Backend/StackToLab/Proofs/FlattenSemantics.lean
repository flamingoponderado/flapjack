import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics
import Flapjack.Compiler.Backend.LabSem.Semantics
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClockIoEventsMono
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClockIoEventsMono
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper

/-! `flatten_semantics`
(`stack_to_labProofScript.sml:2827-3025`): under the halting assumption for
procedure 1, the LabSem semantics of the flattened code equals the StackSem
semantics of the start call. Both semantics are rewritten as the
`semantics_wrapper` of their clock-indexed entry runs (the LabSem family
shifted by the call's clock tick) and compared by `semantics_wrapper_eq`. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

open Classical in
/-- The StackSem entry-run classification matching `stackSem$semantics_def`
(Flapjack infrastructure). -/
noncomputable def stackEntryClass {width : Nat} [NeZero width] :
    Option (StackSemResult width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFFI e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.halt (.word w)) =>
      .CompleteResult (if w = 0 then HolOutcome.success else HolOutcome.resourceLimitHit)
  | some (.result r) => if r = .loc 1 0 then .CompleteResult HolOutcome.success else .RunError
  | _ => .RunError

/-- The LabSem run classification matching `labSem$semantics_def`
(Flapjack infrastructure). -/
def labEntryClass : MachineResult → CrepToLoopSemanticsRunRes HolOutcome
  | .halt o => .CompleteResult o
  | .timeOut => .Incomplete
  | .error => .RunError

/-- Clock-indexed StackSem entry runs. -/
noncomputable def stackRuns {width : Nat} [NeZero width] {C F : Type} (start : Nat)
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent :=
  Prod.map stackEntryClass (fun t : StackSemStateFiniteExact width C F => t.ffi.ioEvents)
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }))

/-- Clock-indexed LabSem runs, shifted by the tick of the StackSem entry call. -/
noncomputable def labRuns {width : Nat} [NeZero width] {C F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) (k : Nat) :
    CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent :=
  Prod.map labEntryClass
    (fun t : Flapjack.Compiler.Backend.LabSem.State width C F => t.ffi.ioEvents)
    (evaluate { t with clock := k - 1 })

/-- `stackSem$semantics_def` as the `semantics_wrapper` of its entry runs. -/
theorem stackSemIsWrapper {width : Nat} [NeZero width] {C F : Type} (start : Nat)
    (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.semantics start s = crepToLoopSemanticsWrapper (stackRuns start s) := by
  have hk : ∀ k, (let res := (StackSemEvaluate.evaluate
        ((.call none (.inl start) none : HolProg width), { s with clock := k })).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w : BitVec width, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e)) ↔
      ∃ v, stackRuns start s k = (.RunError, v) := by
    intro k
    simp only [stackRuns]
    generalize StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k }) = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (v | v | _ | _ | v | _ | _ | _)
    all_goals try (rcases v with v | ⟨a, b⟩)
    all_goals simp [stackEntryClass]
  unfold StackSemEvaluate.semantics crepToLoopSemanticsWrapper
  simp only
  by_cases hf : ∃ k, (let res := (StackSemEvaluate.evaluate
        ((.call none (.inl start) none : HolProg width), { s with clock := k })).1
      res ≠ some .timeOut ∧ res ≠ some (.result (.loc 1 0)) ∧
      (∀ w : BitVec width, res ≠ some (.halt (.word w))) ∧ ∀ e, res ≠ some (.finalFFI e))
  · rw [if_pos hf, if_pos ((exists_congr hk).1 hf)]
  · rw [if_neg hf, if_neg (fun h => hf ((exists_congr hk).2 h))]
    congr 2
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
      refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
      have hnf := fun h => hf ⟨k, h⟩
      simp only [stackRuns, he] at hnf ⊢
      rcases r with v | v | _ | _ | v | _ | e | _ <;> (try rcases v with w | ⟨a, b⟩) <;>
        simp_all [stackEntryClass]
    · rintro ⟨k, r', ev, hfk, rfl⟩
      simp only [stackRuns] at hfk
      rcases he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k }) with ⟨r, t⟩
      rw [he] at hfk
      simp only [Prod.map, Prod.mk.injEq] at hfk
      obtain ⟨hg, rfl⟩ := hfk
      rcases r with _ | r
      · simp [stackEntryClass] at hg
      refine ⟨k, t, r, r', he, ?_, rfl⟩
      rcases r with v | v | _ | _ | v | _ | e | _ <;> (try rcases v with w | ⟨a, b⟩) <;>
        simp [stackEntryClass] at hg ⊢
      all_goals (try split at hg) <;> simp_all

/-- `labSem$semantics_def` as the `semantics_wrapper` of its runs, shifted by
one clock tick. -/
theorem labSemIsWrapper {width : Nat} [NeZero width] {C F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) :
    semantics t = crepToLoopSemanticsWrapper (labRuns t) := by
  have run : ∀ c, labRuns t (c + 1) = Prod.map labEntryClass
      (fun t : Flapjack.Compiler.Backend.LabSem.State width C F => t.ffi.ioEvents)
      (evaluate { t with clock := c }) := fun c => by simp [labRuns]
  have hf : (∃ clock, (evaluate { t with clock := clock }).1 = .error) ↔
      ∃ k v, labRuns t k = (.RunError, v) := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c + 1, (evaluate { t with clock := c }).2.ffi.ioEvents, ?_⟩
      rw [run]
      simp [Prod.map, hc, labEntryClass]
    · rintro ⟨k, v, hk⟩
      refine ⟨k - 1, ?_⟩
      simp only [labRuns, Prod.map, Prod.mk.injEq] at hk
      revert hk
      cases (evaluate { t with clock := k - 1 }).1 <;> simp [labEntryClass]
  unfold semantics crepToLoopSemanticsWrapper
  by_cases h : ∃ clock, (evaluate { t with clock := clock }).1 = .error
  · rw [if_pos h, if_pos (hf.1 h)]
  rw [if_neg h, if_neg (fun h' => h (hf.2 h'))]
  have hP : (fun result => ∃ clock next outcome,
        evaluate { t with clock := clock } = (.halt outcome, next) ∧
        result = HolBehaviour.terminate outcome next.ffi.ioEvents) =
      (fun res => ∃ k r ev, labRuns t k = (.CompleteResult r, ev) ∧
        res = HolBehaviour.terminate r ev) := by
    funext res
    apply propext
    constructor
    · rintro ⟨c, next, outcome, he, rfl⟩
      exact ⟨c + 1, outcome, next.ffi.ioEvents, by rw [run, he]; rfl, rfl⟩
    · rintro ⟨k, r, ev, hk, rfl⟩
      simp only [labRuns] at hk
      rcases he : evaluate { t with clock := k - 1 } with ⟨m, next⟩
      rw [he] at hk
      simp only [Prod.map, Prod.mk.injEq] at hk
      obtain ⟨hm, rfl⟩ := hk
      cases m with
      | halt o =>
        simp only [labEntryClass, CrepToLoopSemanticsRunRes.CompleteResult.injEq] at hm
        exact ⟨k - 1, next, o, he, by rw [hm]⟩
      | error => simp [labEntryClass] at hm
      | timeOut => simp [labEntryClass] at hm
  have hL : (fun trace => ∃ clock,
        trace = HolLList.fromList (evaluate { t with clock := clock }).2.ffi.ioEvents) =
      (fun l => ∃ k, l = HolLList.fromList (labRuns t k).2) := by
    funext l
    apply propext
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c + 1, by rw [run]; rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k - 1, rfl⟩
  rw [hP, hL]
  rfl

/-- The StackSem entry runs simulate into the shifted LabSem runs. -/
theorem stackRunsSim {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : haltAssum C F s1.code) (rel : stateRel s1 s2)
    (hpc : locToPc start 0 s2.code = some s2.pc) :
    ∀ k r ev, stackRuns start s1 k = (r, ev) → r ≠ .RunError →
      ∃ k', labRuns s2 (k + k') = (r, ev) := by
  intro k r ev hk hr
  simp only [stackRuns] at hk
  rcases he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
    { s1 with clock := k }) with ⟨res, s2'⟩
  rw [he] at hk
  simp only [Prod.map, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have nerr : res ≠ some .error := by rintro rfl; simp [stackEntryClass] at hr
  rcases Nat.eq_zero_or_pos k with rfl | kpos
  · -- clock zero: both sides time out at once
    obtain ⟨-, -, ⟨-, rfl, rfl⟩ | ⟨h0, -⟩⟩ := callNoneInlCases he nerr
    · refine ⟨0, ?_⟩
      simp only [labRuns, Nat.add_zero, Nat.zero_sub]
      rw [evaluate, if_pos rfl]
      simp [Prod.map, labEntryClass, stackEntryClass, StackSemStateOps.emptyEnv,
        FlattenCorrect.relFfi rel]
    · exact absurd rfl h0
  have hres : res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F,
          sptSubspt { s1 with clock := k }.code s.code ∧ s.clock ≠ 0 →
          ∃ t, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1) := by
    intro hto
    rcases res with _ | x
    · simp [stackEntryClass] at hr
    rcases x with v | v | _ | _ | v | _ | e | _
    · rcases v with w | ⟨a, b⟩
      · simp [stackEntryClass] at hr
      · by_cases hab : a = 1 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := hab
          exact .inr (.inr ⟨1, rfl, halt⟩)
        · simp [stackEntryClass] at hr; omega
    · simp [stackEntryClass] at hr
    · simp [stackEntryClass] at hr
    · simp [stackEntryClass] at hr
    · rcases v with w | ⟨a, b⟩
      · exact .inl ⟨w, rfl⟩
      · simp [stackEntryClass] at hr
    · exact absurd rfl hto
    · exact .inr (.inl ⟨e, rfl⟩)
    · simp [stackEntryClass] at hr
  obtain ⟨ck, r2, t2, he2, hf, hh, hrs, hffi, hne, hto⟩ :=
    flattenCallCorrect (start := start) (s1 := { s1 with clock := k })
      (t1 := { s2 with clock := k }) (res := res) (s2 := s2')
      ⟨he, stateRelWithClock rel, by simpa using hpc, nerr, hres⟩
  refine ⟨ck, ?_⟩
  simp only [labRuns]
  rw [show k + ck - 1 = k - 1 + ck by omega]
  simp only at he2
  rw [he2]
  simp only [Prod.map, Prod.mk.injEq, hffi, and_true]
  rcases res with _ | x
  · simp [stackEntryClass] at hr
  rcases x with v | v | _ | _ | v | _ | e | _
  · rcases v with w | ⟨a, b⟩
    · simp [stackEntryClass] at hr
    · by_cases hab : a = 1 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := hab
        rw [hrs 1 rfl]
        simp [labEntryClass, stackEntryClass]
      · simp [stackEntryClass] at hr; omega
  · simp [stackEntryClass] at hr
  · simp [stackEntryClass] at hr
  · simp [stackEntryClass] at hr
  · rcases v with w | ⟨a, b⟩
    · rw [hh _ rfl]
      simp only [stackEntryClass]
      split_ifs <;> rfl
    · simp [stackEntryClass] at hr
  · rw [hto rfl]; rfl
  · rw [hf e rfl]; rfl
  · simp [stackEntryClass] at hr

/-- HOL `flatten_semantics`: under the halting assumption for procedure 1,
`state_rel` and the start procedure at the LabSem pc, a non-failing StackSem
semantics of the start call is the LabSem semantics. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "flatten_semantics"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs])
  (words_as_type_indexed_bitvec)]
theorem flattenSemantics {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F} :
    haltAssum C F s1.code ∧
    stateRel s1 s2 ∧
    locToPc start 0 s2.code = some s2.pc ∧
    StackSemEvaluate.semantics start s1 ≠ .fail →
    semantics s2 = StackSemEvaluate.semantics start s1 := by
  rintro ⟨halt, rel, hpc, hfail⟩
  rw [labSemIsWrapper, stackSemIsWrapper]
  rw [stackSemIsWrapper] at hfail
  refine crepToLoopSemanticsWrapper_eq _ _ hfail (stackRunsSim halt rel hpc) ?_ ?_ ?_ ?_
  · -- LabSem runs that do not time out are stable under more clock
    intro k k' r ev hk hr
    simp only [labRuns] at hk ⊢
    rcases he : evaluate { s2 with clock := k - 1 } with ⟨m, next⟩
    rw [he] at hk
    simp only [Prod.map, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hm : m ≠ .timeOut := by rintro rfl; exact hr rfl
    have kpos : k ≠ 0 := by
      rintro rfl
      rw [evaluate, if_pos rfl] at he
      exact hm (Prod.mk.inj he).1.symm
    have := LabProps.evaluateAddClock _ m next k' ⟨he, hm⟩
    simp only at this
    rw [show k + k' - 1 = k - 1 + k' by omega, this]
    rfl
  · -- StackSem runs that do not time out are stable under more clock
    intro k k' r ev hk hr
    simp only [stackRuns] at hk ⊢
    rcases he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s1 with clock := k }) with ⟨res, t⟩
    rw [he] at hk
    simp only [Prod.map, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hres : res ≠ some .timeOut := by rintro rfl; exact hr rfl
    have := StackProps.evaluateAddClock k' _ _ res t ⟨he, hres⟩
    simp only at this
    rw [this]
    rfl
  · -- StackSem event prefixes
    intro k k' ev hk
    refine ⟨_, _, rfl, ?_⟩
    have hev : (stackRuns start s1 (k + k')).2 = ev := by rw [hk]
    rw [← hev]
    have := StackProps.EvaluateAddClockIoEventsMono.evaluateAddClockIoEventsMono k'
      (.call none (.inl start) none : HolProg width) { s1 with clock := k }
    simp only [stackRuns, Prod.map] at this ⊢
    exact this
  · -- LabSem event prefixes
    intro k k' ev hk
    refine ⟨_, _, rfl, ?_⟩
    have hev : (labRuns s2 (k + k')).2 = ev := by rw [hk]
    rw [← hev]
    have := LabProps.evaluateAddClockIoEventsMono { s2 with clock := k - 1 } (k + k' - 1 - (k - 1))
    simp only at this
    rw [show k - 1 + (k + k' - 1 - (k - 1)) = k + k' - 1 by omega] at this
    simpa [labRuns, Prod.map] using this

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
