import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Control
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.StateEffect
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Inst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Call

/-!
# `evaluate_remove_dead`

HOL `evaluate_remove_dead` (`word_allocProofScript.sml:3900-4472`), assembled from
its per-constructor cases (`EvaluateRemoveDead/*`) by structural recursion on the
program, which supplies the induction hypotheses HOL takes from `remove_dead_ind`,
and its whole-program corollary `evaluate_remove_dead_prog` (`4473-4502`).
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

namespace EvaluateRemoveDeadWitnesses
/-- Roundtrip for the evaluator's actual imported canonical state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EvaluateRemoveDeadWitnesses

/-- Programs outside `flat_exp_conventions` satisfy the goal vacuously (Flapjack
infrastructure; HOL discharges `Assign` and `Store` by `flat_exp_conventions_def`
before the case split). -/
theorem removeDeadGoal_of_not_flat {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (h : flatExpConventions prog = false) :
    removeDeadGoal C F prog := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨-, -, -, hf, -, -⟩
  rw [h] at hf
  cases hf

/-- Every program satisfies the `evaluate_remove_dead` goal (Flapjack
infrastructure: the case assembly of the tagged theorem below). -/
theorem removeDeadGoalAll {width : Nat} [NeZero width] {C F : Type} :
    ∀ prog : WordLangProgHOL (BitVec width), removeDeadGoal C F prog
  | .skip => evaluateRemoveDead_Skip
  | .move pri ls => evaluateRemoveDead_Move pri ls
  | .inst i => evaluateRemoveDead_Inst i
  | .assign _ _ => removeDeadGoal_of_not_flat _ rfl
  | .get v name => evaluateRemoveDead_Get v name
  | .set v e => evaluateRemoveDead_Set v e
  | .store _ _ => removeDeadGoal_of_not_flat _ rfl
  | .mustTerminate p => evaluateRemoveDead_MustTerminate p (removeDeadGoalAll p)
  | .call none dest args h => evaluateRemoveDead_CallNone dest args h
  | .call (some (n, names, retH, l1, l2)) dest args none =>
      evaluateRemoveDead_CallSome n names retH l1 l2 dest args none (removeDeadGoalAll retH)
        (fun _ _ _ _ h => by cases h)
  | .call (some (n, names, retH, l1, l2)) dest args (some (hn, hp, a, b)) =>
      have ihp := removeDeadGoalAll hp
      evaluateRemoveDead_CallSome n names retH l1 l2 dest args (some (hn, hp, a, b))
        (removeDeadGoalAll retH) (fun _ _ _ _ h => by cases h; exact ihp)
  | .seq s1 s2 => evaluateRemoveDead_Seq s1 s2 (removeDeadGoalAll s1) (removeDeadGoalAll s2)
  | .ite cmp r ri e2 e3 =>
      evaluateRemoveDead_If cmp r ri e2 e3 (removeDeadGoalAll e2) (removeDeadGoalAll e3)
  | .loop names body exitNames =>
      evaluateRemoveDead_Loop names body exitNames (removeDeadGoalAll body)
  | .alloc n names => evaluateRemoveDead_Alloc n names
  | .storeConsts a b c d w => evaluateRemoveDead_StoreConsts a b c d w
  | .raise n => evaluateRemoveDead_Raise n
  | .return n ms => evaluateRemoveDead_Return n ms
  | .break k => evaluateRemoveDead_Break k
  | .continue k => evaluateRemoveDead_Continue k
  | .tick => evaluateRemoveDead_Tick
  | .opCurrHeap b d s => evaluateRemoveDead_OpCurrHeap b d s
  | .locValue r l => evaluateRemoveDead_LocValue r l
  | .install p l dp dl names => evaluateRemoveDead_Install p l dp dl names
  | .codeBufferWrite r1 r2 => evaluateRemoveDead_CodeBufferWrite r1 r2
  | .dataBufferWrite r1 r2 => evaluateRemoveDead_DataBufferWrite r1 r2
  | .ffi f p1 l1 p2 l2 names => evaluateRemoveDead_FFI f p1 l1 p2 l2 names
  | .shareInst op v e => evaluateRemoveDead_ShareInst op v e

/-- Exact HOL `evaluate_remove_dead` (`word_allocProofScript.sml:3900-3928`): HOL's
quantifiers, premises and existential conclusion in HOL order; HOL `I` is `id`,
HOL `oEL` is `sptOel`, and the conclusion's case expression on `res` is
`removeDeadPost`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateRemoveDead {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)) (prog' : WordLangProgHOL (BitVec width)) (livein : NumSet)
      (nlivein : List WordStoreHOL) (st : WordSemStateFiniteExact width C F)
      (t : Spt (WordLocW width)) (tstore : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F),
      strongLocalsRel id (sptDomain livein) st.locals t ∧
        liveStoreRel nlivein st.store tstore ∧
        evaluate prog st = (res, rst) ∧
        flatExpConventions prog = true ∧
        removeDead prog live nlive lt = (prog', livein, nlivein) ∧
        res ≠ some .error →
      ∃ (t' : Spt (WordLocW width)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW width)),
        evaluate prog' { st with locals := t, store := tstore } =
          (res, { rst with locals := t', store := tstore' }) ∧
        removeDeadPost live nlive lt res rst t' tstore' :=
  fun prog => removeDeadGoalAll prog

/-- Exact HOL `evaluate_remove_dead_prog` (`word_allocProofScript.sml:4473-4502`):
dead-code removal from the empty live set preserves a non-error result, the
final state except its locals, and the locals for results other than `NONE`,
`Break` and `Continue`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateRemoveDeadProg {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st rst : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)),
      flatExpConventions prog = true ∧ evaluate prog st = (res, rst) ∧ res ≠ some .error →
      ∃ t' : Spt (WordLocW width),
        evaluate (removeDeadProg prog) st = (res, { rst with locals := t' }) ∧
        match res with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => rst.locals = t' := by
  rintro prog st rst res ⟨hflat, hev, herr⟩
  rcases hrd : removeDead prog .ln [] [] with ⟨prog', livein, nlivein⟩
  obtain ⟨t', ts', heq, hpost⟩ := evaluateRemoveDead prog .ln [] [] prog' livein nlivein st
    st.locals st.store res rst
    ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hev, hflat, hrd, herr⟩
  have hts : rst.store = ts' := by
    cases res with
    | none => exact (liveStoreRelNil _ _).mp hpost.2
    | some r => cases r <;> first | exact hpost.1 | exact hpost.2
  subst hts
  refine ⟨t', ?_, ?_⟩
  · simp only [removeDeadProg, hrd]
    exact heq
  · cases res with
    | none => trivial
    | some r => cases r <;> first | trivial | exact hpost.1

end Flapjack.WordAlloc
