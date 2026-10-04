import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.NotCreated
import Flapjack.Pancake.WordConvs.CodeLabels
import Flapjack.Pancake.WordConvs.WfCutsets

/-!
# `wordConvsProof` `remove_dead_prog` group

The `remove_dead` convention, label and handler preservation theorems of
`cakeml/compiler/backend/proofs/wordConvsProofScript.sml:1518-1605`.
-/

namespace Flapjack.WordConvs

open Flapjack.WordAlloc Flapjack.Compiler.Encoders.Asm

/-- `remove_dead`'s `Seq` result: a `Skip` child is dropped (Flapjack
infrastructure mirroring the inline match of `remove_dead_def`). -/
def rdSeq {width : Nat} (s1 s2 : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match s1, s2 with
  | .skip, _ => s2
  | _, .skip => s1
  | _, _ => .seq s1 s2

/-- `remove_dead`'s `If` result: two `Skip` branches give `Skip` (Flapjack
infrastructure mirroring `remove_dead_def`). -/
def rdIte {width : Nat} (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (e2 e3 : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match e2, e3 with
  | .skip, .skip => .skip
  | _, _ => .ite cmp r ri e2 e3

/-- The programs `remove_dead` may replace by `Skip` (Flapjack infrastructure). -/
def rdDroppable {width : Nat} : WordLangProgHOL (BitVec width) → Prop
  | .move _ _ | .inst _ | .get _ _ | .opCurrHeap _ _ _ | .locValue _ _ | .set _ _ => True
  | _ => False

/-- Structural induction over `remove_dead` results (Flapjack infrastructure for
HOL's `remove_dead_ind` proofs): a relation holding for the leaf outcomes
(unchanged, `Skip`, filtered `Move`) and closed under the recursive clauses
holds between every program and its `remove_dead` output. -/
theorem removeDead_induct {width : Nat} [NeZero width]
    (R : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) → Prop)
    (hsame : ∀ p, R p p)
    (hskip : ∀ p, rdDroppable p → R p .skip)
    (hmove : ∀ pri ls q, R (.move pri ls) (.move pri (ls.filter q)))
    (hseq : ∀ s1 s2 s1' s2', R s1 s1' → R s2 s2' → R (.seq s1 s2) (rdSeq s1' s2'))
    (hmt : ∀ b b', R b b' → R (.mustTerminate b) (.mustTerminate b'))
    (hite : ∀ cmp r ri e2 e3 e2' e3', R e2 e2' → R e3 e3' →
      R (.ite cmp r ri e2 e3) (rdIte cmp r ri e2' e3'))
    (hloop : ∀ n b e b', R b b' → R (.loop n b e) (.loop n b' e))
    (hcall : ∀ v cut ret l1 l2 dest args ret', R ret ret' →
      R (.call (some (v, cut, ret, l1, l2)) dest args none)
        (.call (some (v, cut, ret', l1, l2)) dest args none))
    (hcallH : ∀ v cut ret l1 l2 dest args hn hp a b ret' hp', R ret ret' → R hp hp' →
      R (.call (some (v, cut, ret, l1, l2)) dest args (some (hn, hp, a, b)))
        (.call (some (v, cut, ret', l1, l2)) dest args (some (hn, hp', a, b)))) :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)), R p (removeDead p live nlive lt).1
  | .seq s1 s2, live, nlive, lt => by
      rw [removeDead.eq_def]
      simp only
      rcases h2 : removeDead s2 live nlive lt with ⟨s2', l2, n2⟩
      rcases h1 : removeDead s1 l2 n2 lt with ⟨s1', l1, n1⟩
      have ih2 := removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH s2 live nlive lt
      have ih1 := removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH s1 l2 n2 lt
      rw [h2] at ih2; rw [h1] at ih1
      exact hseq s1 s2 s1' s2' ih1 ih2
  | .mustTerminate b, live, nlive, lt => by
      rw [removeDead.eq_def]
      simp only
      rcases h : removeDead b live nlive lt with ⟨b', l', n'⟩
      have ih := removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH b live nlive lt
      rw [h] at ih
      exact hmt b b' ih
  | .loop names b exitNames, live, nlive, lt => by
      rw [removeDead.eq_def]
      exact hloop _ _ _ _ (removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH b
        names [] ((names, exitNames) :: lt))
  | .ite cmp r ri e2 e3, live, nlive, lt => by
      rw [removeDead.eq_def]
      simp only
      rcases h2 : removeDead e2 live nlive lt with ⟨e2', l2, n2⟩
      rcases h3 : removeDead e3 live nlive lt with ⟨e3', l3, n3⟩
      have ih2 := removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH e2 live nlive lt
      have ih3 := removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH e3 live nlive lt
      rw [h2] at ih2; rw [h3] at ih3
      exact hite cmp r ri e2 e3 e2' e3' ih2 ih3
  | .call none dest args h, live, nlive, lt => by
      rw [removeDead.eq_def]
      exact hsame _
  | .call (some (v, cut, ret, l1, l2)) dest args none, live, nlive, lt => by
      rw [removeDead.eq_def]
      exact hcall v cut ret l1 l2 dest args _
        (removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH ret live nlive lt)
  | .call (some (v, cut, ret, l1, l2)) dest args (some (hn, hp, a, b)), live, nlive, lt => by
      rw [removeDead.eq_def]
      exact hcallH v cut ret l1 l2 dest args hn hp a b _ _
        (removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH ret live nlive lt)
        (removeDead_induct R hsame hskip hmove hseq hmt hite hloop hcall hcallH hp live nlive lt)
  | .move pri ls, live, nlive, lt => by
      rw [removeDead.eq_def]
      simp only
      split
      · exact hskip _ trivial
      · exact hmove _ _ _
  | .skip, live, nlive, lt | .inst _, live, nlive, lt
  | .assign _ _, live, nlive, lt | .get _ _, live, nlive, lt | .set _ _, live, nlive, lt
  | .store _ _, live, nlive, lt | .alloc _ _, live, nlive, lt
  | .storeConsts _ _ _ _ _, live, nlive, lt | .raise _, live, nlive, lt
  | .return _ _, live, nlive, lt | .break _, live, nlive, lt | .continue _, live, nlive, lt
  | .tick, live, nlive, lt | .opCurrHeap _ _ _, live, nlive, lt
  | .locValue _ _, live, nlive, lt | .install _ _ _ _ _, live, nlive, lt
  | .codeBufferWrite _ _, live, nlive, lt | .dataBufferWrite _ _, live, nlive, lt
  | .ffi _ _ _ _ _ _, live, nlive, lt | .shareInst _ _ _, live, nlive, lt => by
      rw [removeDead.eq_def]
      all_goals (try simp only)
      all_goals (repeat' split)
      all_goals first | exact hsame _ | exact hskip _ trivial

/-- HOL `remove_dead_not_created_subprogs` (`wordConvsProofScript.sml:1521-1535`);
HOL's free predicate `P` is the leading binder. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeDead_notCreatedSubprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (q : NumSet) (r : List WordStoreHOL)
      (lt : List (NumSet × NumSet)),
      notCreatedSubprogsHOL P prog = true →
      notCreatedSubprogsHOL P (removeDead prog q r lt).1 = true := by
  intro prog q r lt
  refine removeDead_induct (fun p p' => notCreatedSubprogsHOL P p = true →
    notCreatedSubprogsHOL P p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ prog q r lt
  · intro p _ _; simp [notCreatedSubprogsHOL]
  · intro _ _ _ _; simp [notCreatedSubprogsHOL]
  · intro s1 s2 s1' s2' ih1 ih2 h
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h
    have h1 := ih1 h.1; have h2 := ih2 h.2
    unfold rdSeq; split <;> simp_all [notCreatedSubprogsHOL]
  · intro b b' ih h
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih h.2⟩
  · intro cmp r ri e2 e3 e2' e3' ih2 ih3 h
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h
    have h2 := ih2 h.1; have h3 := ih3 h.2
    unfold rdIte; split <;> simp_all [notCreatedSubprogsHOL]
  · intro n b e b' ih h
    simp only [notCreatedSubprogsHOL] at h ⊢
    exact ih h
  · intro v cut ret l1 l2 dest args ret' ih h
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, ih h.1.2⟩, h.2⟩
  · intro v cut ret l1 l2 dest args hn hp a b ret' hp' ihr ihp h
    simp only [notCreatedSubprogsHOL, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, ihr h.1.2⟩, h.2.1, ihp h.2.2⟩

/-- HOL `remove_dead_prog_not_created_subprogs` (`wordConvsProofScript.sml:1537-1543`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeDeadProg_notCreatedSubprogs {width : Nat} [NeZero width]
    (P : WordLangProgHOL (BitVec width) → Bool) (prog : WordLangProgHOL (BitVec width)) :
    notCreatedSubprogsHOL P prog = true →
    notCreatedSubprogsHOL P (removeDeadProg prog) = true :=
  removeDead_notCreatedSubprogs P prog .ln [] []

/-- HOL `remove_dead_conventions` (`wordConvsProofScript.sml:1545-1561`): the
program conventions are preserved and the labels are unchanged. HOL's free
instruction predicate `P` is the leading binder; HOL's binder `k` does not occur
in the statement and is omitted. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeDeadConventions {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)) (c : AsmConfigExact width),
      let comp := (removeDead p live nlive lt).1
      (flatExpConventions p = true → flatExpConventions comp = true) ∧
      (fullInstOkLessExact c p = true → fullInstOkLessExact c comp = true) ∧
      (preAllocConventionsHOL p = true → preAllocConventionsHOL comp = true) ∧
      (everyInst P p = true → everyInst P comp = true) ∧
      (wfCutsets p → wfCutsets comp) ∧
      extractLabels p = extractLabels comp := by
  intro p live nlive lt c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine removeDead_induct (fun p p' => flatExpConventions p = true →
      flatExpConventions p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt
    all_goals intros
    all_goals (try unfold rdSeq)
    all_goals (try unfold rdIte)
    all_goals (repeat' split)
    all_goals simp_all [flatExpConventions]
  · refine removeDead_induct (fun p p' => fullInstOkLessExact c p = true → fullInstOkLessExact c p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt
    all_goals intros
    all_goals (try unfold rdSeq)
    all_goals (try unfold rdIte)
    all_goals (repeat' split)
    all_goals simp_all [fullInstOkLessExact, fullInstOkLessWith]
  · intro h
    simp only [preAllocConventionsHOL, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · refine removeDead_induct (fun p p' => everyStackVarHOL isStackVar p = true →
        everyStackVarHOL isStackVar p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt h.1
      all_goals intros
      all_goals (try unfold rdSeq)
      all_goals (try unfold rdIte)
      all_goals (repeat' split)
      all_goals simp_all only [everyStackVarHOL, Bool.and_eq_true, Bool.true_and]
    · refine removeDead_induct (fun p p' => callArgConventionHOL p = true →
        callArgConventionHOL p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt h.2
      all_goals intros
      all_goals (try unfold rdSeq)
      all_goals (try unfold rdIte)
      all_goals (repeat' split)
      all_goals simp_all only [callArgConventionHOL, Bool.and_eq_true, Bool.true_and]
  · refine removeDead_induct (fun p p' => everyInst P p = true → everyInst P p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt
    all_goals intros
    all_goals (try unfold rdSeq)
    all_goals (try unfold rdIte)
    all_goals (repeat' split)
    all_goals simp_all [everyInst]
  · refine removeDead_induct (fun p p' => wfCutsets p → wfCutsets p') (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt
    all_goals intros
    all_goals (try unfold rdSeq)
    all_goals (try unfold rdIte)
    all_goals (repeat' split)
    all_goals simp_all [wfCutsets]
  · refine removeDead_induct (fun p p' => extractLabels p = extractLabels p') (fun _ => rfl)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p live nlive lt
    · intro p hp; cases p <;> simp_all [rdDroppable, extractLabels]
    all_goals intros
    all_goals (try unfold rdSeq)
    all_goals (try unfold rdIte)
    all_goals (repeat' split)
    all_goals simp_all [extractLabels]

/-- HOL `remove_dead_prog_conventions` (`wordConvsProofScript.sml:1563-1565`):
`remove_dead_conventions` at `LN [] []`, with HOL's free `p`, `c` and `P`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem removeDeadProgConventions {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) (p : WordLangProgHOL (BitVec width))
    (c : AsmConfigExact width) :
    (flatExpConventions p = true → flatExpConventions (removeDeadProg p) = true) ∧
    (fullInstOkLessExact c p = true → fullInstOkLessExact c (removeDeadProg p) = true) ∧
    (preAllocConventionsHOL p = true → preAllocConventionsHOL (removeDeadProg p) = true) ∧
    (everyInst P p = true → everyInst P (removeDeadProg p) = true) ∧
    (wfCutsets p → wfCutsets (removeDeadProg p)) ∧
    extractLabels p = extractLabels (removeDeadProg p) :=
  removeDeadConventions P p .ln [] [] c

/-- HOL `word_get_code_labels_remove_dead` (`wordConvsProofScript.sml:1567-1577`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getCodeLabels_removeDead {width : Nat} [NeZero width] :
    ∀ (ps : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)),
      getCodeLabelsHOL (removeDead ps live nlive lt).1 ⊆ getCodeLabelsHOL ps := by
  intro ps live nlive lt
  refine removeDead_induct (fun p p' => getCodeLabelsHOL p' ⊆ getCodeLabelsHOL p)
    (fun _ => fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ps live nlive lt
  all_goals intros
  all_goals (try unfold rdSeq)
  all_goals (try unfold rdIte)
  all_goals (repeat' split)
  all_goals simp only [getCodeLabelsHOL] at *
  all_goals intro x hx
  all_goals aesop

/-- HOL `word_get_code_labels_remove_dead_prog` (`wordConvsProofScript.sml:1579-1584`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getCodeLabels_removeDeadProg {width : Nat} [NeZero width]
    (ps : WordLangProgHOL (BitVec width)) :
    getCodeLabelsHOL (removeDeadProg ps) ⊆ getCodeLabelsHOL ps :=
  getCodeLabels_removeDead ps .ln [] []

/-- HOL `word_good_handlers_remove_dead` (`wordConvsProofScript.sml:1586-1596`);
HOL's free handler label `n` is the leading binder. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem goodHandlers_removeDead {width : Nat} [NeZero width] (n : Nat) :
    ∀ (ps : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)),
      goodHandlersHOL n (removeDead ps live nlive lt).1 = true ↔ goodHandlersHOL n ps = true := by
  intro ps live nlive lt
  refine removeDead_induct (fun p p' => goodHandlersHOL n p' = true ↔ goodHandlersHOL n p = true)
    (fun _ => Iff.rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ps live nlive lt
  · intro p hp; cases p <;> simp_all [rdDroppable, goodHandlersHOL]
  all_goals intros
  all_goals (try unfold rdSeq)
  all_goals (try unfold rdIte)
  all_goals (repeat' split)
  all_goals simp_all [goodHandlersHOL]

/-- HOL `word_good_handlers_remove_dead_prog` (`wordConvsProofScript.sml:1598-1603`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem goodHandlers_removeDeadProg {width : Nat} [NeZero width] (n : Nat)
    (ps : WordLangProgHOL (BitVec width)) :
    goodHandlersHOL n (removeDeadProg ps) = true ↔ goodHandlersHOL n ps = true :=
  goodHandlers_removeDead n ps .ln [] []

end Flapjack.WordConvs
