import Flapjack.Compiler.Backend.WordRemove
import Flapjack.Pancake.WordConvs
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.CodeLabels

/-!
# `wordConvsProof` `remove_must_terminate` group

The `remove_must_terminate` convention, label and handler preservation
theorems of `cakeml/compiler/backend/proofs/wordConvsProofScript.sml:2922-2970`.
-/

namespace Flapjack.WordConvs

open Flapjack.Compiler.Backend.WordRemove Flapjack.Compiler.Encoders.Asm

/-- Structural induction over `remove_must_terminate` results (Flapjack
infrastructure for HOL's `remove_must_terminate_ind` proofs): a reflexive
relation closed under the recursive clauses, with `MustTerminate b` related to
the result of its body, holds between every program and its image. -/
theorem removeMustTerminate_induct {width : Nat} [NeZero width]
    (R : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) → Prop)
    (hsame : ∀ p, R p p)
    (hseq : ∀ a b a' b', R a a' → R b b' → R (.seq a b) (.seq a' b'))
    (hite : ∀ cmp r ri a b a' b', R a a' → R b b' →
      R (.ite cmp r ri a b) (.ite cmp r ri a' b'))
    (hmt : ∀ b b', R b b' → R (.mustTerminate b) b')
    (hloop : ∀ n b e b', R b b' → R (.loop n b e) (.loop n b' e))
    (hcallH : ∀ dest args hn hp a b hp', R hp hp' →
      R (.call none dest args (some (hn, hp, a, b))) (.call none dest args (some (hn, hp', a, b))))
    (hcall : ∀ v cut ret l1 l2 dest args ret', R ret ret' →
      R (.call (some (v, cut, ret, l1, l2)) dest args none)
        (.call (some (v, cut, ret', l1, l2)) dest args none))
    (hcallRH : ∀ v cut ret l1 l2 dest args hn hp a b ret' hp', R ret ret' → R hp hp' →
      R (.call (some (v, cut, ret, l1, l2)) dest args (some (hn, hp, a, b)))
        (.call (some (v, cut, ret', l1, l2)) dest args (some (hn, hp', a, b)))) :
    ∀ p : WordLangProgHOL (BitVec width), R p (removeMustTerminate p)
  | .seq a b => by
      rw [removeMustTerminate]
      exact hseq _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH a)
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH b)
  | .ite cmp r ri a b => by
      rw [removeMustTerminate]
      exact hite _ _ _ _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH a)
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH b)
  | .mustTerminate b => by
      rw [removeMustTerminate]
      exact hmt _ _ (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH b)
  | .loop n b e => by
      rw [removeMustTerminate]
      exact hloop _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH b)
  | .call none dest args none => by rw [removeMustTerminate]; exact hsame _
  | .call none dest args (some (hn, hp, a, b)) => by
      rw [removeMustTerminate]
      exact hcallH _ _ _ _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH hp)
  | .call (some (v, cut, ret, l1, l2)) dest args none => by
      rw [removeMustTerminate]
      exact hcall _ _ _ _ _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH ret)
  | .call (some (v, cut, ret, l1, l2)) dest args (some (hn, hp, a, b)) => by
      rw [removeMustTerminate]
      exact hcallRH _ _ _ _ _ _ _ _ _ _ _ _ _
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH ret)
        (removeMustTerminate_induct R hsame hseq hite hmt hloop hcallH hcall hcallRH hp)
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _
  | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _
  | .tick | .opCurrHeap _ _ _ | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _
  | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by
      rw [removeMustTerminate] <;> first | exact hsame _ | (intros; contradiction)

/-- HOL `remove_must_terminate_conventions` (`wordConvsProofScript.sml:2929-2949`):
the program conventions are preserved and the labels are unchanged. HOL's free
instruction predicate `P` is the leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml" "remove_must_terminate_conventions"
  (words_as_type_indexed_bitvec)]
theorem removeMustTerminateConventions {width : Nat} [NeZero width]
    (P : WordLangInst (BitVec width) → Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (c : AsmConfigExact width) (k : Nat),
      let comp := removeMustTerminate p
      (flatExpConventions p = true → flatExpConventions comp = true) ∧
      (fullInstOkLessExact c p = true → fullInstOkLessExact c comp = true) ∧
      (postAllocConventionsHOL k p = true → postAllocConventionsHOL k comp = true) ∧
      (everyInst P p = true → everyInst P comp = true) ∧
      extractLabels p = extractLabels comp := by
  intro p c k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine removeMustTerminate_induct (fun p p' => flatExpConventions p = true →
      flatExpConventions p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
    all_goals intros
    all_goals simp_all [flatExpConventions]
  · refine removeMustTerminate_induct (fun p p' => fullInstOkLessExact c p = true →
      fullInstOkLessExact c p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
    all_goals intros
    all_goals simp_all [fullInstOkLessExact, fullInstOkLessWith]
  · intro h
    simp only [postAllocConventionsHOL, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_, ?_⟩
    · refine removeMustTerminate_induct (fun p p' => everyVarHOL isPhyVar p = true →
        everyVarHOL isPhyVar p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p h.1
      all_goals intros
      all_goals simp_all only [everyVarHOL, Bool.and_eq_true, Bool.true_and]
    · refine removeMustTerminate_induct (fun p p' =>
        everyStackVarHOL (fun name => decide (name ≥ 2 * k)) p = true →
        everyStackVarHOL (fun name => decide (name ≥ 2 * k)) p' = true)
        (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p h.2.1
      all_goals intros
      all_goals simp_all only [everyStackVarHOL, Bool.and_eq_true, Bool.true_and]
    · refine removeMustTerminate_induct (fun p p' => callArgConventionHOL p = true →
        callArgConventionHOL p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p h.2.2
      all_goals intros
      all_goals simp_all only [callArgConventionHOL, Bool.and_eq_true, Bool.true_and]
  · refine removeMustTerminate_induct (fun p p' => everyInst P p = true →
      everyInst P p' = true) (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
    all_goals intros
    all_goals simp_all [everyInst]
  · refine removeMustTerminate_induct (fun p p' => extractLabels p = extractLabels p')
      (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ p
    all_goals intros
    all_goals simp_all [extractLabels]

/-- HOL `word_get_code_labels_remove_must_terminate`
(`wordConvsProofScript.sml:2951-2959`). -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_get_code_labels_remove_must_terminate" (words_as_type_indexed_bitvec)]
theorem getCodeLabels_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ ps : WordLangProgHOL (BitVec width),
      getCodeLabelsHOL (removeMustTerminate ps) = getCodeLabelsHOL ps := by
  intro ps
  refine removeMustTerminate_induct (fun p p' => getCodeLabelsHOL p' = getCodeLabelsHOL p)
    (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ps
  all_goals intros
  all_goals simp_all [getCodeLabelsHOL]

/-- HOL `word_good_handlers_remove_must_terminate`
(`wordConvsProofScript.sml:2961-2969`); HOL's free handler label `n` is the
leading binder. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "word_good_handlers_remove_must_terminate" (words_as_type_indexed_bitvec)]
theorem goodHandlers_removeMustTerminate {width : Nat} [NeZero width] (n : Nat) :
    ∀ ps : WordLangProgHOL (BitVec width),
      goodHandlersHOL n (removeMustTerminate ps) = true ↔ goodHandlersHOL n ps = true := by
  intro ps
  refine removeMustTerminate_induct
    (fun p p' => goodHandlersHOL n p' = true ↔ goodHandlersHOL n p = true)
    (fun _ => Iff.rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ps
  all_goals intros
  all_goals simp_all [goodHandlersHOL]

end Flapjack.WordConvs
