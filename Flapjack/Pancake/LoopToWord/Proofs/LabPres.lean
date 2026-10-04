import Flapjack.Pancake.LoopToWord.Proofs.LabelHandlers
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode
import Flapjack.Pancake.WordConvs

/-!
# `loop_to_wordProof`: lab_pres for loop_to_word

The `(**** lab_pres for loop_to_word ****)` section and the first-name offset lemmas of
`cakeml/pancake/proofs/loop_to_wordProofScript.sml` (2037-2265): the labels `comp` creates are
the fresh labels of the threaded counter, all in the function's label component, distinct, and
above the starting counter; `compile_prog` keeps function names. HOL's `EVERY P l` is
`∀ x ∈ l, P x`, `ALL_DISTINCT` is `List.Nodup` and `EL n l` (for `n < LENGTH l`) is `l[n]`.
-/

namespace Flapjack.LoopToWord
open Flapjack

/-- Labels of two consecutive counter ranges in the same component: count, range and
    distinctness of the concatenation (Flapjack infrastructure). -/
theorem labels_append {A B : List (Nat × Nat)} {k a b c : Nat} {kb : Nat}
    (hA : A.length = b - a) (hA' : ∀ q ∈ A, q.1 = k ∧ a ≤ q.2 ∧ q.2 < b) (hA'' : A.Nodup)
    (hB : B.length = c - b) (hB' : ∀ q ∈ B, q.1 = kb ∧ b ≤ q.2 ∧ q.2 < c) (hB'' : B.Nodup)
    (hk : kb = k) (hab : a ≤ b) (hbc : b ≤ c) :
    (A ++ B).length = c - a ∧ (∀ q ∈ A ++ B, q.1 = k ∧ a ≤ q.2 ∧ q.2 < c) ∧ (A ++ B).Nodup := by
  subst hk
  refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have := hA' q hq; omega
    · have := hB' q hq; omega
  · rw [List.nodup_append]
    refine ⟨hA'', hB'', fun x hx y hy heq => ?_⟩
    subst heq
    have := hA' x hx
    have := hB' x hy
    omega

/-- The labels of a compiled program: their count, range and distinctness (Flapjack
    infrastructure proving HOL's three `comp` label theorems at once, by induction over
    `comp`). -/
theorem compHOL_labels {width : Nat} [NeZero width] (ctxt : Spt Nat) :
    ∀ (prog : HolLoopProg width) (l : Nat × Nat),
      let r := compHOL ctxt prog l
      (extractLabels r.1).length = r.2.2 - l.2 ∧
        (∀ q ∈ extractLabels r.1, q.1 = l.1 ∧ l.2 ≤ q.2 ∧ q.2 < r.2.2) ∧
        (extractLabels r.1).Nodup := by
  intro prog
  induction prog using (measure (fun p : HolLoopProg width => sizeOf p)).wf.induction with
  | h prog ih =>
    intro l
    have sub : ∀ q, sizeOf q < sizeOf prog → ∀ (lab : Nat × Nat)
        (w : WordLangProgHOL (BitVec width)) (lab' : Nat × Nat), compHOL ctxt q lab = (w, lab') →
        (extractLabels w).length = lab'.2 - lab.2 ∧
          (∀ x ∈ extractLabels w, x.1 = lab.1 ∧ lab.2 ≤ x.2 ∧ x.2 < lab'.2) ∧
          (extractLabels w).Nodup ∧ lab'.1 = lab.1 ∧ lab.2 ≤ lab'.2 := by
      intro q hq lab w lab' hc
      have h := ih q hq lab
      have hb := loopToWordCompLInvariant ctxt q lab w lab' hc
      have hs := loopToWordCompSndLE ctxt q lab w lab' hc
      rw [hc] at h
      exact ⟨h.1, h.2.1, h.2.2, hb, hs⟩
    fun_cases compHOL ctxt prog l <;> simp only [extractLabels] <;>
      (try simp only [List.length_nil, List.not_mem_nil, List.nodup_nil, false_imp_iff,
        implies_true, and_true, Nat.sub_self])
    case h.case3 => simp
    case h.case14 =>
      rename_i first second w1 lab1 w2 lab2 h2 h1
      obtain ⟨a1, b1, c1, d1, e1⟩ := sub first (by simp; omega) l w1 lab1 h1
      obtain ⟨a2, b2, c2, d2, e2⟩ := sub second (by simp; omega) lab1 w2 lab2 h2
      exact labels_append a1 b1 c1 a2 b2 c2 d1 e1 e2
    case h.case15 =>
      rename_i _ _ _ thenB elseB _ w1 lab1 w2 lab2 h2 h1
      simp only [List.append_nil]
      obtain ⟨a1, b1, c1, d1, e1⟩ := sub thenB (by simp; omega) l w1 lab1 h1
      obtain ⟨a2, b2, c2, d2, e2⟩ := sub elseB (by simp; omega) lab1 w2 lab2 h2
      exact labels_append a1 b1 c1 a2 b2 c2 d1 e1 e2
    case h.case16 =>
      rename_i _ body _ w lab h
      simp only [List.nil_append, List.append_nil]
      obtain ⟨a, b, c, -, -⟩ := sub body (by simp; omega) l w lab h
      exact ⟨a, b, c⟩
    case h.case22 =>
      rename_i body
      obtain ⟨a, b, c, -, -⟩ := sub body (by simp) l _ _ rfl
      exact ⟨a, b, c⟩
    case h.case26 => simp +zetaDelta
    case h.case27 =>
      rename_i w1 lab1 w2 lab2 h2 fl nl h1
      obtain ⟨a1, b1, c1, d1, e1⟩ := sub _ (by simp; omega) _ w1 lab1 h1
      obtain ⟨a2, b2, c2, d2, e2⟩ := sub _ (by simp; omega) lab1 w2 lab2 h2
      simp only [fl, nl] at a1 b1 d1 e1 ⊢
      simp only [List.append_nil, List.length_append, List.length_cons, List.length_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨by omega, ?_, ?_⟩
      · intro q hq
        rcases hq with ((hq | hq) | hq) | hq
        · subst hq; dsimp only; omega
        · subst hq; dsimp only; omega
        · have := b2 q hq; omega
        · have := b1 q hq; omega
      · rw [List.nodup_append, List.nodup_append]
        refine ⟨⟨?_, c2, ?_⟩, c1, ?_⟩
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
            and_true, Prod.mk.injEq, not_and]
          exact ⟨fun _ => by omega, not_false⟩
        · intro a ha b hb heq
          subst heq
          have := b2 a hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with ha | ha <;> subst ha <;> dsimp only at this <;> omega
        · intro a ha b hb heq
          subst heq
          have := b1 a hb
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with (ha | ha) | ha
          · subst ha; dsimp only at this; omega
          · subst ha; dsimp only at this; omega
          · have := b2 a ha; omega

/-- HOL `loop_to_word_comp_extract_labels_len` (`loop_to_wordProofScript.sml:2051-2085`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_extract_labels_len"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_extract_labels_len {width : Nat} [NeZero width] :
    ∀ (ctxt : Spt Nat) (prog : HolLoopProg width) (l : Nat × Nat)
      (p : WordLangProgHOL (BitVec width)) (r : Nat × Nat),
      compHOL ctxt prog l = (p, r) → (extractLabels p).length = r.2 - l.2 := by
  intro ctxt prog l p r h
  have := (compHOL_labels ctxt prog l).1
  rw [h] at this
  exact this

/-- HOL `loop_to_word_comp_extract_labels` (`loop_to_wordProofScript.sml:2087-2135`); HOL's
    `EVERY (λ(q,r). …)` is `∀ x ∈ …` on the pair's components. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_extract_labels"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_extract_labels {width : Nat} [NeZero width] :
    ∀ (ctxt : Spt Nat) (prog : HolLoopProg width) (l : Nat × Nat)
      (p : WordLangProgHOL (BitVec width)) (l' : Nat × Nat),
      compHOL ctxt prog l = (p, l') →
      ∀ x ∈ extractLabels p, x.1 = l.1 ∧ l.2 ≤ x.2 ∧ x.2 < l'.2 := by
  intro ctxt prog l p l' h
  have := (compHOL_labels ctxt prog l).2.1
  rw [h] at this
  exact this

/-- HOL `loop_to_word_comp_ALL_DISTINCT` (`loop_to_wordProofScript.sml:2137-2195`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_ALL_DISTINCT"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_ALL_DISTINCT {width : Nat} [NeZero width] :
    ∀ (ctxt : Spt Nat) (prog : HolLoopProg width) (l : Nat × Nat)
      (p : WordLangProgHOL (BitVec width)) (r : Nat × Nat),
      compHOL ctxt prog l = (p, r) → (extractLabels p).Nodup := by
  intro ctxt prog l p r h
  have := (compHOL_labels ctxt prog l).2.2
  rw [h] at this
  exact this

/-- HOL `loop_to_word_comp_func_lab_pres` (`loop_to_wordProofScript.sml:2197-2214`); HOL's
    free `n' params body p` are explicit, `EL n l` is `l[n]` under `n < LENGTH l`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_comp_func_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_comp_func_lab_pres {width : Nat} [NeZero width] (n' : Nat)
    (params : List Nat) (body : HolLoopProg width) (p : WordLangProgHOL (BitVec width)) :
    loopToWordCompFuncHOL n' params body = p →
    (∀ n (h : n < (extractLabels p).length),
        (extractLabels p)[n].1 = n' ∧ (extractLabels p)[n].2 ≠ 0 ∧ (extractLabels p)[n].2 ≠ 1) ∧
      (extractLabels p).Nodup := by
  rintro rfl
  simp only [loopToWordCompFuncHOL]
  obtain ⟨-, hr, hd⟩ := compHOL_labels (width := width)
    (makeCtxtHOL 2 (params ++ fromNumSetHOL (sptDifference (accVarsHOL body (.ln : Spt Unit))
      (toNumSetHOL params))) (.ln : Spt Nat)) body (n', 2)
  refine ⟨fun n h => ?_, hd⟩
  have := hr _ (List.getElem_mem h)
  dsimp only at this
  omega

/-- HOL `loop_to_word_compile_prog_lab_pres` (`loop_to_wordProofScript.sml:2216-2232`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_lab_pres"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_prog_lab_pres {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    loopToWordCompileProgHOL prog = prog' →
    ∀ x ∈ prog',
      (∀ q ∈ extractLabels x.2.2, q.1 = x.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧ (extractLabels x.2.2).Nodup := by
  rintro rfl x hx
  simp only [loopToWordCompileProgHOL, List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := loop_to_word_comp_func_lab_pres e.1 e.2.1 e.2.2 _ rfl
  refine ⟨fun q hq => ?_, h2⟩
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hq
  exact h1 n hn

/-- HOL `loop_to_word_compile_prog_FST_eq` (`loop_to_wordProofScript.sml:2236-2245`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_FST_eq"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_prog_FST_eq {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    loopToWordCompileProgHOL prog = prog' → prog'.map Prod.fst = prog.map Prod.fst := by
  rintro rfl
  simp [loopToWordCompileProgHOL, List.map_map, Function.comp_def]

/-- HOL `loop_to_word_compile_prog_lab_min` (`loop_to_wordProofScript.sml:2247-2254`); HOL's free
    `x` is explicit. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_prog_lab_min"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_prog_lab_min {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) (x : Nat) :
    loopToWordCompileProgHOL prog = prog' ∧ (∀ p ∈ prog, x ≤ p.1) → ∀ p ∈ prog', x ≤ p.1 := by
  rintro ⟨h, hx⟩ p hp
  have hf := loop_to_word_compile_prog_FST_eq prog prog' h
  have : p.1 ∈ prog.map Prod.fst := hf ▸ List.mem_map_of_mem hp
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp this
  rw [← hqe]
  exact hx q hq

/-- HOL `loop_to_word_compile_lab_min` (`loop_to_wordProofScript.sml:2256-2265`). -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "loop_to_word_compile_lab_min"
  (words_as_type_indexed_bitvec)]
theorem loop_to_word_compile_lab_min {width : Nat} [NeZero width]
    (prog : List (Nat × List Nat × HolLoopProg width))
    (prog' : List (Nat × Nat × WordLangProgHOL (BitVec width))) (x : Nat) :
    loopToWordCompileHOL prog = prog' ∧ (∀ p ∈ prog, x ≤ p.1) → ∀ p ∈ prog', x ≤ p.1 :=
  loop_to_word_compile_prog_lab_min prog prog' x

end Flapjack.LoopToWord
