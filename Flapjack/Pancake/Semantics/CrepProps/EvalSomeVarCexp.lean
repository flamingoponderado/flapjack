import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# crepProps `eval_some_var_cexp_local_lookup` over the exact carriers

Exact ports of `cakeml/pancake/semantics/crepPropsScript.sml`'s
`eval_some_var_cexp_local_lookup` (835) and
`opt_mmap_eval_some_var_cexp_local_lookup` (847) over the exact
`CrepSemHOLState`, the tagged `evalCrepSemHOLExp` (`eval_def`) and
`crepExpVarsHOL` (`var_cexp_def`) (bead `flapjack-pxn.18.5.6.33.15.10`).
HOL `OPT_MMAP` is `List.mapM` in `Option`, `FLAT (MAP f es)` is
`(es.map f).flatten`, and `FLOOKUP s.locals` is `s.locals.lookup`.  The generic
production-evaluator rendering is `evalCrepFullExpState_local_lookup_of_mem` in
`Flapjack/CrepeExpressionStability.lean`.
-/

namespace Flapjack

namespace CrepPropsEvalSomeVarCexpWitnesses

/-- Same-module witness for the `fmap_as_finite_support := [locals, globals,
    code]` qualifier (the evaluator reads `s.locals` and `s.globals`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

end CrepPropsEvalSomeVarCexpWitnesses

private theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ x ∈ xs, ∃ y, f x = some y
  | [], _, _, x, hx => by simp at hx
  | a :: as, ys, h, x, hx => by
      simp only [List.mapM_cons] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some b =>
        cases has : as.mapM f with
        | none => simp [ha, has] at h
        | some bs =>
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b, ha⟩
          · exact mapM_some_mem f as bs has x hx

private theorem eval_some_var_cexp_aux {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (n : Nat) :
    ∀ (e : CrepExpHOL width) (v : HolWordLab width),
      evalCrepSemHOLExp s e = some v → n ∈ crepExpVarsHOL e →
        ∃ w, s.locals.lookup n = some w
  | .const _, _, _, hm => by simp [crepExpVarsHOL] at hm
  | .var m, v, he, hm => by
      simp only [crepExpVarsHOL, List.mem_singleton] at hm
      subst hm
      exact ⟨v, by simpa [evalCrepSemHOLExp] using he⟩
  | .load a, _, he, hm => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at he
      | some w => exact eval_some_var_cexp_aux s n a w ha (by simpa [crepExpVarsHOL] using hm)
  | .load32 a, _, he, hm => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at he
      | some w => exact eval_some_var_cexp_aux s n a w ha (by simpa [crepExpVarsHOL] using hm)
  | .loadByte a, _, he, hm => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at he
      | some w => exact eval_some_var_cexp_aux s n a w ha (by simpa [crepExpVarsHOL] using hm)
  | .loadGlob _, _, _, hm => by simp [crepExpVarsHOL] at hm
  | .op _ args, _, he, hm => by
      cases hargs : args.mapM (evalCrepSemHOLExp s) with
      | none => simp [evalCrepSemHOLExp, hargs] at he
      | some vs =>
        simp only [crepExpVarsHOL, crepExpVarsHOLList_eq_flatMap] at hm
        obtain ⟨arg, harg, hn⟩ := List.mem_flatMap.mp hm
        obtain ⟨w, hw⟩ := mapM_some_mem _ args vs hargs arg harg
        exact eval_some_var_cexp_aux s n arg w hw hn
  | .crepOp _ args, _, he, hm => by
      cases hargs : args.mapM (evalCrepSemHOLExp s) with
      | none => simp [evalCrepSemHOLExp, hargs] at he
      | some vs =>
        simp only [crepExpVarsHOL, crepExpVarsHOLList_eq_flatMap] at hm
        obtain ⟨arg, harg, hn⟩ := List.mem_flatMap.mp hm
        obtain ⟨w, hw⟩ := mapM_some_mem _ args vs hargs arg harg
        exact eval_some_var_cexp_aux s n arg w hw hn
  | .cmp _ l r, _, he, hm => by
      cases hl : evalCrepSemHOLExp s l with
      | none => simp [evalCrepSemHOLExp, hl] at he
      | some wl =>
        cases hr : evalCrepSemHOLExp s r with
        | none => simp [evalCrepSemHOLExp, hl, hr] at he
        | some wr =>
          simp only [crepExpVarsHOL, List.mem_append] at hm
          rcases hm with hm | hm
          · exact eval_some_var_cexp_aux s n l wl hl hm
          · exact eval_some_var_cexp_aux s n r wr hr hm
  | .shift _ l r, _, he, hm => by
      cases hl : evalCrepSemHOLExp s l with
      | none => simp [evalCrepSemHOLExp, hl] at he
      | some wl =>
        cases hr : evalCrepSemHOLExp s r with
        | none => simp [evalCrepSemHOLExp, hl, hr] at he
        | some wr =>
          simp only [crepExpVarsHOL, List.mem_append] at hm
          rcases hm with hm | hm
          · exact eval_some_var_cexp_aux s n l wl hl hm
          · exact eval_some_var_cexp_aux s n r wr hr hm
  | .baseAddr, _, _, hm => by simp [crepExpVarsHOL] at hm
  | .topAddr, _, _, hm => by simp [crepExpVarsHOL] at hm
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem harg; omega)

/-- Exact HOL `eval_some_var_cexp_local_lookup` (`crepPropsScript.sml:835-837`):
    `∀s e v n. eval s e = SOME v /\ MEM n (var_cexp e) ==>
      ?w. FLOOKUP s.locals n = SOME w`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "eval_some_var_cexp_local_lookup"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crepEval_some_var_cexp_local_lookup {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
      (v : HolWordLab width) (n : Nat),
      evalCrepSemHOLExp s e = some v ∧ n ∈ crepExpVarsHOL e →
        ∃ w, s.locals.lookup n = some w :=
  fun s e v n h => eval_some_var_cexp_aux s n e v h.1 h.2

/-- Exact HOL `opt_mmap_eval_some_var_cexp_local_lookup`
    (`crepPropsScript.sml:847-850`): `∀s es vs n. OPT_MMAP (eval s) es = SOME vs ∧
      MEM n (FLAT (MAP var_cexp es)) ⇒ ∃w. FLOOKUP s.locals n = SOME w`. -/
@[hol "cakeml/pancake/semantics/crepPropsScript.sml" "opt_mmap_eval_some_var_cexp_local_lookup"
  (fmap_as_finite_support := [locals, globals, code]) (words_as_type_indexed_bitvec)]
theorem crepOptMmapEval_some_var_cexp_local_lookup {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width))
      (vs : List (HolWordLab width)) (n : Nat),
      es.mapM (evalCrepSemHOLExp s) = some vs ∧ n ∈ (es.map crepExpVarsHOL).flatten →
        ∃ w, s.locals.lookup n = some w := by
  intro s es vs n ⟨hes, hn⟩
  obtain ⟨vars, hvars, hmem⟩ := List.mem_flatten.mp hn
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvars
  obtain ⟨v, hv⟩ := mapM_some_mem _ es vs hes e he
  exact eval_some_var_cexp_aux s n e v hv hmem

end Flapjack
