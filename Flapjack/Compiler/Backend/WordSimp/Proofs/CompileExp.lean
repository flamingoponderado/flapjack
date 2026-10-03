import Flapjack.Compiler.Backend.WordSimp.Proofs.ConstFp

/-!
# `word_simpProof`: `simp_duplicate_if`, `push_out_if` and `compile_exp_thm`

Counterpart of `cakeml/compiler/backend/proofs/word_simpProofScript.sml:1171-1327`
(bead `flapjack-pxn.18.5.15.2.41`): `evaluate_try_if_hoist2`,
`evaluate_try_if_hoist1`, `evaluate_simp_duplicate_if`, `push_out_if_aux_T`,
`evaluate_simp_push_out_if` and the pass theorem `compile_exp_thm`, over the
native exact evaluator and the tagged `word_simp` definitions.

The untagged `evaluate_ite_seq` and the gc-restricted congruences are Flapjack
proof infrastructure; HOL obtains them by unfolding `evaluate_def` inside the
corresponding `*_ind` cases.

Inherited assumption: theorems mentioning `evaluate` reach the
`reals_as_rational_cuts`-qualified `inst`; the theorem map records the
`docs/SOUNDNESS.md` item 8 assumption.
-/

namespace Flapjack

namespace WordSimpCompileExpSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSimpCompileExpSupport

namespace WordSemStateFiniteExact

open Compiler.Backend.WordSimp

section Infrastructure

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem evaluate_ite_eq (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (.ite cmp r ri c1 c2) s =
      match getVar r s, getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => evaluate c1 s
          | some false => evaluate c2 s
          | none => (some .error, s)
      | _, _ => (some .error, s) :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    s ri r cmp c2 c1

/-- `Seq` distributes into both branches of an `If`. -/
theorem evaluate_ite_seq (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (b1 b2 q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (.seq (.ite cmp r ri b1 b2) q) s = evaluate (.ite cmp r ri (.seq b1 q) (.seq b2 q)) s := by
  rw [evaluate_seq_eq, evaluate_ite_eq, evaluate_ite_eq]
  rcases getVar r s with _ | x <;> rcases getVarImm ri s with _ | y <;> simp only
  rcases wordSemWordCmp cmp x y with _ | _ | _ <;> simp only <;> rw [evaluate_seq_eq]

end Infrastructure

theorem evaluate_hoist_ite {width : Nat} [NeZero width] {C : Type} {F : Type}
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec width))
    (br1 br2 interm p2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    evaluate (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2)) s =
      evaluate (.seq (.seq (.ite cmp lhs rhs br1 br2) interm) p2) s := by
  rw [evalEq_seq_assoc, evaluate_ite_seq]
  exact evalEq_ite (fun v => evalEq_seq_assoc br1 interm p2 v)
    (fun v => evalEq_seq_assoc br2 interm p2 v) cmp lhs rhs s

/-- Exact HOL local `evaluate_try_if_hoist2` (`word_simpProofScript.sml:1171-1206`);
    HOL's free `p3` is an explicit binder. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_try_if_hoist2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_try_if_hoist2 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p3 : WordLangProgHOL (BitVec width)) :
    ∀ (N : Nat) (p1 interm dummy p2 : WordLangProgHOL (BitVec width))
      (s : WordSemStateFiniteExact width C F),
      tryIfHoist2 N p1 interm dummy p2 = some p3 →
        gcFunConstOk s.gcFun →
        evaluate p3 s = evaluate (.seq (.seq p1 interm) p2) s := by
  intro N
  induction N with
  | zero => intro p1 interm dummy p2 s h; simp [tryIfHoist2] at h
  | succ n ih =>
    intro p1 interm dummy p2 s h hok
    simp only [tryIfHoist2] at h
    cases p1 with
    | ite cmp lhs rhs br1 br2 =>
      simp only at h
      split at h
      · cases h
      split at h
      · cases h
      simp only [Option.some.injEq] at h
      subst h
      rw [evaluate_const_fp _ _ hok, evaluate_hoist_ite]
    | seq f q =>
      simp only at h
      split at h
      · rename_i cmp lhs rhs br1 br2 hd
        have hq : q = .ite cmp lhs rhs br1 br2 := (dest_If_thm q cmp lhs rhs br1 br2).mp hd
        subst hq
        split at h
        · cases h
        split at h
        · cases h
        simp only [Option.some.injEq] at h
        subst h
        rw [evalEq_seq_assoc, evalEq_seq_assoc, evaluate_seq_eq, evaluate_seq_eq]
        rcases hf : evaluate f s with ⟨_ | r, s1⟩
        · have hok1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok f s none s1 ⟨hf, hok⟩
          simp only
          rw [evaluate_const_fp _ _ hok1, evaluate_hoist_ite, evalEq_seq_assoc]
        · rfl
      · split at h
        · rw [ih f (.seq q interm) dummy p2 s h hok]
          exact evalEq_seq (fun v => (evalEq_seq_assoc f q interm v).symm) (fun _ => rfl) s
        · cases h
    | _ => simp at h

/-- Exact HOL local `evaluate_try_if_hoist1` (`word_simpProofScript.sml:1208-1220`);
    HOL's free `p1 p2 p3 s` are explicit binders. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_try_if_hoist1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_try_if_hoist1 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p1 p2 p3 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    tryIfHoist1 p1 p2 = some p3 → gcFunConstOk s.gcFun →
      evaluate p3 s = evaluate (.seq p1 p2) s := by
  intro h hok
  simp only [tryIfHoist1] at h
  split at h
  · cases h
  · rw [evaluate_try_if_hoist2 p3 _ p1 .skip _ p2 s h hok]
    exact evalEq_seq (fun v => evaluate_Seq_Skip p1 v) (fun _ => rfl) s

section GcCongruence

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem gcFun_callEnv_pushEnv (args1 : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (callEnv args1 ss (pushEnv envs handler (decClock s))).gcFun = s.gcFun := by
  rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl

theorem evalEq_call_ret_gc {h1 h2 : WordLangProgHOL (BitVec width)}
    (h : ∀ v : WordSemStateFiniteExact width C F, gcFunConstOk v.gcFun →
      evaluate h1 v = evaluate h2 v)
    (n : List Nat) (names : WordLangCutsetsHOL) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (hok : gcFunConstOk s.gcFun) :
    evaluate (.call (some (n, names, h1, l1, l2)) dest args handler) s =
      evaluate (.call (some (n, names, h2, l1, l2)) dest args handler) s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht, ht]
  simp only [wordSemAddRetLoc]
  rcases getVars args s with _ | xs
  · rfl
  simp only
  split
  · rfl
  rcases wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · rfl
  simp only
  split
  · rfl
  rcases wordSemCutEnvs names s.locals with _ | envs
  · rfl
  simp only
  split
  · rfl
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨rc, s2⟩
  have hok2 : gcFunConstOk s2.gcFun := by
    rw [← (evaluate_consts prog _ _ s2 hcv).1, gcFun_callEnv_pushEnv]; exact hok
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | _ | _ | _ | _ | _ | _ <;> simp only
  split
  · rfl
  rcases hp : popEnv s2 with _ | s1
  · rfl
  simp only
  split
  · exact h _ (pop_env_gc_fun_const_ok s2 s1 ⟨hp, hok2⟩)
  · rfl

theorem evalEq_call_handler_gc {e1 e2 : WordLangProgHOL (BitVec width)}
    (h : ∀ v : WordSemStateFiniteExact width C F, gcFunConstOk v.gcFun →
      evaluate e1 v = evaluate e2 v)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat) (n l1 l2 : Nat)
    (s : WordSemStateFiniteExact width C F) (hok : gcFunConstOk s.gcFun) :
    evaluate (.call ret dest args (some (n, e1, l1, l2))) s =
      evaluate (.call ret dest args (some (n, e2, l1, l2))) s := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hp : ∀ (envs : Spt (WordLocW width) × Spt (WordLocW width))
      (t : WordSemStateFiniteExact width C F),
      pushEnv envs (some (n, e1, l1, l2)) t = pushEnv envs (some (n, e2, l1, l2)) t :=
    fun _ _ => rfl
  rw [ht, ht]
  simp only [hp]
  rcases getVars args s with _ | xs
  · rfl
  simp only
  split
  · rfl
  rcases wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · rfl
  simp only
  cases ret with
  | none => rfl
  | some rv =>
    obtain ⟨rn, names, retHandler, rl1, rl2⟩ := rv
    simp only
    split
    · rfl
    rcases wordSemCutEnvs names s.locals with _ | envs
    · rfl
    simp only
    split
    · rfl
    rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs (some (n, e2, l1, l2)) (decClock s)))
      with ⟨rc, s2⟩
    have hok2 : gcFunConstOk s2.gcFun := by
      rw [← (evaluate_consts prog _ _ s2 hcv).1]; exact hok
    rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | _ | _ | _ | _ | _ | _ <;> simp only
    split
    · rfl
    split
    · exact h _ hok2
    · rfl

end GcCongruence

theorem evaluate_seq_congr_gc {width : Nat} [NeZero width] {C : Type} {F : Type}
    {a a' b b' : WordLangProgHOL (BitVec width)} (s : WordSemStateFiniteExact width C F)
    (hok : gcFunConstOk s.gcFun) (ha : evaluate a' s = evaluate a s)
    (hb : ∀ v : WordSemStateFiniteExact width C F, gcFunConstOk v.gcFun →
      evaluate b' v = evaluate b v) :
    evaluate (.seq a' b') s = evaluate (.seq a b) s := by
  rw [evaluate_seq_eq, evaluate_seq_eq, ha]
  rcases he : evaluate a s with ⟨_ | r, s1⟩
  · exact hb s1 (evaluate_gc_fun_const_ok a s none s1 ⟨he, hok⟩)
  · rfl

/-- Exact HOL `evaluate_simp_duplicate_if` (`word_simpProofScript.sml:1222-1264`), by
    structural recursion as HOL's `simp_duplicate_if_ind`.  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_simp_duplicate_if"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_simp_duplicate_if {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      gcFunConstOk s.gcFun → evaluate (simpDuplicateIf p) s = evaluate p s
  | .mustTerminate q, s, hok => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [simpDuplicateIf]
      rw [ht, ht, evaluate_simp_duplicate_if q { s with
          clock := wordSemMustTerminateLimit width
          termdep := s.termdep - 1 } hok]
  | .call ret dest args handler, s, hok => by
      unfold simpDuplicateIf
      rcases ret with _ | ⟨x1, x2, q1, x3, x4⟩ <;> rcases handler with _ | ⟨y1, q2, y2, y3⟩ <;>
        simp only
      · exact evalEq_call_handler_gc (fun v hv => evaluate_simp_duplicate_if q2 v hv)
          none dest args y1 y2 y3 s hok
      · exact evalEq_call_ret_gc (fun v hv => evaluate_simp_duplicate_if q1 v hv)
          x1 x2 x3 x4 dest args none s hok
      · rw [evalEq_call_ret_gc (h1 := simpDuplicateIf q1) (h2 := q1)
          (fun v hv => evaluate_simp_duplicate_if q1 v hv) x1 x2 x3 x4 dest args _ s hok]
        exact evalEq_call_handler_gc (fun v hv => evaluate_simp_duplicate_if q2 v hv)
          _ dest args y1 y2 y3 s hok
  | .ite cmp lhs rhs br1 br2, s, hok => by
      simp only [simpDuplicateIf]
      rw [evaluate_ite_eq, evaluate_ite_eq, evaluate_simp_duplicate_if br1 s hok,
        evaluate_simp_duplicate_if br2 s hok]
  | .seq p1 p2, s, hok => by
      simp only [simpDuplicateIf]
      have hx : evaluate (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s =
          evaluate (.seq p1 p2) s :=
        evaluate_seq_congr_gc s hok (evaluate_simp_duplicate_if p1 s hok)
          (fun v hv => evaluate_simp_duplicate_if p2 v hv)
      split
      · exact hx
      · rename_i p3 h3
        rw [evaluate_Seq_assoc, evaluate_try_if_hoist1 _ _ p3 s h3 hok, hx]
  | .loop names body exitNames, s, hok => by
      simp only [simpDuplicateIf]
      exact evaluate_Loop_body_cong_gc gcFunConstOk s names body _ exitNames
        (fun v hv => evaluate_simp_duplicate_if body v hv) hok
  | .skip, _, _ | .move _ _, _, _ | .inst _, _, _ | .assign _ _, _, _ | .get _ _, _, _
  | .set _ _, _, _ | .store _ _, _, _ | .alloc _ _, _, _ | .storeConsts _ _ _ _ _, _, _
  | .raise _, _, _ | .return _ _, _, _ | .break _, _, _ | .continue _, _, _ | .tick, _, _
  | .opCurrHeap _ _ _, _, _ | .locValue _ _, _, _ | .install _ _ _ _ _, _, _
  | .codeBufferWrite _ _, _, _ | .dataBufferWrite _ _, _, _ | .ffi _ _ _ _ _ _, _, _
  | .shareInst _ _ _, _, _ => by simp only [simpDuplicateIf]

/-- Exact HOL local `push_out_if_aux_T` (`word_simpProofScript.sml:1266-1280`), by
    structural recursion as HOL's `push_out_if_aux_ind`. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "push_out_if_aux_T"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem push_out_if_aux_T {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (c2 c2' : WordLangProgHOL (BitVec width)) (res : Option (WordSemResult width))
      (s s' : WordSemStateFiniteExact width C F),
      pushOutIfAux c2 = (c2', true) → evaluate c2 s = (res, s') → res ≠ none
  | .mustTerminate q, c2', res, s, s', h, he => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [pushOutIfAux] at h
      rcases hq : pushOutIfAux q with ⟨c, b⟩
      rw [hq] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [ht] at he
      by_cases hz : s.termdep = 0
      · simp only [hz, if_true, Prod.mk.injEq] at he; rw [← he.1]; simp
      · simp only [hz, if_false] at he
        rcases hev : evaluate q { s with
            clock := wordSemMustTerminateLimit width
            termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hev] at he
        have hr := push_out_if_aux_T q c r _ s1 hq hev
        cases r with
        | none => exact absurd rfl hr
        | some x => cases x <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1] <;> simp
  | .return a b, _, res, s, s', _, he => by
      rw [evaluate] at he
      split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1] <;> simp
  | .raise n, _, res, s, s', _, he => by
      rw [evaluate] at he
      split at he
      · simp only [Prod.mk.injEq] at he; rw [← he.1]; simp
      · split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1] <;> simp
  | .call ret dest args handler, c2', res, s, s', h, he => by
      cases ret with
      | none =>
        have := evaluate_call_none_ne_none dest args handler s
        rw [he] at this; exact this
      | some _ => simp [pushOutIfAux] at h
  | .ite cmp r1 ri c1 c2, c2', res, s, s', h, he => by
      simp only [pushOutIfAux] at h
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rcases h2 : pushOutIfAux c2 with ⟨c2'', b2⟩
      rw [h1, h2] at h
      rcases b1 <;> rcases b2 <;> simp only [Prod.mk.injEq, Bool.false_eq_true, and_false] at h
      rw [evaluate_ite_eq] at he
      rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
        simp only [hx, hy, Prod.mk.injEq] at he
      all_goals try (rw [← he.1]; exact Option.some_ne_none _)
      rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hc, Prod.mk.injEq] at he
      · rw [← he.1]; simp
      · exact push_out_if_aux_T c2 c2'' res s s' h2 he
      · exact push_out_if_aux_T c1 c1' res s s' h1 he
  | .seq c1 c2, c2', res, s, s', h, he => by
      simp only [pushOutIfAux] at h
      rw [evaluate_seq_eq] at he
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rw [h1] at h
      rcases hev : evaluate c1 s with ⟨r1, s1⟩
      rw [hev] at he
      rcases b1
      · simp only at h
        rcases h2 : pushOutIfAux c2 with ⟨c2'', b2⟩
        rw [h2] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        cases r1 with
        | none => exact push_out_if_aux_T c2 c2'' res s1 s' h2 he
        | some x => simp only [Prod.mk.injEq] at he; rw [← he.1]; simp
      · have hr := push_out_if_aux_T c1 c1' r1 s s1 h1 hev
        cases r1 with
        | none => exact absurd rfl hr
        | some x => simp only [Prod.mk.injEq] at he; rw [← he.1]; simp
  | .loop _ _ _, _, _, _, _, h, _ => by simp [pushOutIfAux] at h
  | .skip, _, _, _, _, h, _ | .move _ _, _, _, _, _, h, _ | .inst _, _, _, _, _, h, _
  | .assign _ _, _, _, _, _, h, _ | .get _ _, _, _, _, _, h, _ | .set _ _, _, _, _, _, h, _
  | .store _ _, _, _, _, _, h, _ | .alloc _ _, _, _, _, _, h, _
  | .storeConsts _ _ _ _ _, _, _, _, _, h, _ | .break _, _, _, _, _, h, _
  | .continue _, _, _, _, _, h, _ | .tick, _, _, _, _, h, _
  | .opCurrHeap _ _ _, _, _, _, _, h, _ | .locValue _ _, _, _, _, _, h, _
  | .install _ _ _ _ _, _, _, _, _, h, _ | .codeBufferWrite _ _, _, _, _, _, h, _
  | .dataBufferWrite _ _, _, _, _, _, h, _ | .ffi _ _ _ _ _ _, _, _, _, _, h, _
  | .shareInst _ _ _, _, _, _, _, h, _ => by simp [pushOutIfAux] at h

/-- The `push_out_if_aux_ind` induction inside HOL's `evaluate_simp_push_out_if`
    proof, as a structural recursion over the first projection. Flapjack proof
    infrastructure; the tagged statement follows. -/
theorem evaluate_push_out_if_aux {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (pushOutIfAux p).1 s = evaluate p s
  | .mustTerminate q, s => by
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [pushOutIfAux]
      rw [ht, ht, evaluate_push_out_if_aux q]
  | .ite cmp r1 ri c1 c2, s => by
      have e1 := fun v => evaluate_push_out_if_aux (C := C) (F := F) c1 v
      have e2 := fun v => evaluate_push_out_if_aux (C := C) (F := F) c2 v
      simp only [pushOutIfAux]
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rcases h2 : pushOutIfAux c2 with ⟨c2', b2⟩
      rw [h1] at e1; rw [h2] at e2
      simp only at e1 e2
      rcases b1 <;> rcases b2 <;> simp only
      · rw [evaluate_ite_eq, evaluate_ite_eq, e1, e2]
      · rw [evaluate_seq_eq, evaluate_ite_eq, evaluate_ite_eq]
        rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
          simp only
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
        · rcases hev : evaluate c2' s with ⟨r, s1⟩
          rw [e2] at hev
          have hr := push_out_if_aux_T c2 c2' r s s1 h2 hev
          rw [hev]
          cases r with
          | none => exact absurd rfl hr
          | some _ => rfl
        · rw [evaluate_skip_eq]; exact e1 s
      · rw [evaluate_seq_eq, evaluate_ite_eq, evaluate_ite_eq]
        rcases hx : getVar r1 s with _ | x <;> rcases hy : getVarImm ri s with _ | y <;>
          simp only
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only
        · rw [evaluate_skip_eq]; exact e2 s
        · rcases hev : evaluate c1' s with ⟨r, s1⟩
          rw [e1] at hev
          have hr := push_out_if_aux_T c1 c1' r s s1 h1 hev
          rw [hev]
          cases r with
          | none => exact absurd rfl hr
          | some _ => rfl
      · rw [evaluate_ite_eq, evaluate_ite_eq, e1, e2]
  | .seq c1 c2, s => by
      have e1 := fun v => evaluate_push_out_if_aux (C := C) (F := F) c1 v
      have e2 := fun v => evaluate_push_out_if_aux (C := C) (F := F) c2 v
      simp only [pushOutIfAux]
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rw [h1] at e1
      simp only at e1
      rcases b1 <;> simp only
      · rcases h2 : pushOutIfAux c2 with ⟨c2', b2⟩
        rw [h2] at e2
        simp only at e2
        rw [evaluate_seq_eq, evaluate_seq_eq, e1]
        simp only [e2]
      · rw [evaluate_seq_eq, evaluate_seq_eq, e1]
  | .loop names body exitNames, s => by
      simp only [pushOutIfAux]
      exact evaluate_Loop_body_cong s names body _ exitNames
        (fun v => evaluate_push_out_if_aux body v)
  | .call ret dest args handler, s => by
      cases ret <;> simp only [pushOutIfAux]
  | .skip, _ | .move _ _, _ | .inst _, _ | .assign _ _, _ | .get _ _, _
  | .set _ _, _ | .store _ _, _ | .alloc _ _, _ | .storeConsts _ _ _ _ _, _
  | .raise _, _ | .return _ _, _ | .break _, _ | .continue _, _ | .tick, _
  | .opCurrHeap _ _ _, _ | .locValue _ _, _ | .install _ _ _ _ _, _
  | .codeBufferWrite _ _, _ | .dataBufferWrite _ _, _ | .ffi _ _ _ _ _ _, _
  | .shareInst _ _ _, _ => by simp only [pushOutIfAux]

/-- Exact HOL `evaluate_simp_push_out_if` (`word_simpProofScript.sml:1287-1314`). -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "evaluate_simp_push_out_if"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_simp_push_out_if {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
      evaluate (pushOutIf p) s = evaluate p s :=
  evaluate_push_out_if_aux

/-- Exact HOL `compile_exp_thm` (`word_simpProofScript.sml:1318-1327`): the
    `word_simp` pass preserves every non-`Error` evaluation. -/
@[hol "cakeml/compiler/backend/proofs/word_simpProofScript.sml" "compile_exp_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_exp_thm {width : Nat} [NeZero width] {C : Type} {F : Type}
    (prog : WordLangProgHOL (BitVec width)) (s s2 : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) :
    evaluate prog s = (res, s2) ∧ res ≠ some .error ∧ gcFunConstOk s.gcFun →
      evaluate (Compiler.Backend.WordSimp.compileExp prog) s = (res, s2) := by
  rintro ⟨he, -, hok⟩
  simp only [Compiler.Backend.WordSimp.compileExp]
  rw [evaluate_simp_push_out_if, evaluate_simp_duplicate_if _ _ hok,
    evaluate_const_fp _ _ hok, evaluate_Seq_assoc, he]

end WordSemStateFiniteExact

end Flapjack
