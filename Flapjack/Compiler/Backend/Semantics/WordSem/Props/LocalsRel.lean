import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead.Inst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
import Flapjack.Pancake.WordLang.OccurrencesExact
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Compiler.Backend.WordInst.Proofs.PullExp

/-!
# `wordProps`: extra temporaries do not affect evaluation (`locals_rel`)

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:3385-3850`
(bead `flapjack-pxn.18.5.15.2.42.1`): `locals_rel_def`, `the_words_EVERY_IS_SOME`,
the `locals_rel` lemmas for `get_var(s)`, `get_var_imm`, `alist_insert`,
`word_exp`, `insert`, `delete`, `cut_envs`, `cut_env`, and
`locals_rel_evaluate_thm` with every `Resume` case, over the native exact
evaluator.

HOL's `(λx. x < temp)` predicate is the Boolean `fun x => decide (x < temp)`;
HOL `EVERY (λx. x < temp) ls` over a register list is `∀ x ∈ ls, x < temp`.
The per-instruction frame of `Inst` reuses the allocator proof's
`instCongr` (Flapjack infrastructure), and the cut lemmas reuse
`strongLocalsRelICutEnvs` (HOL `strong_locals_rel_I_cut_envs`), which already
establish the HOL tree equalities by `spt_eq_thm`.

Inherited assumption: theorems mentioning `evaluate` reach the
`reals_as_rational_cuts`-qualified `inst`; the theorem map records the
`docs/SOUNDNESS.md` item 8 assumption.
-/

namespace Flapjack

namespace WordSemLocalsRelSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemLocalsRelSupport

/-- Exact HOL `locals_rel_def` (`wordPropsScript.sml:3385-3387`):
    `locals_rel temp s t ⇔ ∀x. x < temp ⇒ lookup x s = lookup x t`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_def"
  (words_as_type_indexed_bitvec)]
def wordLocalsRel {width : Nat} [NeZero width] (temp : Nat) (s t : Spt (WordLocW width)) : Prop :=
  ∀ x, x < temp → sptLookup x s = sptLookup x t

namespace WordSemStateFiniteExact

/-- Exact HOL `the_words_EVERY_IS_SOME` (`wordPropsScript.sml:3389-3397`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "the_words_EVERY_IS_SOME"
  (words_as_type_indexed_bitvec)]
theorem the_words_EVERY_IS_SOME {width : Nat} [NeZero width] :
    ∀ (ls : List (Option (WordLocW width))) (x : List (BitVec width)),
      theWords ls = some x → ∀ o ∈ ls, o.isSome = true
  | [], _, _ => by simp
  | o :: ls, x, h => by
      intro o' ho'
      rcases o with _ | (a | _)
      · simp [theWords] at h
      · cases hl : theWords ls with
        | none => simp [theWords, hl] at h
        | some xs =>
            rcases List.mem_cons.mp ho' with rfl | ho'
            · rfl
            · exact the_words_EVERY_IS_SOME ls xs hl o' ho'
      · simp [theWords] at h

/-- Exact HOL `locals_rel_get_var` (`wordPropsScript.sml:3424-3432`); HOL's free
    `r`, `temp`, `st`, `x` and `loc` are explicit binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r temp : Nat) (st : WordSemStateFiniteExact width C F) (x : WordLocW width)
    (loc : Spt (WordLocW width)) :
    r < temp ∧ getVar r st = some x ∧ wordLocalsRel temp st.locals loc →
      getVar r { st with locals := loc } = some x := by
  rintro ⟨hr, hg, hl⟩
  simp only [getVar] at hg ⊢
  rw [← hl r hr]
  exact hg

/-- Exact HOL `locals_rel_get_var_simp` (`wordPropsScript.sml:3434-3440`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_simp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_var_simp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r temp : Nat) (st : WordSemStateFiniteExact width C F) (loc : Spt (WordLocW width)) :
    r < temp ∧ wordLocalsRel temp st.locals loc →
      getVar r { st with locals := loc } = getVar r st := by
  rintro ⟨hr, hl⟩
  simp only [getVar]
  exact (hl r hr).symm

/-- Exact HOL `locals_rel_get_vars` (`wordPropsScript.sml:3399-3411`); HOL's free
    `st`, `temp` and `loc` are the outer binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_vars"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_vars {width : Nat} [NeZero width] {C : Type} {F : Type}
    (st : WordSemStateFiniteExact width C F) (temp : Nat) (loc : Spt (WordLocW width)) :
    ∀ (ls : List Nat) (vs : List (WordLocW width)),
      getVars ls st = some vs ∧ (∀ x ∈ ls, x < temp) ∧ wordLocalsRel temp st.locals loc →
        getVars ls { st with locals := loc } = some vs
  | [], vs, ⟨h, _, _⟩ => h
  | v :: ls, vs, ⟨h, hlt, hl⟩ => by
      simp only [getVars] at h ⊢
      rw [locals_rel_get_var_simp v temp st loc ⟨hlt v (List.mem_cons_self ..), hl⟩]
      cases hv : getVar v st with
      | none => rw [hv] at h; simp at h
      | some x =>
          rw [hv] at h
          simp only at h ⊢
          cases hvs : getVars ls st with
          | none => rw [hvs] at h; simp at h
          | some xs =>
              rw [hvs] at h
              rw [locals_rel_get_vars st temp loc ls xs
                ⟨hvs, fun y hy => hlt y (List.mem_cons_of_mem _ hy), hl⟩]
              exact h

/-- Exact HOL `locals_rel_get_vars_simp` (`wordPropsScript.sml:3442-3450`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_vars_simp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_vars_simp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : List Nat) (temp : Nat) (st : WordSemStateFiniteExact width C F)
    (loc : Spt (WordLocW width)) :
    (∀ x ∈ l, x < temp) ∧ wordLocalsRel temp st.locals loc →
      getVars l { st with locals := loc } = getVars l st := by
  rintro ⟨hlt, hl⟩
  induction l with
  | nil => rfl
  | cons v l ih =>
      simp only [getVars]
      rw [locals_rel_get_var_simp v temp st loc ⟨hlt v (List.mem_cons_self ..), hl⟩,
        ih (fun y hy => hlt y (List.mem_cons_of_mem _ hy))]

/-- Exact HOL `locals_rel_get_var_imm` (`wordPropsScript.sml:3452-3460`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_imm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_var_imm {width : Nat} [NeZero width] {C : Type} {F : Type}
    (temp : Nat) (r : WordRegImm (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (x : WordLocW width) (loc : Spt (WordLocW width)) :
    everyVarImmHOL (fun x => decide (x < temp)) r = true ∧ getVarImm r st = some x ∧
      wordLocalsRel temp st.locals loc →
      getVarImm r { st with locals := loc } = some x := by
  rintro ⟨he, hg, hl⟩
  cases r with
  | reg n =>
      simp only [everyVarImmHOL, decide_eq_true_eq] at he
      exact locals_rel_get_var n temp st x loc ⟨he, hg, hl⟩
  | imm w => exact hg

/-- Exact HOL `locals_rel_get_var_imm_simp` (`wordPropsScript.sml:3462-3470`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_get_var_imm_simp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_get_var_imm_simp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (temp : Nat) (r : WordRegImm (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (loc : Spt (WordLocW width)) :
    everyVarImmHOL (fun x => decide (x < temp)) r = true ∧ wordLocalsRel temp st.locals loc →
      getVarImm r { st with locals := loc } = getVarImm r st := by
  rintro ⟨he, hl⟩
  cases r with
  | reg n =>
      simp only [everyVarImmHOL, decide_eq_true_eq] at he
      exact locals_rel_get_var_simp n temp st loc ⟨he, hl⟩
  | imm w => rfl

/-- Exact HOL local `locals_rel_set_var` (`wordPropsScript.sml:3524-3530`); HOL's
    free `temp` and `v` are the outer binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_set_var"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_set_var {width : Nat} [NeZero width] (temp : Nat) (v : WordLocW width) :
    ∀ (n : Nat) (s t : Spt (WordLocW width)),
      wordLocalsRel temp s t → wordLocalsRel temp (sptInsert n v s) (sptInsert n v t) := by
  intro n s t h x hx
  by_cases hxn : x = n
  · subst hxn; rw [sptLookup_sptInsert_same, sptLookup_sptInsert_same]
  · rw [sptLookup_sptInsert_ne _ _ _ _ hxn, sptLookup_sptInsert_ne _ _ _ _ hxn]
    exact h x hx

/-- Exact HOL local `locals_rel_delete` (`wordPropsScript.sml:3532-3538`); HOL's
    free `temp` is the outer binder. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_delete"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_delete {width : Nat} [NeZero width] (temp : Nat) :
    ∀ (n : Nat) (s t : Spt (WordLocW width)),
      wordLocalsRel temp s t → wordLocalsRel temp (sptDelete n s) (sptDelete n t) := by
  intro n s t h x hx
  rw [sptLookup_sptDelete, sptLookup_sptDelete]
  split
  · rfl
  · exact h x hx

/-- Exact HOL `locals_rel_alist_insert` (`wordPropsScript.sml:3413-3422`); HOL's
    free `temp` is the outer binder. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_alist_insert"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_alist_insert {width : Nat} [NeZero width] (temp : Nat) :
    ∀ (ls : List Nat) (vs : List (WordLocW width)) (s t : Spt (WordLocW width)),
      wordLocalsRel temp s t ∧ (∀ x ∈ ls, x < temp) →
        wordLocalsRel temp (LoopSemStateFiniteExact.sptAlistInsert ls vs s)
          (LoopSemStateFiniteExact.sptAlistInsert ls vs t)
  | [], _, _, _, ⟨h, _⟩ => h
  | _ :: _, [], _, _, ⟨h, _⟩ => h
  | l :: ls, v :: vs, s, t, ⟨h, hlt⟩ =>
      locals_rel_set_var temp v l _ _
        (locals_rel_alist_insert temp ls vs s t ⟨h, fun x hx => hlt x (List.mem_cons_of_mem _ hx)⟩)

/-- Exact HOL `locals_rel_word_exp_simp` (`wordPropsScript.sml:3502-3522`); HOL's
    free `temp` and `loc` are the outer binders. HOL's `∀s exp w` also binds a
    `w` that occurs nowhere in the statement; that vacuous binder is omitted. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_word_exp_simp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_word_exp_simp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (temp : Nat) (loc : Spt (WordLocW width)) :
    ∀ (s : WordSemStateFiniteExact width C F) (exp : WordLangExpHOL (BitVec width)),
      everyVarExpHOL (fun x => decide (x < temp)) exp = true ∧ wordLocalsRel temp s.locals loc →
        wordExp { s with locals := loc } exp = wordExp s exp
  | s, .const _, _ => by simp only [wordExp]
  | s, .var v, ⟨he, hl⟩ => by
      simp only [everyVarExpHOL, decide_eq_true_eq] at he
      simp only [wordExp]
      exact locals_rel_get_var_simp v temp s loc ⟨he, hl⟩
  | s, .lookup _, _ => by simp only [wordExp]; rfl
  | s, .load e, ⟨he, hl⟩ => by
      simp only [everyVarExpHOL] at he
      simp only [wordExp]
      rw [locals_rel_word_exp_simp temp loc s e ⟨he, hl⟩]
      rfl
  | s, .op op ls, ⟨he, hl⟩ => by
      have hm : ∀ x ∈ ls, everyVarExpHOL (fun x => decide (x < temp)) x = true := by
        intro x hx
        have := he
        simp only [everyVarExpHOL] at this
        exact (Compiler.Backend.WordInst.everyVarExpsHOL_iff _ ls).mp this x hx
      rw [Compiler.Backend.WordInst.wordExp_op, Compiler.Backend.WordInst.wordExp_op]
      rw [List.map_congr_left (fun x hx => locals_rel_word_exp_simp temp loc s x ⟨hm x hx, hl⟩)]
  | s, .shift sh e1 e2, ⟨he, hl⟩ => by
      simp only [everyVarExpHOL, Bool.and_eq_true] at he
      simp only [wordExp]
      rw [locals_rel_word_exp_simp temp loc s e1 ⟨he.1, hl⟩,
        locals_rel_word_exp_simp temp loc s e2 ⟨he.2, hl⟩]
termination_by _ exp => sizeOf exp
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

/-- Exact HOL `locals_rel_word_exp` (`wordPropsScript.sml:3472-3500`); HOL's free
    `temp` and `loc` are the outer binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_word_exp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_word_exp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (temp : Nat) (loc : Spt (WordLocW width)) :
    ∀ (s : WordSemStateFiniteExact width C F) (exp : WordLangExpHOL (BitVec width))
      (w : WordLocW width),
      everyVarExpHOL (fun x => decide (x < temp)) exp = true ∧ wordExp s exp = some w ∧
        wordLocalsRel temp s.locals loc →
        wordExp { s with locals := loc } exp = some w := by
  rintro s exp w ⟨he, hw, hl⟩
  rw [locals_rel_word_exp_simp temp loc s exp ⟨he, hl⟩]
  exact hw

/-- One name set of `locals_rel_cut_envs` (Flapjack infrastructure; the HOL proof
    closes it with `lookup_inter`). -/
theorem localsRel_cutNames {width : Nat} [NeZero width] {γ : Type} (temp : Nat)
    (names : Spt γ) (loc loc' x : Spt (WordLocW width)) (hr : wordLocalsRel temp loc loc')
    (hn : ∀ k, sptDomain names k → k < temp)
    (hc : wordSemCutNames names loc = some x) : wordSemCutNames names loc' = some x := by
  have hsub : LoopSemStateFiniteExact.sptSubsetLive names loc := by
    by_cases h : LoopSemStateFiniteExact.sptSubsetLive names loc
    · exact h
    · simp [wordSemCutNames, h] at hc
  have hx : sptInter loc names = x := by simpa [wordSemCutNames, hsub] using hc
  subst x
  have htsub : LoopSemStateFiniteExact.sptSubsetLive names loc' := by
    intro k hk
    obtain ⟨v, hv⟩ := (sptMem_iff_lookup k loc).mp (hsub k hk)
    have hkd : sptDomain names k := by
      obtain ⟨u, hu⟩ := (sptMem_iff_lookup k names).mp hk
      simp [sptDomain, hu]
    exact (sptMem_iff_lookup k loc').mpr ⟨v, (hr k (hn k hkd)) ▸ hv⟩
  simp only [wordSemCutNames, htsub, if_true, Option.some.injEq]
  rw [sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩]
  intro k
  rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
  cases hk : sptLookup k names with
  | none => cases sptLookup k loc' <;> cases sptLookup k loc <;> rfl
  | some w =>
      have hkd : sptDomain names k := by simp [sptDomain, hk]
      rw [hr k (hn k hkd)]

/-- Exact HOL `locals_rel_cut_envs` (`wordPropsScript.sml:3540-3559`); HOL's free
    variables are explicit binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_cut_envs"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_cut_envs {width : Nat} [NeZero width] (temp : Nat)
    (loc loc' : Spt (WordLocW width)) (names : WordLangCutsetsHOL)
    (x : Spt (WordLocW width) × Spt (WordLocW width)) :
    wordLocalsRel temp loc loc' ∧ everyNameHOL (fun x => decide (x < temp)) names = true ∧
      wordSemCutEnvs names loc = some x →
      wordSemCutEnvs names loc' = some x := by
  rintro ⟨hr, hn, hc⟩
  simp only [everyNameHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
  have hn1 : ∀ k, sptDomain names.1 k → k < temp :=
    fun k hk => hn.1 k ((sptMemMapFstToAList names.1 k).mpr hk)
  have hn2 : ∀ k, sptDomain names.2 k → k < temp :=
    fun k hk => hn.2 k ((sptMemMapFstToAList names.2 k).mpr hk)
  unfold wordSemCutEnvs at hc ⊢
  cases h1 : wordSemCutNames names.1 loc with
  | none => rw [h1] at hc; cases hc
  | some e1 =>
      cases h2 : wordSemCutNames names.2 loc with
      | none => rw [h1, h2] at hc; cases hc
      | some e2 =>
          rw [h1, h2] at hc
          rw [localsRel_cutNames temp _ _ _ _ hr hn1 h1, localsRel_cutNames temp _ _ _ _ hr hn2 h2]
          exact hc

/-- Exact HOL `locals_rel_cut_env` (`wordPropsScript.sml:3561-3572`); HOL's free
    variables are explicit binders. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_cut_env"
  (words_as_type_indexed_bitvec)]
theorem locals_rel_cut_env {width : Nat} [NeZero width] (temp : Nat)
    (loc loc' : Spt (WordLocW width)) (names : WordLangCutsetsHOL) (x : Spt (WordLocW width)) :
    wordLocalsRel temp loc loc' ∧ everyNameHOL (fun x => decide (x < temp)) names = true ∧
      wordSemCutEnv names loc = some x →
      wordSemCutEnv names loc' = some x := by
  rintro ⟨hr, hn, hc⟩
  unfold wordSemCutEnv at hc ⊢
  cases h : wordSemCutEnvs names loc with
  | none => rw [h] at hc; cases hc
  | some e =>
      rw [h] at hc
      rw [locals_rel_cut_envs temp loc loc' names e ⟨hr, hn, h⟩]
      exact hc

/-! ## Replacing the locals (Flapjack infrastructure for `locals_rel_evaluate_thm`) -/

section WithLocals

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem withLocals_self (s : WordSemStateFiniteExact width C F) :
    { s with locals := s.locals } = s := rfl

theorem flushState_withLocals (b : Bool) (s : WordSemStateFiniteExact width C F)
    (a : Spt (WordLocW width)) : flushState b { s with locals := a } = flushState b s := by
  cases b <;> rfl

theorem popEnv_withLocals (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    popEnv { s with locals := a } = popEnv s := by
  unfold popEnv
  rfl

theorem jumpExc_withLocals (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    jumpExc { s with locals := a } = jumpExc s := by
  unfold jumpExc
  rfl

theorem pushEnv_withLocals (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    pushEnv envs h { s with locals := a } = { pushEnv envs h s with locals := a } := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> rfl

theorem memStore_withLocals (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width))
    (ad : BitVec width) (w : WordLocW width) :
    memStore ad w { s with locals := a } = (memStore ad w s).map (fun s' => { s' with locals := a }) := by
  unfold memStore
  by_cases h : s.mdomain ad = true <;> simp [h]

theorem gc_withLocals (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    gc { s with locals := a } = (gc s).map (fun s' => { s' with locals := a }) := by
  unfold gc
  dsimp only
  cases h1 : s.gcFun (wordSemEncStack s.stack, s.memory, s.mdomain, s.store) with
  | none => simp only [Option.map_none]
  | some r =>
      obtain ⟨wl, m, st⟩ := r
      simp only
      cases wordSemDecStack wl s.stack <;> simp only [Option.map_none, Option.map_some]

theorem alloc_withLocals (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width))
    (h : wordSemCutEnvs names a = wordSemCutEnvs names s.locals) :
    alloc w names { s with locals := a } = alloc w names s := by
  unfold alloc
  simp only [h]
  split
  · rfl
  · rename_i envs _
    have e : pushEnv envs none (setStore .allocSize (.word w) { s with locals := a }) =
        { pushEnv envs none (setStore .allocSize (.word w) s) with locals := a } := rfl
    rw [e, gc_withLocals]
    cases gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => rfl
    | some s1 => simp only [Option.map_some, popEnv_withLocals, flushState_withLocals]

theorem cutState_withLocals (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F)
    (a : Spt (WordLocW width)) (h : wordSemCutEnv names a = wordSemCutEnv names s.locals) :
    cutState names { s with locals := a } = cutState names s := by
  unfold cutState
  simp only [h]

theorem decClock_withLocals (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    decClock { s with locals := a } = { decClock s with locals := a } := rfl

theorem callEnv_withLocals (args : List (WordLocW width)) (ss : Option Nat)
    (s : WordSemStateFiniteExact width C F) (a : Spt (WordLocW width)) :
    callEnv args ss { s with locals := a } = callEnv args ss s := rfl

end WithLocals

/-! ## `locals_rel_evaluate_thm` cases (Flapjack infrastructure) -/

section EvaluateCases

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The result-dependent conclusion of HOL `locals_rel_evaluate_thm`. -/
def LrPost (temp : Nat) :
    Option (WordSemResult width) → Spt (WordLocW width) → Spt (WordLocW width) → Prop
  | none, l, l' => wordLocalsRel temp l l'
  | some (.break _), l, l' => wordLocalsRel temp l l'
  | some (.continue _), l, l' => wordLocalsRel temp l l'
  | some _, l, l' => l = l'

theorem lrPost_refl (temp : Nat) (res : Option (WordSemResult width)) (l : Spt (WordLocW width)) :
    LrPost temp res l l := by
  unfold LrPost
  split <;> first | exact fun _ _ => rfl | rfl

/-- HOL `locals_rel_evaluate_thm` for one program and state, as proved by induction. -/
def LrGoal (temp : Nat) (p : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : Prop :=
  ∀ (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
    (loc : Spt (WordLocW width)),
    evaluate p st = (res, rst) → res ≠ some .error →
      everyVarHOL (fun x => decide (x < temp)) p = true → wordLocalsRel temp st.locals loc →
      ∃ loc', evaluate p { st with locals := loc } = (res, { rst with locals := loc' }) ∧
        LrPost temp res rst.locals loc'

/-- A statement whose run is independent of the locals keeps the source locals. -/
theorem lrGoal_of_eq (temp : Nat) (p : WordLangProgHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F)
    (h : ∀ loc, everyVarHOL (fun x => decide (x < temp)) p = true →
      wordLocalsRel temp st.locals loc → evaluate p { st with locals := loc } = evaluate p st) :
    LrGoal temp p st := by
  intro res rst loc he _ hv hl
  exact ⟨rst.locals, by rw [h loc hv hl, he], lrPost_refl temp res rst.locals⟩

theorem lr_skip (temp : Nat) (st : WordSemStateFiniteExact width C F) : LrGoal temp .skip st := by
  intro res rst loc he _ _ hl
  rw [evaluate] at he ⊢
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨loc, rfl, hl⟩

theorem lr_break (temp k : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.break k) st := by
  intro res rst loc he _ _ hl
  rw [evaluate] at he ⊢
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨loc, rfl, hl⟩

theorem lr_continue (temp k : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.continue k) st := by
  intro res rst loc he _ _ hl
  rw [evaluate] at he ⊢
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨loc, rfl, hl⟩

theorem lr_tick (temp : Nat) (st : WordSemStateFiniteExact width C F) : LrGoal temp .tick st := by
  intro res rst loc he _ _ hl
  rw [evaluate] at he ⊢
  by_cases hz : st.clock = 0
  · have hz' : ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
    rw [if_pos hz']
    rw [if_pos hz] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨(flushState true st).locals, by rw [flushState_withLocals], rfl⟩
  · have hz' : ¬ ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
    rw [if_neg hz']
    rw [if_neg hz] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨loc, rfl, hl⟩

theorem lr_assign (temp v : Nat) (e : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.assign v e) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_word_exp_simp temp loc st e ⟨hv.2, hl⟩]
  cases hw : wordExp st e with
  | none => rw [hw] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some w =>
      rw [hw] at he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨sptInsert v w loc, ⟨rfl, rfl⟩, locals_rel_set_var temp w v _ _ hl⟩

theorem lr_get (temp v : Nat) (name : WordStoreHOL) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.get v name) st := by
  intro res rst loc he herr _ hl
  rw [evaluate] at he ⊢
  have hg : getStore name { st with locals := loc } = getStore name st := rfl
  rw [hg]
  cases hw : getStore name st with
  | none => rw [hw] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some w =>
      rw [hw] at he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨sptInsert v w loc, ⟨rfl, rfl⟩, locals_rel_set_var temp w v _ _ hl⟩

theorem lr_set (temp : Nat) (v : WordStoreHOL) (e : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.set v e) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_word_exp_simp temp loc st e ⟨hv, hl⟩]
  by_cases hb : v = .handler ∨ v = .bitmapBase
  · simp only [hb, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
  · simp only [hb, if_false] at he ⊢
    cases hw : wordExp st e with
    | none => rw [hw] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
    | some w =>
        rw [hw] at he
        simp only [Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨loc, ⟨rfl, rfl⟩, hl⟩

theorem lr_store (temp v : Nat) (e : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.store e v) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_word_exp_simp temp loc st e ⟨hv.2, hl⟩,
    locals_rel_get_var_simp v temp st loc ⟨hv.1, hl⟩]
  rcases hw : wordExp st e with _ | (a | _) <;> rcases hg : getVar v st with _ | w <;>
    rw [hw, hg] at he <;> simp only [Prod.mk.injEq] at he <;>
    first | exact absurd he.1.symm herr | skip
  simp only at he ⊢
  rw [memStore_withLocals]
  cases hm : memStore a w st with
  | none => rw [hm] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some s1 =>
      rw [hm] at he
      simp only [Prod.mk.injEq, Option.map_some] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨loc, ⟨rfl, rfl⟩, by rw [(memStoreConst a w st s1 hm).1]; exact hl⟩

theorem lr_opCurrHeap (temp : Nat) (b : BinOp) (dst src : Nat)
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.opCurrHeap b dst src) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  have hx : everyVarExpHOL (fun x => decide (x < temp))
      (.op b [.var src, .lookup .currHeap] : WordLangExpHOL (BitVec width)) = true := by
    simp [everyVarExpHOL, everyVarExpsHOL, hv.2]
  rw [locals_rel_word_exp_simp temp loc st _ ⟨hx, hl⟩]
  cases hw : wordExp st (.op b [.var src, .lookup .currHeap]) with
  | none => rw [hw] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some w =>
      rw [hw] at he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨sptInsert dst w loc, ⟨rfl, rfl⟩, locals_rel_set_var temp w dst _ _ hl⟩

theorem lr_locValue (temp r l1 : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.locValue r l1) st := by
  intro res rst loc he herr _ hl
  rw [evaluate] at he ⊢
  by_cases hc : sptMem l1 st.code
  · have hc' : sptMem l1 ({ st with locals := loc } : WordSemStateFiniteExact width C F).code := hc
    rw [if_pos hc] at he
    rw [if_pos hc']
    simp only [Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨sptInsert r (.loc l1 0) loc, ⟨rfl, rfl⟩, locals_rel_set_var temp _ r _ _ hl⟩
  · rw [if_neg hc] at he
    simp only [Prod.mk.injEq] at he
    exact absurd he.1.symm herr

theorem lr_move (temp pri : Nat) (moves : List (Nat × Nat))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.move pri moves) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  by_cases hd : (moves.map Prod.fst).Nodup
  · rw [if_pos hd] at he ⊢
    rw [locals_rel_get_vars_simp _ temp st loc ⟨hv.2, hl⟩]
    cases hg : getVars (moves.map Prod.snd) st with
    | none => rw [hg] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
    | some vs =>
        rw [hg] at he
        simp only [Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨LoopSemStateFiniteExact.sptAlistInsert (moves.map Prod.fst) vs loc, ⟨rfl, rfl⟩,
          locals_rel_alist_insert temp _ vs _ _ ⟨hl, hv.1⟩⟩
  · rw [if_neg hd] at he
    simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr

theorem lr_raise (temp n : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.raise n) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp n temp st loc ⟨hv, hl⟩, jumpExc_withLocals]
  cases hg : getVar n st with
  | none => rw [hg] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some w =>
      rw [hg] at he
      simp only at he ⊢
      cases hj : jumpExc st with
      | none => rw [hj] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
      | some j =>
          obtain ⟨s1, l1, l2⟩ := j
          rw [hj] at he
          simp only [Prod.mk.injEq] at he ⊢
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨s1.locals, ⟨rfl, rfl⟩, rfl⟩

theorem lr_return (temp n : Nat) (ms : List Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.return n ms) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp n temp st loc ⟨hv.1, hl⟩,
    locals_rel_get_vars_simp ms temp st loc ⟨hv.2, hl⟩, flushState_withLocals]
  rcases hg : getVar n st with _ | (_ | ⟨l1, l2⟩) <;> rcases hgs : getVars ms st with _ | ys <;>
    rw [hg, hgs] at he <;> simp only [Prod.mk.injEq] at he <;>
    first | exact absurd he.1.symm herr | skip
  simp only [Prod.mk.injEq] at he ⊢
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨(flushState false st).locals, ⟨rfl, rfl⟩, rfl⟩

theorem lr_codeBufferWrite (temp r1 r2 : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.codeBufferWrite r1 r2) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp r1 temp st loc ⟨hv.1, hl⟩,
    locals_rel_get_var_simp r2 temp st loc ⟨hv.2, hl⟩]
  rcases hg1 : getVar r1 st with _ | (w1 | _) <;> rcases hg2 : getVar r2 st with _ | (w2 | _) <;>
    rw [hg1, hg2] at he <;> simp only [Prod.mk.injEq] at he <;>
    first | exact absurd he.1.symm herr | skip
  simp only at he ⊢
  cases hb : wordSemBufferWrite st.codeBuffer w1 (w2.setWidth 8) with
  | none => rw [hb] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some cb =>
      rw [hb] at he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨loc, ⟨rfl, rfl⟩, hl⟩

theorem lr_dataBufferWrite (temp r1 r2 : Nat) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.dataBufferWrite r1 r2) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp r1 temp st loc ⟨hv.1, hl⟩,
    locals_rel_get_var_simp r2 temp st loc ⟨hv.2, hl⟩]
  rcases hg1 : getVar r1 st with _ | (w1 | _) <;> rcases hg2 : getVar r2 st with _ | (w2 | _) <;>
    rw [hg1, hg2] at he <;> simp only [Prod.mk.injEq] at he <;>
    first | exact absurd he.1.symm herr | skip
  simp only at he ⊢
  cases hb : wordSemBufferWrite st.dataBuffer w1 w2 with
  | none => rw [hb] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some db =>
      rw [hb] at he
      simp only [Prod.mk.injEq] at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨loc, ⟨rfl, rfl⟩, hl⟩

theorem lr_storeConsts (temp t1 t2 addr offset : Nat) (words : List (Bool × BitVec width))
    (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.storeConsts t1 t2 addr offset words) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp addr temp st loc ⟨hv.1.2, hl⟩,
    locals_rel_get_var_simp offset temp st loc ⟨hv.2, hl⟩]
  rcases hg1 : getVar addr st with _ | (a | _) <;> rcases hg2 : getVar offset st with _ | (off | _) <;>
    rw [hg1, hg2] at he <;> simp only [Prod.mk.injEq] at he <;>
    first | exact absurd he.1.symm herr | skip
  simp only at he ⊢
  have hd : wordSemConstAddresses a words
      ({ st with locals := loc } : WordSemStateFiniteExact width C F).mdomain =
      wordSemConstAddresses a words st.mdomain := rfl
  rw [hd]
  by_cases hc : ¬ wordSemConstAddresses a words st.mdomain = true
  · rw [if_pos hc] at he
    simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  · rw [if_neg hc] at he ⊢
    simp only [Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, ⟨rfl, rfl⟩, ?_⟩
    simp only [setVar, unsetVar]
    exact locals_rel_set_var temp _ _ _ _ (locals_rel_set_var temp _ _ _ _
      (locals_rel_delete temp _ _ _ (locals_rel_delete temp _ _ _ hl)))

theorem instReads_lt (temp : Nat) (i : WordLangInst (BitVec width))
    (h : everyVarInstHOL (fun x => decide (x < temp)) i = true) :
    ∀ x ∈ WordAlloc.instReads i, x < temp := by
  intro x hx
  unfold WordAlloc.instReads at hx
  split at hx
  all_goals first
    | (simp at hx; done)
    | (simp only [everyVarInstHOL, everyVarImmHOL, Bool.and_eq_true, decide_eq_true_eq] at h
       (try split at hx) <;> (try split at h) <;>
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
         (try simp only [Bool.and_eq_true, decide_eq_true_eq] at h) <;>
         omega)

theorem lr_inst (temp : Nat) (i : WordLangInst (BitVec width))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.inst i) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL] at hv
  rw [evaluate] at he ⊢
  cases hi : inst i st with
  | none => rw [hi] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some s1 =>
      rw [hi] at he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨t', ht, hfr, hwr, hst⟩ := WordAlloc.instCongr i st s1 loc st.store hi
        (fun x v hx hv' => by rw [← hl x (instReads_lt temp i hv x hx)]; exact hv')
      have e : ({ st with locals := loc, store := st.store } : WordSemStateFiniteExact width C F) =
          { st with locals := loc } := rfl
      rw [e] at ht
      rw [ht]
      refine ⟨t', ?_, ?_⟩
      · rw [← hst]
      · intro k hk
        by_cases hw : k ∈ WordAlloc.instWrites i
        · exact (hwr k hw).symm
        · obtain ⟨h1, h2⟩ := hfr k hw
          rw [h1, h2]
          exact hl k hk

theorem lr_alloc (temp n : Nat) (names : WordLangCutsetsHOL)
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.alloc n names) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp n temp st loc ⟨hv.1, hl⟩]
  rcases hg : getVar n st with _ | (w | _) <;> rw [hg] at he <;> simp only at he ⊢ <;>
    first | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr) | skip
  cases hc : wordSemCutEnvs names st.locals with
  | none =>
      unfold alloc at he
      rw [hc] at he
      simp only [Prod.mk.injEq] at he
      exact absurd he.1.symm herr
  | some e =>
      have hc' := locals_rel_cut_envs temp st.locals loc names e ⟨hl, hv.2, hc⟩
      rw [alloc_withLocals w names st loc (hc'.trans hc.symm), he]
      exact ⟨rst.locals, rfl, lrPost_refl temp res rst.locals⟩

theorem lr_install (temp ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.install ptr len dptr dlen names) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  cases hc : wordSemCutEnv names st.locals with
  | none => rw [hc] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some env =>
      rw [locals_rel_cut_env temp st.locals loc names env ⟨hl, hv.2, hc⟩]
      rw [hc] at he
      simp only at he ⊢
      rw [locals_rel_get_var_simp ptr temp st loc ⟨hv.1.1.1.1, hl⟩,
        locals_rel_get_var_simp len temp st loc ⟨hv.1.1.1.2, hl⟩,
        locals_rel_get_var_simp dptr temp st loc ⟨hv.1.1.2, hl⟩,
        locals_rel_get_var_simp dlen temp st loc ⟨hv.1.2, hl⟩]
      refine ⟨rst.locals, ?_, lrPost_refl temp res rst.locals⟩
      change _ = (res, rst)
      repeat' split at he
      all_goals first
        | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr)
        | (rw [← he]; simp only [*, and_self, if_true])

theorem lr_ffi (temp : Nat) (idx : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.ffi idx ptr1 len1 ptr2 len2 names) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_get_var_simp len1 temp st loc ⟨hv.1.1.1.2, hl⟩,
    locals_rel_get_var_simp ptr1 temp st loc ⟨hv.1.1.1.1, hl⟩,
    locals_rel_get_var_simp len2 temp st loc ⟨hv.1.2, hl⟩,
    locals_rel_get_var_simp ptr2 temp st loc ⟨hv.1.1.2, hl⟩]
  refine ⟨rst.locals, ?_, lrPost_refl temp res rst.locals⟩
  change _ = (res, rst)
  repeat' split at he
  all_goals first
    | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr)
    | skip
  all_goals
    have hc' := locals_rel_cut_env temp st.locals loc names _
      ⟨hl, hv.2, ‹wordSemCutEnv names st.locals = some _›⟩
    try simp only at he
    rw [← he]
    simp only [*, flushState_withLocals]

set_option linter.unusedSimpArgs false in
theorem lr_shareInst (temp : Nat) (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.shareInst op v exp) st := by
  intro res rst loc he herr hv hl
  simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [evaluate] at he ⊢
  rw [locals_rel_word_exp_simp temp loc st exp ⟨hv.2, hl⟩]
  have hg := locals_rel_get_var_simp v temp st loc ⟨hv.1, hl⟩
  rcases hw : wordExp st exp with _ | (ad | _) <;> rw [hw] at he <;> simp only at he ⊢ <;>
    first | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr) | skip
  cases op <;>
    simp only [shareInst, shMemSetVar, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32,
      shMemStore, shMemStoreByte, shMemStore16, shMemStore32, hg] at he ⊢
  all_goals (repeat' split at he)
  all_goals first
    | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr)
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
       exact ⟨_, by simp only [*, flushState_withLocals, if_true], rfl⟩)
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
       exact ⟨loc, by simp only [*, if_true], hl⟩)
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
       refine ⟨_, ?_, locals_rel_set_var temp _ _ _ _ hl⟩
       simp only [*, setVar, if_true])

theorem lr_loop (temp : Nat) (names : WordLangNumSetHOL) (c : WordLangProgHOL (BitVec width))
    (exitNames : WordLangNumSetHOL) (st : WordSemStateFiniteExact width C F) :
    LrGoal temp (.loop names c exitNames) st := by
  intro res rst loc he herr hv hl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn : everyNameHOL (fun x => decide (x < temp)) (names, Spt.ln) = true := by
    simp only [everyVarHOL, Bool.and_eq_true] at hv
    simp only [everyNameHOL, hv.1.1, Bool.true_and]
    rfl
  rw [ht] at he
  cases hc : wordSemCutEnv (names, .ln) st.locals with
  | none =>
      have : cutState (names, .ln) st = none := by unfold cutState; rw [hc]
      rw [this] at he
      simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some env =>
      have hc' := locals_rel_cut_env temp st.locals loc (names, .ln) env ⟨hl, hn, hc⟩
      have hcs : cutState (names, .ln) st = some { st with locals := env } := by
        unfold cutState; rw [hc]
      refine ⟨rst.locals, ?_, lrPost_refl temp res rst.locals⟩
      rw [ht, cutState_withLocals _ st loc (hc'.trans hc.symm), hcs]
      rw [hcs] at he
      exact he

theorem lr_call (temp : Nat)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (st : WordSemStateFiniteExact width C F) : LrGoal temp (.call ret dest args handler) st := by
  intro res rst loc he herr hv hl
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hargs : ∀ x ∈ args, x < temp := by
    rcases ret with _ | ⟨n, names, retHandler, l1, l2⟩ <;>
      rcases handler with _ | ⟨a, b, c, d⟩ <;>
      simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv <;>
      first | exact hv | exact hv.1
  have hnames : ∀ n names r l1 l2, ret = some (n, names, r, l1, l2) →
      everyNameHOL (fun x => decide (x < temp)) names = true := by
    intro n names r l1 l2 hr
    subst hr
    rcases handler with _ | ⟨a, b, c, d⟩ <;>
      simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv <;>
      exact hv.2.1.1.2
  rw [ht] at he ⊢
  rw [locals_rel_get_vars_simp args temp st loc ⟨hargs, hl⟩]
  refine ⟨rst.locals, ?_, lrPost_refl temp res rst.locals⟩
  change _ = (res, rst)
  rw [← he]
  cases hg : getVars args st with
  | none => rw [hg] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
  | some xs =>
      rw [hg] at he
      simp only at he ⊢
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
      simp only [hbad, Bool.false_eq_true, if_false] at he ⊢
      cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) st.code st.stackSize with
      | none => rw [hf] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
      | some fc =>
          obtain ⟨args1, prog, ss⟩ := fc
          rw [hf] at he
          simp only at he ⊢
          cases ret with
          | none =>
              cases handler with
              | some _ => simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
              | none =>
                  simp only
                  by_cases hz : st.clock = 0
                  · have hz' : ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
                    rw [if_pos hz', if_pos hz, flushState_withLocals]
                  · have hz' : ¬ ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
                    rw [if_neg hz', if_neg hz]
                    rfl
          | some rv =>
              obtain ⟨n, names, retHandler, l1, l2⟩ := rv
              have hnm := hnames n names retHandler l1 l2 rfl
              simp only at he ⊢
              by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
              · simp only [hdc, if_true, Prod.mk.injEq] at he; exact absurd he.1.symm herr
              simp only [hdc, if_false] at he ⊢
              cases hce : wordSemCutEnvs names st.locals with
              | none => rw [hce] at he; simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
              | some envs =>
                  have hce' := locals_rel_cut_envs temp st.locals loc names envs
                    ⟨hl, hnm, hce⟩
                  rw [hce']
                  simp only
                  have e1 : callEnv args1 ss (pushEnv envs handler (decClock { st with locals := loc })) =
                      callEnv args1 ss (pushEnv envs handler (decClock st)) := by
                    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
                  have e2 : (callEnv args1 ss (pushEnv envs handler { st with locals := loc })).stackMax =
                      (callEnv args1 ss (pushEnv envs handler st)).stackMax := by
                    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
                  rw [e1, e2]
                  by_cases hz : st.clock = 0
                  · have hz' : ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
                    rw [if_pos hz', if_pos hz]
                    rfl
                  · have hz' : ¬ ({ st with locals := loc } : WordSemStateFiniteExact width C F).clock = 0 := hz
                    rw [if_neg hz', if_neg hz]

/-- `locals_rel_evaluate_thm` by recursion on `evaluate`'s measure (HOL:
    `completeInduct_on prog_size`). -/
theorem lr_aux (temp : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F),
      LrGoal temp p st
  | .mustTerminate q, st => by
      intro res rst loc he herr hv hl
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyVarHOL] at hv
      rw [ht] at he ⊢
      by_cases hz : st.termdep = 0
      · rw [if_pos hz] at he
        simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
      · have hz' : ¬ ({ st with locals := loc } : WordSemStateFiniteExact width C F).termdep = 0 := hz
        rw [if_neg hz] at he
        rw [if_neg hz']
        rcases hq : evaluate q { st with
            clock := wordSemMustTerminateLimit width
            termdep := st.termdep - 1 } with ⟨r, s1⟩
        rw [hq] at he
        have hr : r ≠ some .error := by
          rintro rfl
          simp only [Prod.mk.injEq] at he; exact herr he.1.symm
        obtain ⟨loc', h1, h2⟩ := lr_aux temp q { st with
            clock := wordSemMustTerminateLimit width
            termdep := st.termdep - 1 } r s1 loc hq hr hv hl
        have e : ({ ({ st with locals := loc } : WordSemStateFiniteExact width C F) with
            clock := wordSemMustTerminateLimit width
            termdep := ({ st with locals := loc } : WordSemStateFiniteExact width C F).termdep - 1 }) =
            { ({ st with
              clock := wordSemMustTerminateLimit width
              termdep := st.termdep - 1 } : WordSemStateFiniteExact width C F) with locals := loc } := rfl
        rw [e, h1]
        rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp only [Prod.mk.injEq] at he ⊢ <;>
          first
            | exact absurd he.1.symm herr
            | (obtain ⟨rfl, rfl⟩ := he; exact ⟨loc', ⟨rfl, rfl⟩, h2⟩)
  | .seq c1 c2, st => by
      intro res rst loc he herr hv hl
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyVarHOL, Bool.and_eq_true] at hv
      rw [ht] at he ⊢
      rcases h1 : evaluate c1 st with ⟨r1, s1⟩
      rw [h1] at he
      have hc1 := evaluate_clock c1 st r1 s1 h1
      have hr1 : r1 ≠ some .error := by
        rintro rfl
        simp only [Prod.mk.injEq] at he; exact herr he.1.symm
      obtain ⟨loc1, e1, p1⟩ := lr_aux temp c1 st r1 s1 loc h1 hr1 hv.1 hl
      rw [e1]
      cases r1 with
      | none => exact lr_aux temp c2 s1 res rst loc1 he herr hv.2 p1
      | some x =>
          simp only [Prod.mk.injEq] at he ⊢
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨loc1, ⟨rfl, rfl⟩, p1⟩
  | .ite cmp r1 ri c1 c2, st => by
      intro res rst loc he herr hv hl
      have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      simp only [everyVarHOL, Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [ht] at he ⊢
      rw [locals_rel_get_var_simp r1 temp st loc ⟨hv.1.1.1, hl⟩,
        locals_rel_get_var_imm_simp temp ri st loc ⟨hv.1.1.2, hl⟩]
      rcases hx : getVar r1 st with _ | x <;> rcases hy : getVarImm ri st with _ | y <;>
        simp only [hx, hy] at he ⊢ <;>
        first | (simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr) | skip
      rcases hc : wordSemWordCmp cmp x y with _ | _ | _ <;> simp only [hc] at he ⊢
      · simp only [Prod.mk.injEq] at he; exact absurd he.1.symm herr
      · exact lr_aux temp c2 st res rst loc he herr hv.2 hl
      · exact lr_aux temp c1 st res rst loc he herr hv.1.2 hl
  | .loop names c exitNames, st => lr_loop temp names c exitNames st
  | .call ret dest args handler, st => lr_call temp ret dest args handler st
  | .skip, st => lr_skip temp st
  | .move a b, st => lr_move temp a b st
  | .inst a, st => lr_inst temp a st
  | .assign a b, st => lr_assign temp a b st
  | .get a b, st => lr_get temp a b st
  | .set a b, st => lr_set temp a b st
  | .store a b, st => lr_store temp b a st
  | .alloc a b, st => lr_alloc temp a b st
  | .storeConsts a b c d f, st => lr_storeConsts temp a b c d f st
  | .raise a, st => lr_raise temp a st
  | WordLangProgHOL.return a b, st => lr_return temp a b st
  | WordLangProgHOL.break a, st => lr_break temp a st
  | WordLangProgHOL.continue a, st => lr_continue temp a st
  | .tick, st => lr_tick temp st
  | .opCurrHeap a b c, st => lr_opCurrHeap temp a b c st
  | .locValue a b, st => lr_locValue temp a b st
  | .install a b c d f, st => lr_install temp a b c d f st
  | .codeBufferWrite a b, st => lr_codeBufferWrite temp a b st
  | .dataBufferWrite a b, st => lr_dataBufferWrite temp a b st
  | .ffi a b c d f g, st => lr_ffi temp a b c d f g st
  | .shareInst a b c, st => lr_shareInst temp a b c st
termination_by p st => (st.termdep, st.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc1 with ⟨_, _⟩)
    omega

end EvaluateCases

/-- Exact HOL `locals_rel_evaluate_thm` (`wordPropsScript.sml:3575-3850`, with
    every `Resume` case): extra temporaries at or above `temp` do not affect
    evaluation of a program whose variables are all below `temp`.  HOL's
    `res ≠ SOME Error` and `every_var (λx. x < temp)` premises are kept; the
    conclusion is HOL's case split on the result.  Inherits
    `reals_as_rational_cuts` through `evaluate`. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "locals_rel_evaluate_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem locals_rel_evaluate_thm {width : Nat} [NeZero width] {C : Type} {F : Type} :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (res : Option (WordSemResult width)) (rst : WordSemStateFiniteExact width C F)
      (loc : Spt (WordLocW width)) (temp : Nat),
      evaluate prog st = (res, rst) ∧ res ≠ some .error ∧
        everyVarHOL (fun x => decide (x < temp)) prog = true ∧ wordLocalsRel temp st.locals loc →
      ∃ loc', evaluate prog { st with locals := loc } = (res, { rst with locals := loc' }) ∧
        match res with
        | none => wordLocalsRel temp rst.locals loc'
        | some (.break _) => wordLocalsRel temp rst.locals loc'
        | some (.continue _) => wordLocalsRel temp rst.locals loc'
        | some _ => rst.locals = loc' := by
  rintro prog st res rst loc temp ⟨he, herr, hv, hl⟩
  obtain ⟨loc', h1, h2⟩ := lr_aux temp prog st res rst loc he herr hv hl
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact ⟨loc', h1, h2⟩

end WordSemStateFiniteExact

end Flapjack
