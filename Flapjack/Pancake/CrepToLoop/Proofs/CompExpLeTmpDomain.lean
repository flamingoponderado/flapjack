import Flapjack.Pancake.CrepToLoop.Proofs.CompExpTmpBound
import Flapjack.Pancake.CrepToLoop.StateRel
import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.Semantics.LoopProps.EvalExact

/-!
# crep_to_loop `compile_exp_le_tmp_domain`

Counterpart of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`compile_exp_le_tmp_domain_cases` (line 682) and its two projections (769-770)
over the exact `compileExpHOLExact`/`compileExpsHOLExact`
(bead `flapjack-pxn.18.5.6.32.2`).
-/

namespace Flapjack

theorem sptListInsert_mono (k : Nat) :
    ∀ (ks : List Nat) (t : NumSet), (sptLookup k t).isSome = true →
      (sptLookup k (sptListInsert ks t)).isSome = true
  | [], t, h => h
  | key :: ks, t, h => by
      simp only [sptListInsert]
      apply sptListInsert_mono k ks
      rw [sptLookup_sptInsert]; split <;> simp_all

theorem sptListInsert_mem (k : Nat) :
    ∀ (ks : List Nat) (t : NumSet), k ∈ ks → (sptLookup k (sptListInsert ks t)).isSome = true
  | [], t, h => by simp at h
  | key :: ks, t, h => by
      simp only [sptListInsert]
      rcases List.mem_cons.mp h with rfl | h
      · apply sptListInsert_mono; rw [sptLookup_sptInsert, if_pos rfl]; rfl
      · exact sptListInsert_mem k ks _ h

variable {width : Nat} [NeZero width]

mutual
theorem compileExpHOLExact_domain_mono (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (e : CrepExpHOL width) (k : Nat), (sptLookup k l).isSome = true →
      (sptLookup k (compileExpHOLExact ct tmp l e).2.2.2).isSome = true
  | .baseAddr, k, h | .topAddr, k, h | .const _, k, h | .var _, k, h | .loadGlob _, k, h => by
      simp only [compileExpHOLExact]; exact h
  | .load a, k, h => by
      have ih := compileExpHOLExact_domain_mono ct tmp l a k h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]; exact ih
  | .load32 a, k, h | .loadByte a, k, h => by
      have ih := compileExpHOLExact_domain_mono ct tmp l a k h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]
      rw [sptLookup_sptInsert]; split <;> simp_all
  | .op o es, k, h => by
      have ih := compileExpsHOLExact_domain_mono ct tmp l es k h
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]; exact ih
  | .crepOp o es, k, h => by
      have ih := compileExpsHOLExact_domain_mono ct tmp l es k h
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih; simp only [compileExpHOLExact, hA]
      rw [sptLookup_sptInsert]; split
      · rfl
      · exact sptListInsert_mono k _ _ ih
  | .cmp o a b, k, h => by
      have iha := compileExpHOLExact_domain_mono ct tmp l a k h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      have ihb := compileExpHOLExact_domain_mono ct m ol b k iha
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      simp only [compileExpHOLExact, hA, hB]; exact sptListInsert_mono k _ _ ihb
  | .shift o a b, k, h => by
      have iha := compileExpHOLExact_domain_mono ct tmp l a k h
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      have ihb := compileExpHOLExact_domain_mono ct m ol b k iha
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      simp only [compileExpHOLExact, hA, hB]; exact ihb
termination_by e => sizeOf e

theorem compileExpsHOLExact_domain_mono (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ (es : List (CrepExpHOL width)) (k : Nat), (sptLookup k l).isSome = true →
      (sptLookup k (compileExpsHOLExact ct tmp l es).2.2.2).isSome = true
  | [], k, h => by simp only [compileExpsHOLExact]; exact h
  | e :: es, k, h => by
      have iha := compileExpHOLExact_domain_mono ct tmp l e k h
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha; simp only at iha
      have ihb := compileExpsHOLExact_domain_mono ct m ol es k iha
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', v', m', ol'⟩
      rw [hB] at ihb; simp only at ihb
      simp only [compileExpsHOLExact, hA, hB]; exact ihb
termination_by es => sizeOf es
end

theorem crepExpVarsHOLList_eq_flatten :
    ∀ es : List (CrepExpHOL width), crepExpVarsHOLList es = (es.map crepExpVarsHOL).flatten
  | [] => by simp [crepExpVarsHOLList]
  | e :: es => by simp [crepExpVarsHOLList, crepExpVarsHOLList_eq_flatten es]

theorem holLoopLocalsTouched_op (o : BinOp) (les : List (HolLoopExp width)) :
    holLoopLocalsTouched (.op o les) = (les.map holLoopLocalsTouched).flatten := by
  simp only [holLoopLocalsTouched, List.attach_map_val (f := holLoopLocalsTouched)]

mutual
theorem compileExpHOLExact_le_tmp_domain (ct : CrepToLoopContextExact)
    (hmax : crepToLoopCtxtMax ct.vmax ct.vars.lookup) (tmp : Nat) (l : NumSet) :
    ∀ (e : CrepExpHOL width) (n : Nat), ct.vmax < tmp →
      (∀ v, v ∈ crepExpVarsHOL e → ∃ m, ct.vars.lookup v = some m ∧ (sptLookup m l).isSome = true) →
      n ∈ holLoopLocalsTouched (compileExpHOLExact ct tmp l e).2.1 →
      n < (compileExpHOLExact ct tmp l e).2.2.1 ∧
        (sptLookup n (compileExpHOLExact ct tmp l e).2.2.2).isSome = true
  | .baseAddr, n, _, _, h | .topAddr, n, _, _, h | .const _, n, _, _, h | .loadGlob _, n, _, _, h => by
      simp [compileExpHOLExact, holLoopLocalsTouched] at h
  | .var v, n, ht, hv, h => by
      obtain ⟨m, hm, hml⟩ := hv v (by simp [crepExpVarsHOL])
      simp only [compileExpHOLExact, hm, holLoopLocalsTouched, List.mem_singleton] at h ⊢
      rw [h]
      exact ⟨Nat.lt_of_le_of_lt (hmax v m hm) ht, hml⟩
  | .load a, n, ht, hv, h => by
      have ih := compileExpHOLExact_le_tmp_domain ct hmax tmp l a n ht
        (fun v hv' => hv v (by simpa [crepExpVarsHOL] using hv'))
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA, holLoopLocalsTouched] at h ⊢; exact ih h
  | .load32 a, n, ht, hv, h | .loadByte a, n, ht, hv, h => by
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      simp only [compileExpHOLExact, hA, holLoopLocalsTouched, List.mem_singleton] at h ⊢
      subst h
      refine ⟨Nat.lt_succ_self _, ?_⟩
      rw [sptLookup_sptInsert, if_pos rfl]; rfl
  | .op o es, n, ht, hv, h => by
      have ih := compileExpsHOLExact_le_tmp_domain ct hmax tmp l es n ht
        (fun v hv' => hv v (by simpa [crepExpVarsHOL, crepExpVarsHOLList_eq_flatten] using hv'))
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp only at ih
      simp only [compileExpHOLExact, hA, holLoopLocalsTouched_op] at h ⊢; exact ih h
  | .crepOp o es, n, ht, hv, h => by
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      simp only [compileExpHOLExact, hA] at h ⊢
      rcases hB : compileCrepopHOLExact (width := width) o ct.target m (m + 1) (m + vs.length)
        (sptListInsert ((List.range vs.length).map (fun offset => m + offset)) ol) with ⟨oc, d⟩
      rw [hB] at h; simp only [holLoopLocalsTouched, List.mem_singleton] at h ⊢
      subst h
      refine ⟨Nat.lt_succ_self _, ?_⟩
      rw [sptLookup_sptInsert, if_pos rfl]; rfl
  | .cmp o a b, n, ht, hv, h => by
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      simp only [compileExpHOLExact, hA, hB, holLoopLocalsTouched, List.mem_singleton] at h ⊢
      subst h
      exact ⟨by omega, sptListInsert_mem _ _ _ (by simp)⟩
  | .shift o a b, n, ht, hv, h => by
      have hle := compileExpHOLExact_tmp_le ct tmp l a
      have iha := compileExpHOLExact_le_tmp_domain ct hmax tmp l a n ht
        (fun v hv' => hv v (by simp [crepExpVarsHOL, hv']))
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha hle; simp only at iha hle
      have ihb := compileExpHOLExact_le_tmp_domain ct hmax m ol b n (by omega)
        (fun v hv' => by
          obtain ⟨k, hk, hkl⟩ := hv v (by simp [crepExpVarsHOL, hv'])
          refine ⟨k, hk, ?_⟩
          have := compileExpHOLExact_domain_mono ct tmp l a k hkl
          rw [hA] at this; exact this)
      have hleb := compileExpHOLExact_tmp_le ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb hleb; simp only at ihb hleb
      simp only [compileExpHOLExact, hA, hB, holLoopLocalsTouched, List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := iha h
        refine ⟨by omega, ?_⟩
        have := compileExpHOLExact_domain_mono ct m ol b n h2
        rw [hB] at this; exact this
      · exact ihb h
termination_by e => sizeOf e

theorem compileExpsHOLExact_le_tmp_domain (ct : CrepToLoopContextExact)
    (hmax : crepToLoopCtxtMax ct.vmax ct.vars.lookup) (tmp : Nat) (l : NumSet) :
    ∀ (es : List (CrepExpHOL width)) (n : Nat), ct.vmax < tmp →
      (∀ v, v ∈ (es.map crepExpVarsHOL).flatten →
        ∃ m, ct.vars.lookup v = some m ∧ (sptLookup m l).isSome = true) →
      n ∈ ((compileExpsHOLExact ct tmp l es).2.1.map holLoopLocalsTouched).flatten →
      n < (compileExpsHOLExact ct tmp l es).2.2.1 ∧
        (sptLookup n (compileExpsHOLExact ct tmp l es).2.2.2).isSome = true
  | [], n, _, _, h => by simp [compileExpsHOLExact] at h
  | e :: es, n, ht, hv, h => by
      have hle := compileExpHOLExact_tmp_le ct tmp l e
      have iha := compileExpHOLExact_le_tmp_domain ct hmax tmp l e n ht
        (fun v hv' => hv v (by simp [hv']))
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha hle; simp only at iha hle
      have ihb := compileExpsHOLExact_le_tmp_domain ct hmax m ol es n (by omega)
        (fun w hw => by
          obtain ⟨k, hk, hkl⟩ := hv w (by simp only [List.map_cons, List.flatten_cons, List.mem_append]; exact Or.inr hw)
          refine ⟨k, hk, ?_⟩
          have := compileExpHOLExact_domain_mono ct tmp l e k hkl
          rw [hA] at this; exact this)
      have hleb := compileExpsHOLExact_tmp_le ct m ol es
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', vs', m', ol'⟩
      rw [hB] at ihb hleb; simp only at ihb hleb
      simp only [compileExpsHOLExact, hA, hB, List.map_cons, List.flatten_cons,
        List.mem_append] at h ⊢
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := iha h
        refine ⟨by omega, ?_⟩
        have := compileExpsHOLExact_domain_mono ct m ol es n h2
        rw [hB] at this; exact this
      · exact ihb h
termination_by es => sizeOf es
end

namespace CrepToLoopCompExpLeTmpDomainWitnesses

/-- Same-module re-export of the canonical finite-support witness for the
    `crep_to_loop$context` carrier, required by the `fmap_as_finite_support`
    qualifier on the `compile_exp_le_tmp_domain` ports below. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

end CrepToLoopCompExpLeTmpDomainWitnesses

/-- Exact HOL `compile_exp_le_tmp_domain_cases`
    (`crep_to_loopProofScript.sml:682-692`).  `ctxt_max ct.vmax ct.vars` is the
    tagged `crepToLoopCtxtMax` applied to the map's lookup, `FLOOKUP` is
    `HolFiniteMapExact.lookup`, `m ∈ domain l` is `(sptLookup m l).isSome`, and
    `var_cexp`/`locals_touched` are the tagged `crepExpVarsHOL`/`holLoopLocalsTouched`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_le_tmp_domain_cases"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exp_le_tmp_domain_cases :
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (tmp' : Nat) (l' : NumSet) (n : Nat),
      crepToLoopCtxtMax ct.vmax ct.vars.lookup ∧
      compileExpHOLExact ct tmp l e = (p, le, tmp', l') ∧ ct.vmax < tmp ∧
      (∀ n, n ∈ crepExpVarsHOL e → ∃ m, ct.vars.lookup n = some m ∧ (sptLookup m l).isSome = true) ∧
      n ∈ holLoopLocalsTouched le →
      n < tmp' ∧ (sptLookup n l').isSome = true) ∧
    (∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (es : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (tmp' : Nat) (l' : NumSet)
      (n : Nat),
      crepToLoopCtxtMax ct.vmax ct.vars.lookup ∧
      compileExpsHOLExact ct tmp l es = (p, les, tmp', l') ∧ ct.vmax < tmp ∧
      (∀ n, n ∈ (es.map crepExpVarsHOL).flatten →
        ∃ m, ct.vars.lookup n = some m ∧ (sptLookup m l).isSome = true) ∧
      n ∈ (les.map holLoopLocalsTouched).flatten →
      n < tmp' ∧ (sptLookup n l').isSome = true) :=
  ⟨fun ct tmp l e p le tmp' l' n ⟨hmax, h, ht, hv, hn⟩ => by
      have := compileExpHOLExact_le_tmp_domain ct hmax tmp l e n ht hv
      rw [h] at this; exact this hn,
   fun ct tmp l es p les tmp' l' n ⟨hmax, h, ht, hv, hn⟩ => by
      have := compileExpsHOLExact_le_tmp_domain ct hmax tmp l es n ht hv
      rw [h] at this; exact this hn⟩

/-- Exact HOL `compile_exp_le_tmp_domain`
    (`crep_to_loopProofScript.sml:769`, `CONJUNCT1` of the cases theorem). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exp_le_tmp_domain"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exp_le_tmp_domain :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (e : CrepExpHOL width)
      (p : List (HolLoopProg width)) (le : HolLoopExp width) (tmp' : Nat) (l' : NumSet) (n : Nat),
      crepToLoopCtxtMax ct.vmax ct.vars.lookup ∧
      compileExpHOLExact ct tmp l e = (p, le, tmp', l') ∧ ct.vmax < tmp ∧
      (∀ n, n ∈ crepExpVarsHOL e → ∃ m, ct.vars.lookup n = some m ∧ (sptLookup m l).isSome = true) ∧
      n ∈ holLoopLocalsTouched le →
      n < tmp' ∧ (sptLookup n l').isSome = true :=
  compile_exp_le_tmp_domain_cases.1

/-- Exact HOL `compile_exps_le_tmp_domain`
    (`crep_to_loopProofScript.sml:770`, `CONJUNCT2` of the cases theorem). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "compile_exps_le_tmp_domain"
  (fmap_as_finite_support := [vars, funcs]) (words_as_type_indexed_bitvec)]
theorem compile_exps_le_tmp_domain :
    ∀ (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) (es : List (CrepExpHOL width))
      (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (tmp' : Nat) (l' : NumSet)
      (n : Nat),
      crepToLoopCtxtMax ct.vmax ct.vars.lookup ∧
      compileExpsHOLExact ct tmp l es = (p, les, tmp', l') ∧ ct.vmax < tmp ∧
      (∀ n, n ∈ (es.map crepExpVarsHOL).flatten →
        ∃ m, ct.vars.lookup n = some m ∧ (sptLookup m l).isSome = true) ∧
      n ∈ (les.map holLoopLocalsTouched).flatten →
      n < tmp' ∧ (sptLookup n l').isSome = true :=
  compile_exp_le_tmp_domain_cases.2

end Flapjack
