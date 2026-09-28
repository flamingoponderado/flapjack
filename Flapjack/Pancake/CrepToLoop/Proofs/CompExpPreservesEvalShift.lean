import Flapjack.Pancake.CrepToLoop.Proofs.CompExpLeTmpDomain
import Flapjack.Pancake.CrepToLoop.Proofs.CompExpOutRel
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkEvalExact
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

/-!
# `comp_exp_preserves_eval`: Shift case

Case piece of HOL `comp_exp_preserves_eval`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:772-781`, Shift case at
1084-1127) over the exact carriers: `CrepSemHOLState`/`CrepExpHOL`/
`CrepToLoopContextExact`/`LoopSemStateFiniteExact`, the exact `compile_exp_def`
port `compileExpHOLExact`, the exact Crep evaluator `evalCrepSemHOLExp`, the exact
loop evaluator `LoopSemStateFiniteExact.evaluate`, and the exact relations
`crepToLoopStateRelExact`/`crepToLoopMemRelHOLExact`/`crepToLoopGlobalsRelHOLExact`/
`crepToLoopCodeRelExact`/`crepToLoopLocalsRelExact`.

FLAPJACK-SPECIFIC (not a tagged HOL port, so no `@[hol]` annotation): this is one
case of the HOL induction with the HOL hypotheses/conclusion shape plus exactly the
two sub-expression induction hypotheses, so the `@[hol "comp_exp_preserves_eval"]`
tag is carried by the assembling theorem (bead `flapjack-pxn.18.5.6.33.15.8`), per
the AGENTS.md splitting rule; the specialised pieces themselves stay untagged.

Also records a genuine missing exact port: `evalCrepSemHOLExp_local_lookup_of_mem`
is the exact counterpart of `crepProps$eval_some_var_cexp_local_lookup`
(`cakeml/pancake/semantics/crepPropsScript.sml:835`), proved here because no
declaration for it exists in the repository yet.
-/

namespace Flapjack

variable {width : Nat} [NeZero width] {σ : Type}

/-- Flapjack-only list helper (local copy of the same-named declaration in
`Flapjack/CrepeExpressionStability.lean`): a member of the flattened variable
lists of a successfully mapped list comes from an element whose evaluation
succeeds. -/
theorem exists_mapM_of_mem_flatten_map {α β γ : Type _}
    (f : α → Option β) (g : α → List γ) (es : List α) (vs : List β) (n : γ)
    (heval : es.mapM f = some vs)
    (hmem : n ∈ (es.map g).flatten) :
    ∃ e ∈ es, ∃ v, f e = some v ∧ n ∈ g e := by
  induction es generalizing vs with
  | nil => simp at hmem
  | cons e es ih =>
      rw [List.mapM_cons] at heval
      cases hfe : f e with
      | none => simp [hfe] at heval
      | some v =>
          simp only [hfe] at heval
          cases hes : es.mapM f with
          | none => simp [hes] at heval
          | some vs' =>
              simp only [hes] at heval
              have hvs : v :: vs' = vs := by simpa using heval
              subst hvs
              simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ⟨e, by simp, v, hfe, hmem⟩
              · obtain ⟨e', he'mem, v', hf', hn'⟩ := ih vs' hes hmem
                exact ⟨e', by simp [he'mem], v', hf', hn'⟩

/-- Exact port of `crepProps$eval_some_var_cexp_local_lookup`
(`cakeml/pancake/semantics/crepPropsScript.sml:835`): a successfully evaluated
exact Crep expression binds every variable that occurs in it.  Flapjack-only
helper: it has no tagged counterpart declaration in this repository yet (the
faithful tagged port is a follow-up). -/
theorem evalCrepSemHOLExp_local_lookup_of_mem_aux (s : CrepSemHOLState width σ)
    [DecidablePred s.memaddrs] (n : Nat) :
    ∀ (e : CrepExpHOL width) (v : HolWordLab width),
      evalCrepSemHOLExp s e = some v → n ∈ crepExpVarsHOL e →
        ∃ w, s.locals.lookup n = some w
  | .const _, _, _, hmem => by simp [crepExpVarsHOL] at hmem
  | .var name, v, heval, hmem => by
      simp only [crepExpVarsHOL, List.mem_singleton] at hmem
      subst hmem
      exact ⟨v, by simpa only [evalCrepSemHOLExp] using heval⟩
  | .load a, v, heval, hmem => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at heval
      | some av => exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n a av ha (by simpa only [crepExpVarsHOL] using hmem)
  | .load32 a, v, heval, hmem => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at heval
      | some av => exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n a av ha (by simpa only [crepExpVarsHOL] using hmem)
  | .loadByte a, v, heval, hmem => by
      cases ha : evalCrepSemHOLExp s a with
      | none => simp [evalCrepSemHOLExp, ha] at heval
      | some av => exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n a av ha (by simpa only [crepExpVarsHOL] using hmem)
  | .op o args, v, heval, hmem => by
      simp only [crepExpVarsHOL] at hmem
      rw [crepExpVarsHOLList_eq_flatMap] at hmem
      cases hargs : args.mapM (evalCrepSemHOLExp s) with
      | none => simp [evalCrepSemHOLExp, hargs] at heval
      | some values =>
          obtain ⟨b, hb, bv, hbv, hbmem⟩ := exists_mapM_of_mem_flatten_map (evalCrepSemHOLExp s) crepExpVarsHOL args values n hargs hmem
          exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n b bv hbv hbmem
  | .crepOp o args, v, heval, hmem => by
      simp only [crepExpVarsHOL] at hmem
      rw [crepExpVarsHOLList_eq_flatMap] at hmem
      cases hargs : args.mapM (evalCrepSemHOLExp s) with
      | none => simp [evalCrepSemHOLExp, hargs] at heval
      | some values =>
          obtain ⟨b, hb, bv, hbv, hbmem⟩ := exists_mapM_of_mem_flatten_map (evalCrepSemHOLExp s) crepExpVarsHOL args values n hargs hmem
          exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n b bv hbv hbmem
  | .cmp o l r, v, heval, hmem => by
      simp only [crepExpVarsHOL, List.mem_append] at hmem
      cases hl : evalCrepSemHOLExp s l with
      | none => simp [evalCrepSemHOLExp, hl] at heval
      | some lv =>
          cases hr : evalCrepSemHOLExp s r with
          | none => simp [evalCrepSemHOLExp, hl, hr] at heval
          | some rv =>
              rcases hmem with hmem | hmem
              · exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n l lv hl hmem
              · exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n r rv hr hmem
  | .shift o l r, v, heval, hmem => by
      simp only [crepExpVarsHOL, List.mem_append] at hmem
      cases hl : evalCrepSemHOLExp s l with
      | none => simp [evalCrepSemHOLExp, hl] at heval
      | some lv =>
          cases hr : evalCrepSemHOLExp s r with
          | none => simp [evalCrepSemHOLExp, hl, hr] at heval
          | some rv =>
              rcases hmem with hmem | hmem
              · exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n l lv hl hmem
              · exact evalCrepSemHOLExp_local_lookup_of_mem_aux s n r rv hr hmem
  | .baseAddr, _, _, hmem => by simp [crepExpVarsHOL] at hmem
  | .topAddr, _, _, hmem => by simp [crepExpVarsHOL] at hmem
  | .loadGlob _, _, _, hmem => by simp [crepExpVarsHOL] at hmem
  termination_by e _ _ _ => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals first
      | decreasing_trivial
      | (rename_i hb; have := List.sizeOf_lt_of_mem hb;
         simp_all only [CrepExpHOL.op.sizeOf_spec, CrepExpHOL.crepOp.sizeOf_spec]; omega)

theorem evalCrepSemHOLExp_local_lookup_of_mem (s : CrepSemHOLState width σ)
    [DecidablePred s.memaddrs] (e : CrepExpHOL width) (v : HolWordLab width) (n : Nat)
    (heval : evalCrepSemHOLExp s e = some v)
    (hmem : n ∈ crepExpVarsHOL e) :
    ∃ w, s.locals.lookup n = some w :=
  evalCrepSemHOLExp_local_lookup_of_mem_aux s n e v heval hmem


/-- The conclusion shape of HOL `comp_exp_preserves_eval` for a fixed source
state `s` and expression `e`: this is the induction motive of the HOL proof. -/
def CrepToLoopCompExpEvalPiece (s : CrepSemHOLState width σ) [DecidablePred s.memaddrs]
    (e : CrepExpHOL width) : Prop :=
  ∀ (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet),
    evalCrepSemHOLExp s e = some v →
    crepToLoopStateRelExact s t →
    crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs →
    crepToLoopGlobalsRelHOLExact s.globals t.globals →
    crepToLoopCodeRelExact ctxt s.code t.code →
    crepToLoopLocalsRelExact ctxt l s.locals t.locals →
    compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) →
    ctxt.vmax < tmp →
    ∃ ck st,
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p) { t with clock := t.clock + ck } =
        (none, st) ∧
      LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals

/-- Shift case piece of HOL `comp_exp_preserves_eval`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:1084-1127`).  Same
hypotheses as the HOL theorem restricted to `e = .shift shiftOp left right`,
with exactly the two sub-expression induction hypotheses. -/
theorem comp_exp_preserves_eval_shift (s : CrepSemHOLState width σ)
    [DecidablePred s.memaddrs] (shiftOp : Shift) (left right : CrepExpHOL width)
    (ihLeft : CrepToLoopCompExpEvalPiece s left)
    (ihRight : CrepToLoopCompExpEvalPiece s right) :
    CrepToLoopCompExpEvalPiece s (.shift shiftOp left right) := by
  intro v t ctxt tmp l p le ntmp nl hEval hState hMem hGlobals hCode hLocals hCompile hTmp
  simp only [evalCrepSemHOLExp] at hEval
  cases hl : evalCrepSemHOLExp s left with
  | none => simp [hl] at hEval
  | some lv =>
      cases hr : evalCrepSemHOLExp s right with
      | none => simp [hl, hr] at hEval
      | some rv =>
          cases lv with
          | word lw =>
              cases rv with
              | word rw =>
                  cases hshift : wordShiftHOL shiftOp lw rw.toNat with
                  | none => simp [hl, hr, hshift] at hEval
                  | some sw =>
                      simp [hl, hr, hshift] at hEval
                      subst hEval
                      simp only [compileExpHOLExact] at hCompile
                      rcases hL : compileExpHOLExact ctxt tmp l left with
                        ⟨leftCode, leftValue, leftNext, leftLive⟩
                      rcases hR : compileExpHOLExact ctxt leftNext leftLive right with
                        ⟨rightCode, rightValue, rightNext, rightLive⟩
                      rw [hL, hR] at hCompile
                      simp only [Prod.mk.injEq] at hCompile
                      obtain ⟨hp, hle, hntmp, hnl⟩ := hCompile
                      obtain ⟨ck1, st1, hEval1, hVal1, hState1, hMem1, hGlob1, hCode1, hLoc1⟩ :=
                        ihLeft (.word lw) t ctxt tmp l leftCode leftValue leftNext leftLive
                          hl hState hMem hGlobals hCode hLocals hL hTmp
                      have htmp_le : tmp ≤ leftNext := by
                        have := compileExpHOLExact_tmp_le ctxt tmp l left
                        rw [hL] at this
                        exact this
                      obtain ⟨ck2, st2, hEval2, hVal2, hState2, hMem2, hGlob2, hCode2, hLoc2⟩ :=
                        ihRight (.word rw) st1 ctxt leftNext leftLive rightCode rightValue
                          rightNext rightLive hr hState1 hMem1 hGlob1 hCode1 hLoc1 hR
                          (Nat.lt_of_lt_of_le hTmp htmp_le)
                      refine ⟨ck1 + ck2, st2, ?_, ?_, hState2, hMem2, hGlob2, hCode2, ?_⟩
                      · rw [← hp]
                        have hEval1' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL leftCode)
                            {t with clock := (t.clock + ck1) + ck2} =
                            (none, {st1 with clock := st1.clock + ck2}) := by
                          simpa only [LoopSemStateFiniteExact.with_clock_with_clock] using
                            LoopSemStateFiniteExact.evaluate_add_clock_eq (loopNestedSeqHOL leftCode)
                              {t with clock := t.clock + ck1} none st1 ck2 hEval1 (by simp)
                        have hcomb := LoopSemStateFiniteExact.evaluate_none_nested_seq_append
                          (p := leftCode) (s := {t with clock := (t.clock + ck1) + ck2})
                          (st := {st1 with clock := st1.clock + ck2}) (q := rightCode) hEval1'
                        rw [← Nat.add_assoc]
                        rw [hcomb, hEval2]
                      · rw [← hle]
                        have hVal1' : LoopSemStateFiniteExact.eval st1 leftValue = some (.word lw) := by
                          simpa only [wlabWlocExact] using hVal1
                        have hVal2' : LoopSemStateFiniteExact.eval st2 rightValue = some (.word rw) := by
                          simpa only [wlabWlocExact] using hVal2
                        have hOutL := compile_exp_out_rel ctxt tmp l left leftCode leftValue
                          leftNext leftLive hL
                        have hOutR := compile_exp_out_rel ctxt leftNext leftLive right rightCode
                          rightValue rightNext rightLive hR
                        have hMax : crepToLoopCtxtMax ctxt.vmax ctxt.vars.lookup :=
                          (crepToLoopLocalsRelExact_intro ctxt l s.locals t.locals hLocals).2.1
                        have hVars : ∀ n, n ∈ crepExpVarsHOL left →
                            ∃ m, ctxt.vars.lookup n = some m ∧ sptMem m l := by
                          intro n hn
                          obtain ⟨val, hval⟩ :=
                            evalCrepSemHOLExp_local_lookup_of_mem s left (.word lw) n hl hn
                          obtain ⟨m, hvar, hmem, _⟩ :=
                            (crepToLoopLocalsRelExact_intro ctxt l s.locals t.locals hLocals).2.2.2
                              n val hval
                          exact ⟨m, hvar, hmem⟩
                        have hBoundL : ∀ n, n ∈ holLoopAssignedVars (loopNestedSeqHOL leftCode) →
                            n < leftNext := by
                          intro n hn
                          exact (comp_exp_assigned_vars_tmp_bound ctxt tmp l left leftCode
                            leftValue leftNext leftLive n ⟨hL, hn⟩).2
                        have hBoundR : ∀ n, n ∈ holLoopAssignedVars (loopNestedSeqHOL rightCode) →
                            leftNext ≤ n := by
                          intro n hn
                          exact (comp_exp_assigned_vars_tmp_bound ctxt leftNext leftLive right
                            rightCode rightValue rightNext rightLive n ⟨hR, hn⟩).1
                        have hTouched : ∀ n, n ∈ holLoopLocalsTouched leftValue →
                            n < leftNext ∧
                              sptMem n (cutSetsHOL l (loopNestedSeqHOL leftCode)) := by
                          intro n hn
                          have hdom := compile_exp_le_tmp_domain ctxt tmp l left leftCode leftValue
                            leftNext leftLive n ⟨hMax, hL, hTmp, hVars, hn⟩
                          refine ⟨hdom.1, ?_⟩
                          rw [← hOutL.2.2]
                          simpa only [sptMem, sptDomain] using hdom.2
                        have hpure : LoopSemStateFiniteExact.eval st2 leftValue = some (.word lw) :=
                          LoopSemStateFiniteExact.nested_seq_pure_evaluation (p := leftCode)
                            (q := rightCode) (t := t) (r := st2) (st := st1) (l := l)
                            (m := leftNext) (e := leftValue) (v := .word lw) (ck := ck1)
                            (ck' := ck2)
                            ⟨by simpa only [Nat.add_comm] using hEval1,
                             by simpa only [Nat.add_comm] using hEval2,
                             hOutL.1, by rw [← hOutL.2.2]; exact hOutR.1,
                             hBoundL, hBoundR, hTouched, hVal1'⟩
                        simp only [LoopSemStateFiniteExact.eval, hpure, hVal2', hshift,
                          wlabWlocExact, Option.map_some]
                      · rw [← hnl]
                        exact hLoc2

end Flapjack
