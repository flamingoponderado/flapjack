import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Seq
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas
import Flapjack.Pancake.Semantics.PanCommonProps

/-!
# crep_to_loop `ncompile_correct`, split by HOL's `evaluate_ind` cases

Pieces of `cakeml/pancake/proofs/crep_to_loopProofScript.sml`'s
`ncompile_correct` (110-154) over the exact carriers (bead
`flapjack-pxn.18.5.6.24`).  HOL proves the theorem by
`recInduct crepSemTheory.evaluate_ind` and resumes each case with
`Resume ncompile_correct[...]`; each Lean piece below is one such case, carrying
every HOL hypothesis and the HOL conclusion with the program fixed to that
constructor, plus exactly the `evaluate_ind` hypotheses of that case.  HOL's
quantifier order `∀v v1 res s1 t ctxt l` is kept (constructor payload and the
source state `v1` first, as in `evaluate_ind`).  `evaluate` is the tagged exact
`evalCrepSemHOLProgExact` (`crepSem$evaluate_def`) and
`LoopSemStateFiniteExact.evaluate` (`loopSem$evaluate_def`), `compile` is the
tagged `compileHOLExact` (`compile_def`), `wlab_wloc` is `wlabWlocExact`, and
the five relations are the tagged exact ones.
-/

namespace Flapjack

/-! Owning carriers of the finite maps the statements traverse; same-module
witnesses for the `fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopNcompileCorrectWitnesses

theorem holFmapAsFiniteSupportRelationWitness_CrepToLoopContextExact
    (context : CrepToLoopContextExact) :
    CrepToLoopContextExact.ofBroad (CrepToLoopContextExact.toBroad context) = context :=
  CrepToLoopContextExact.holFmapAsFiniteSupportWitness context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

theorem holFmapAsFiniteSupportRelationWitness_LoopSemStateFiniteExact
    {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end CrepToLoopNcompileCorrectWitnesses

/-- Flapjack helper (no HOL declaration): HOL `ncompile_correct`'s result
    correspondence `case res of NONE => NONE | SOME (Break n) => SOME (Break n)
    | ... | SOME Error => SOME Error` (`crep_to_loopProofScript.sml:119-127`). -/
def crepToLoopResultHOL {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → Option (LoopSemStateFiniteExact.LoopResultExact width)
  | none => none
  | some (.break n) => some (.break n)
  | some (.continue n) => some (.continue n)
  | some (.return vs) => some (.result (vs.map wlabWlocExact))
  | some (.exception eid) => some (.exception (.word eid))
  | some .timeOut => some .timeOut
  | some (.finalFfi f) => some (.finalFfi f)
  | some .error => some .error

/-- Flapjack helper (no HOL declaration): HOL `ncompile_correct`'s final
    `case res of NONE => locals_rel ctxt l s1.locals t1.locals | SOME (Break n)
    => locals_rel ... | SOME (Continue n) => locals_rel ... | SOME (Return vs) => T
    | SOME Error => F | _ => T` (`crep_to_loopProofScript.sml:128-134`). -/
def crepToLoopResultLocalsHOL {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sLocals : HolFiniteMapExact Nat (HolWordLab width)) (tLocals : Spt (WordLocW width)) :
    Option (CrepResultHOLExact width) → Prop
  | none => crepToLoopLocalsRelExact ctxt l sLocals tLocals
  | some (.break _) => crepToLoopLocalsRelExact ctxt l sLocals tLocals
  | some (.continue _) => crepToLoopLocalsRelExact ctxt l sLocals tLocals
  | some (.return _) => True
  | some .error => False
  | some _ => True

/-- Flapjack-only abbreviation (no HOL declaration) of the `ncompile_correct`
    statement at a fixed program `v` and source state `v1`, i.e. the
    `evaluate_ind` induction hypothesis HOL's case proofs receive for a
    sub-program.  Only used as an antecedent of the case pieces; every piece
    states its own conclusion in full. -/
def crepToLoopNcompileCorrectAt {width : Nat} [NeZero width] {σ : Type}
    (v : CrepProgHOL width) (v1 : CrepSemHOLState width σ) : Prop :=
  ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
    evalCrepSemHOLProgExact v1 v = (res, s1) ∧ res ≠ some .error ∧
      crepToLoopStateRelExact v1 t ∧
      crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
      crepToLoopCodeRelExact ctxt v1.code t.code ∧
      crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
    ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width)) (t1 : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l v)
          { t with clock := t.clock + ck } = (res1, t1) ∧
      crepToLoopStateRelExact s1 t1 ∧
      crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
      crepToLoopCodeRelExact ctxt s1.code t1.code ∧
      res1 = crepToLoopResultHOL res ∧
      crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res

/-- `ncompile_correct`, case `If e c1 c2` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[If]` at 2585-2681), with the
    `evaluate_ind` hypothesis `∀w. eval s e = SOME (Word w) ⇒
    P (if w ≠ 0w then c1 else c2, s)`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_if {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (v1 : CrepSemHOLState width σ),
      (∀ w, evalCrepSemHOLExp v1 e = some (.word w) →
        crepToLoopNcompileCorrectAt (if w ≠ 0 then c1 else c2) v1) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.ite e c1 c2) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.ite e c1 c2))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro e c1 c2 v1 ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
    simp only [hev, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word w =>
  simp only [hev] at he
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval v1 e (.word w) t ctxt (ctxt.vmax + 1) l np le tmp nl
      ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  -- `st with locals := insert tmp (Word w) st.locals` satisfies `locals_rel ctxt l`
  have hl' : crepToLoopLocalsRelExact ctxt l v1.locals
      (LoopSemStateFiniteExact.setVar tmp (.word w) st).locals := by
    refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hnl : sptDomain nl k := hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
      exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k hnl))
    · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
      obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
      have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
      subst hnn
      have hle := h1l.2.1 vn n' hn1'
      refine ⟨n', hn1', hn2, ?_⟩
      simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
      rw [if_neg (by omega)]
      exact hn3'
  obtain ⟨ck', res1, t1, h2, h2s, h2m, h2g, h2c, h2r, h2l⟩ :=
    ih w hev res s1 (LoopSemStateFiniteExact.setVar tmp (.word w) st) ctxt l
      ⟨he, hne, h1s, h1m, h1g, h1c, hl'⟩
  have hcomp : compileHOLExact ctxt l (.ite e c1 c2) =
      loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l]) := by
    rw [compileHOLExact, hC]
  rw [hcomp]
  -- the `Assign tmp le; If NotEqual tmp (Imm 0w) ...` tail from any clock extension
  have htail : ∀ k, LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l])
      { st with clock := st.clock + k } =
      LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
          { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + k }) := by
    intro k
    have hle : LoopSemStateFiniteExact.eval { st with clock := st.clock + k } le =
        some (.word w) := by
      rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
    simp only [LoopSemStateFiniteExact.evaluate, hle]
    simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
      LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hw : w = 0
    · simp only [hw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false,
        ne_eq, not_true_eq_false]
      split <;> rename_i h <;> exact h.symm
    · have hb : (w == 0) = false := by simpa using hw
      simp only [hb, Bool.not_false, if_true, ne_eq, hw, not_false_eq_true]
      split <;> rename_i h <;> exact h.symm
  have h1k : ∀ k, LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
      { t with clock := t.clock + (ck + k) } = (none, { st with clock := st.clock + k }) := by
    intro k
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
    simpa [Nat.add_assoc] using this
  have h2' : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
      { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + ck' } =
        (res1, t1) := h2
  cases res with
  | none =>
    have hr1 : res1 = none := by simpa [crepToLoopResultHOL] using h2r
    subst hr1
    have h2l' : crepToLoopLocalsRelExact ctxt l s1.locals t1.locals := h2l
    have h2k : LoopSemStateFiniteExact.evaluate
        (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
        { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + 1) } =
          (none, { t1 with clock := t1.clock + 1 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2' (by simp)
      simpa [Nat.add_assoc] using this
    have hsub : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
    have hcut : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
        (none, { t1 with locals := sptInter t1.locals l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub]
      simp [LoopSemStateFiniteExact.decClock]
    refine ⟨ck + (ck' + 1), none, { t1 with locals := sptInter t1.locals l }, ?_, h2s, h2m,
      h2g, h2c, rfl, ?_⟩
    · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k (ck' + 1)),
        htail, h2k, hcut]
    · refine ⟨h2l'.1, h2l'.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
      · have hk' : (sptLookup k l).isSome := hk
        show (sptLookup k (sptInter t1.locals l)).isSome
        rw [sptLookup_sptInter, if_pos hk']
        exact hsub k hk
      · obtain ⟨n, hn1, hn2, hn3⟩ := h2l'.2.2.2 vn val hval
        have hnl : (sptLookup n l).isSome := hn2
        refine ⟨n, hn1, hn2, ?_⟩
        show sptLookup n (sptInter t1.locals l) = _
        rw [sptLookup_sptInter, if_pos hnl]
        exact hn3
  | some r =>
    obtain ⟨x, hx⟩ : ∃ x, res1 = some x := by
      cases r <;> simp only [crepToLoopResultHOL] at h2r <;> exact ⟨_, h2r⟩
    refine ⟨ck + ck', res1, t1, ?_, h2s, h2m, h2g, h2c, h2r, h2l⟩
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k ck'), htail, h2', hx]
    rfl


/-- `ncompile_correct`, case `Return es` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[Return]` at 1704-1749).  `evaluate_ind`
    gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_return {width : Nat} [NeZero width] {σ : Type} :
    ∀ (es : List (CrepExpHOL width)) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.return es) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.return es))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro es v1 res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hes : es.mapM (evalCrepSemHOLExp v1) with
  | none =>
    simp only [hes, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some ws =>
  simp only [hes, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rcases hC : compileExpsHOLExact ctxt (ctxt.vmax + 1) l es with ⟨p, les, ntmp, nl⟩
  obtain ⟨ck, st, h1, hles, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exps_preserves_eval es v1 ws t ctxt (ctxt.vmax + 1) l p les ntmp nl
      ⟨hes, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  have hlen : les.length = ws.length := by
    have := congrArg List.length ((optMmapEqSome les _ _).mp hles)
    simpa using this
  let temps := genTemps ntmp les.length
  have htlen : temps.length = les.length := by simp [temps, genTemps]
  have htnodup : temps.Nodup := by
    simp only [temps, genTemps]
    rw [List.Nodup, List.pairwise_map]
    exact (List.nodup_range).imp (fun h => by omega)
  have hdisj : distinctListsHol temps (les.map holLoopLocalsTouched).flatten = true := by
    simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq]
    intro x hx hmem
    have hx' : ntmp ≤ x := by
      simp only [temps, genTemps, List.mem_map, List.mem_range] at hx
      obtain ⟨a, _, rfl⟩ := hx; omega
    have := (compile_exps_le_tmp_domain ctxt (ctxt.vmax + 1) l es p les ntmp nl x
      ⟨hl.2.1, hC, Nat.lt_succ_self _, fun k hk => by
        obtain ⟨w, hw⟩ := crepOptMmapEval_some_var_cexp_local_lookup v1 es ws k ⟨hes, hk⟩
        obtain ⟨m, hm1, hm2, _⟩ := hl.2.2.2 k w hw
        exact ⟨m, hm1, hm2⟩, hmem⟩).1
    omega
  have hassign := LoopSemStateFiniteExact.loop_eval_nested_assign_distinct_eq les temps st
    (ws.map wlabWlocExact) ⟨(optMmapEqSome les _ _).mp hles, hdisj, htnodup, htlen⟩
  have hget := LoopSemStateFiniteExact.get_vars_local_update_some_eq temps
    (ws.map wlabWlocExact) st htnodup (by simp [htlen, hlen])
  refine ⟨ck, some (.result (ws.map wlabWlocExact)),
    LoopSemStateFiniteExact.callEnv []
      { st with locals := LoopSemStateFiniteExact.sptAlistInsert temps (ws.map wlabWlocExact) st.locals },
    ?_, h1s, h1m, h1g, h1c, rfl, trivial⟩
  rw [compileHOLExact, hC]
  simp only [List.append_assoc]
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none p _ _ _ h1]
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none _ _ _ _ hassign]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
    LoopSemStateFiniteExact.evaluate]
  rw [hget]

/-- `ncompile_correct`, case `Raise eid` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[Raise]` at 1750-1756).  `evaluate_ind`
    gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_raise {width : Nat} [NeZero width] {σ : Type} :
    ∀ (eid : BitVec width) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.raise eid) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.raise eid))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro eid v1 res s1 t ctxt l ⟨he, _, hs, hm, hg, hc, _⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨0, some (.exception (.word eid)),
    LoopSemStateFiniteExact.callEnv []
      (LoopSemStateFiniteExact.setVar (ctxt.vmax + 1) (.word eid) { t with clock := t.clock + 0 }),
    ?_, hs, hm, hg, hc, rfl, trivial⟩
  simp only [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq,
    LoopSemStateFiniteExact.evaluate, LoopSemStateFiniteExact.eval]
  simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
end Flapjack
