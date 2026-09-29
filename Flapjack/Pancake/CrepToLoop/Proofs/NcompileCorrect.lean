import Flapjack.Pancake.CrepToLoop.Proofs.CompExpPreservesEval
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Seq
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas
import Flapjack.Pancake.Semantics.PanCommonProps
import Flapjack.Pancake.Semantics.CrepProps
import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel

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

/-- Flapjack helper (no HOL declaration): the panSem `word8` `get_byte` rendering
    is wordSem's `byte$get_byte`, at every width. -/
private theorem panGetByteWord8HOL_eq_getByteHOL8 {width : Nat}
    (a v : BitVec width) (be : Bool) :
    panGetByteWord8HOL a v be = getByteHOL8 a v be := by
  apply BitVec.eq_of_toNat_eq
  simp only [panGetByteWord8HOL, getByteHOL8, byteIndexHOL, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  cases be <;> simp [Nat.pow_mul]

/-- Flapjack helper (no HOL declaration): HOL's ExtCall case proves
    `mem_load_byte_aux t.memory t.mdomain t.be = mem_load_byte s.memory
    s.memaddrs s.be` by extensionality under `mem_rel` and `state_rel`; this is
    that step over the exact carriers (for any decision procedure on the
    source domain). -/
private theorem panMemLoadByteWord8HOL_eq_memLoadByteAuxExact {width : Nat} [NeZero width]
    (smem : BitVec width → HolWordLab width) (dom : BitVec width → Prop) [DecidablePred dom]
    (tmem : BitVec width → WordLocW width) (tdom : BitVec width → Bool) (be : Bool)
    (hdom : dom = fun x => tdom x = true) (hm : crepToLoopMemRelHOLExact smem tmem dom) :
    panMemLoadByteWord8HOL smem dom be = memLoadByteAuxExact tmem tdom be := by
  funext a
  unfold panMemLoadByteWord8HOL memLoadByteAuxExact
  rw [riscvByteAlignHOL_eq_panByteAlignHOL]
  cases hv : smem (panByteAlignHOL a) with
  | word val =>
    simp only
    by_cases hd : dom (panByteAlignHOL a)
    · have hmv := hm _ hd
      rw [hv] at hmv
      have htd : tdom (panByteAlignHOL a) = true := by subst hdom; exact hd
      rw [if_pos hd, ← hmv]
      simp [wlabWlocExact, htd, panGetByteWord8HOL_eq_getByteHOL8, hv]
    · have htd : tdom (panByteAlignHOL a) = false := by
        subst hdom; simpa using hd
      rw [if_neg hd]
      cases htm : tmem (panByteAlignHOL a) <;> simp [htd]


/-- Flapjack helper (no HOL declaration): the tagged `write_bytearray_mem_rel`
    with the source domain given as any decidable predicate equal to the Prop
    view of the target domain (HOL has one `dm`; the exact carriers have a Bool
    target domain and a Prop source domain). -/
private theorem write_bytearray_mem_rel_dom {width : Nat} [NeZero width]
    (nb : List (BitVec 8)) (sm : BitVec width → HolWordLab width)
    (tm : BitVec width → WordLocW width) (w : BitVec width)
    (dom : BitVec width → Prop) [inst : DecidablePred dom] (tdom : BitVec width → Bool)
    (be : Bool) (hdom : dom = fun a => tdom a = true)
    (h : crepToLoopMemRelHOLExact sm tm dom) :
    crepToLoopMemRelHOLExact (panWriteBytearrayWord8HOL w nb sm dom be)
      (writeBytearrayExact w nb tm tdom be) dom := by
  subst hdom
  have hi : inst = fun a => instDecidableEqBool (tdom a) true := Subsingleton.elim _ _
  subst hi
  exact write_bytearray_mem_rel nb sm tm w tdom be h

/-- `ncompile_correct`, case `ExtCall f c cl a al`
    (`crep_to_loopProofScript.sml:110-134` statement; `Resume ncompile_correct[ExtCall]`
    at 2682-2714).  `evaluate_ind` gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_extCall {width : Nat} [NeZero width] {σ : Type} :
    ∀ (f : Flapjack.Basis.Pure.MlString.MlString) (c cl a al : Nat) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.extCall f c cl a al) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.extCall f c cl a al))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro f c cl a al v1 res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  classical
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  -- all four source locals are words (otherwise the source errors)
  cases hcl : v1.locals.lookup cl with
  | none => simp [hcl] at he; exact absurd he.1.symm hne
  | some xcl =>
  cases hc' : v1.locals.lookup c with
  | none => simp [hcl, hc'] at he; exact absurd he.1.symm hne
  | some xc =>
  cases hal : v1.locals.lookup al with
  | none => simp [hcl, hc', hal] at he; exact absurd he.1.symm hne
  | some xal =>
  cases ha : v1.locals.lookup a with
  | none => simp [hcl, hc', hal, ha] at he; exact absurd he.1.symm hne
  | some xa =>
  cases xcl with | word wcl =>
  cases xc with | word wc =>
  cases xal with | word wal =>
  cases xa with | word wa =>
  simp only [hcl, hc', hal, ha] at he
  obtain ⟨ncl, hncl1, hncl2, hncl3⟩ := hl.2.2.2 cl _ hcl
  obtain ⟨nc, hnc1, hnc2, hnc3⟩ := hl.2.2.2 c _ hc'
  obtain ⟨nal, hnal1, hnal2, hnal3⟩ := hl.2.2.2 al _ hal
  obtain ⟨na, hna1, hna2, hna3⟩ := hl.2.2.2 a _ ha
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  rw [panMemLoadByteWord8HOL_eq_memLoadByteAuxExact v1.memory v1.memaddrs
    t.memory t.mdomain v1.be hs.1 hm] at he
  have hcomp : compileHOLExact ctxt l (.extCall f c cl a al) =
      (HolLoopProg.ffi f nc ncl na nal l : HolLoopProg width) := by
    simp [compileHOLExact, hnc1, hncl1, hna1, hnal1]
  rw [hcomp]
  obtain ⟨hdom, hsh, hclk, hbe, hffi, hba, hta⟩ := hs
  rw [hbe, hffi] at he
  have hcut : LoopSemStateFiniteExact.cutState l t = some { t with locals := sptInter t.locals l } :=
    LoopSemStateFiniteExact.cutState_of_subset l t hsub
  have ht0 : ({ t with clock := t.clock + 0 } : LoopSemStateFiniteExact width σ) = t := rfl
  have hlocals : crepToLoopLocalsRelExact ctxt l v1.locals (sptInter t.locals l) := by
    refine ⟨hl.1, hl.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hk' : (sptLookup k l).isSome := hk
      show (sptLookup k (sptInter t.locals l)).isSome
      rw [sptLookup_sptInter, if_pos hk']
      exact hsub k hk
    · obtain ⟨n, hn1, hn2, hn3⟩ := hl.2.2.2 vn val hval
      have hnl : (sptLookup n l).isSome := hn2
      refine ⟨n, hn1, hn2, ?_⟩
      show sptLookup n (sptInter t.locals l) = _
      rw [sptLookup_sptInter, if_pos hnl]
      exact hn3
  cases hr1 : readBytearrayWordHOL wc wcl.toNat (memLoadByteAuxExact t.memory t.mdomain t.be) with
  | none => simp [hr1] at he; exact absurd he.1.symm hne
  | some cb =>
  cases hr2 : readBytearrayWordHOL wa wal.toNat (memLoadByteAuxExact t.memory t.mdomain t.be) with
  | none => simp [hr1, hr2] at he; exact absurd he.1.symm hne
  | some ab =>
  simp only [hr1, hr2] at he
  cases hf : callFFIHOL t.ffi (.extCall f) cb ab with
  | final ev =>
    simp only [hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    let tf : LoopSemStateFiniteExact width σ :=
      LoopSemStateFiniteExact.callEnv [] { t with locals := sptInter t.locals l }
    refine ⟨0, some (.finalFfi ev), tf, ?_, ⟨hdom, hsh, hclk, hbe, hffi, hba, hta⟩, hm, hg, hc,
      rfl, trivial⟩
    rw [ht0]
    simp only [LoopSemStateFiniteExact.evaluate, hncl3, hnc3, hnal3, hna3, wlabWlocHOL, hcut,
      hr1, hr2, hf, tf]
  | ret nf nb =>
    simp only [hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    let tf : LoopSemStateFiniteExact width σ :=
      { t with locals := sptInter t.locals l,
               memory := writeBytearrayExact wa nb t.memory t.mdomain t.be,
               ffi := nf }
    refine ⟨0, none, tf, ?_, ⟨hdom, hsh, hclk, rfl, rfl, hba, hta⟩, ?_, hg, hc, rfl, hlocals⟩
    · rw [ht0]
      simp only [LoopSemStateFiniteExact.evaluate, hncl3, hnc3, hnal3, hna3, wlabWlocHOL, hcut,
        hr1, hr2, hf, tf]
    · exact write_bytearray_mem_rel_dom nb v1.memory t.memory wa v1.memaddrs t.mdomain t.be
        hdom hm

/-- `ncompile_correct`, case `StoreGlob dst e` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[StoreGlob]` at 2075-2104).  `evaluate_ind`
    gives this case no induction hypothesis. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_storeGlob {width : Nat} [NeZero width] {σ : Type} :
    ∀ (dst : BitVec 5) (e : CrepExpHOL width) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.storeGlob dst e) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.storeGlob dst e))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro dst e v1 res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
    simp only [hev, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some w =>
  simp only [hev, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨p, le, tmp, l'⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval v1 e w t ctxt (ctxt.vmax + 1) l p le tmp l'
      ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, _, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e p le tmp l' hC
  have hsub : sptSubspt l l' := hlA ▸ comp_syn_impl_cut_sets_subspt _ l hokA
  refine ⟨ck, none, LoopSemStateFiniteExact.setGlobals dst (wlabWlocExact w) st, ?_, h1s, h1m,
    ?_, h1c, rfl, crepToLoopLocalsRelExact_cutset_prop ctxt l l' v1.locals t.locals st.locals
      hl h1l hsub⟩
  · rw [compileHOLExact, hC]
    simp only
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none p _ _ _ h1]
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq,
      LoopSemStateFiniteExact.evaluate, h1v]
  · intro ad v hv
    simp only [CrepSemHOLState.setGlobals, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL] at hv
    simp only [LoopSemStateFiniteExact.setGlobals, HolFiniteMapExact.lookup_update, FUPDATE]
    by_cases had : ad = dst
    · subst had
      simp only [if_true] at hv
      simp only [beq_self_eq_true, if_true, Option.some.injEq]
      rw [Option.some.inj hv]
    · rw [if_neg had] at hv
      have hne' : (dst == ad) = false := beq_eq_false_iff_ne.mpr (fun h => had h.symm)
      rw [hne']
      simp only [Bool.false_eq_true, if_false]
      exact h1g ad v hv

section LoopStep
/-! Flapjack helpers (no HOL declaration): one unfolding of loopSem's `Loop`
clause (`evaluate_def`, `loopSemScript.sml`) by the outcome of the entry
`cut_res` and of the body, as HOL's While case uses `Once evaluate_def`. -/

variable {width : Nat} [NeZero width] {F : Type}

private theorem loop_step_cut_some {L L' : NumSet} {B : HolLoopProg width}
    {X Y : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (some r, Y)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (some r, Y) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h => rw [hc] at h; simp at h
  next h => exact hc

private theorem loop_step_none {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (none, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_continue {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.continue 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_break {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.break 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.cutRes L' (none, s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_exit {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hr0 : r ≠ .continue 0) (hr1 : r ≠ .break 0)
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some r, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (LoopSemStateFiniteExact.exitLoop (some r), s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

end LoopStep

section WhileHelpers
/-! Flapjack helpers (no HOL declaration) for HOL's While case: the
`locals_rel_def` / `domain_inter` / `lookup_inter` / `lookup_insert` steps, one
unfolding of the compiled loop body, and `exit_loop` against the result map. -/

variable {width : Nat} [NeZero width] {F : Type}

private theorem locals_rel_inter (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l sl tl) :
    crepToLoopLocalsRelExact ctxt l sl (sptInter tl l) := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter tl l)).isSome
    rw [sptLookup_sptInter, if_pos hk']
    exact h.2.2.1 k hk
  · obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hnl : (sptLookup n l).isSome := hn2
    refine ⟨n, hn1, hn2, ?_⟩
    show sptLookup n (sptInter tl l) = _
    rw [sptLookup_sptInter, if_pos hnl]
    exact hn3

/-- `locals_rel ctxt l` survives the compiled condition (whose output live set
    `nl` contains `l`) and the write of the fresh temporary `tmp > vmax`. -/
private theorem locals_rel_insert_of (ctxt : CrepToLoopContextExact) (l nl : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl tl' : Spt (WordLocW width))
    (hl : crepToLoopLocalsRelExact ctxt l sl tl) (h1l : crepToLoopLocalsRelExact ctxt nl sl tl')
    (hsub : ∀ k, sptDomain l k → sptDomain nl k) (tmp : Nat) (htmp : ctxt.vmax < tmp)
    (x : WordLocW width) :
    crepToLoopLocalsRelExact ctxt l sl (sptInsert tmp x tl') := by
  refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hsub k hk)))
  · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
    obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
    have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
    subst hnn
    have hle := h1l.2.1 vn n' hn1'
    refine ⟨n', hn1', hn2, ?_⟩
    rw [sptLookup_sptInsert, if_neg (by omega)]
    exact hn3'

private theorem seq_continue_none {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F}
    (h : LoopSemStateFiniteExact.evaluate cC S = (none, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some (.continue 0), s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]
  simp only [LoopSemStateFiniteExact.evaluate]

private theorem seq_continue_some {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F} {x : LoopSemStateFiniteExact.LoopResultExact width}
    (h : LoopSemStateFiniteExact.evaluate cC S = (some x, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some x, s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]

/-- One run of the compiled While body `nested_seq (np ++ [Assign tmp le;
    If NotEqual tmp (Imm 0w) (Seq c (Continue 0)) (Break 0) l])`. -/
private theorem while_body_eval (np : List (HolLoopProg width)) (le : HolLoopExp width)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg width) (Y st : LoopSemStateFiniteExact width F)
    (w : BitVec width) (h1 : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w)) :
    LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width)) (.seq cC (.continue 0)) (.break 0) l])) Y =
      if w = 0 then (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word w) st)
      else LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0))
          (LoopSemStateFiniteExact.setVar tmp (.word w) st)) := by
  generalize (HolLoopProg.seq cC (.continue 0) : HolLoopProg width) = q
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ h1]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
  simp only [LoopSemStateFiniteExact.evaluate, h1v]
  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
    LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rfl
  · have hb : (w == 0) = false := by simpa using hw
    simp only [hb, Bool.not_false, if_true, hw, if_false]
    split <;> rename_i h <;> exact h.symm

private theorem crepToLoopResultHOL_exitLoop (r : CrepResultHOLExact width)
    (h0 : r ≠ .continue 0) (h1 : r ≠ .break 0) :
    LoopSemStateFiniteExact.exitLoop (crepToLoopResultHOL (some r)) =
      crepToLoopResultHOL (exitLoopCrepResult (some r)) := by
  cases r with
  | «continue» n => cases n with
    | zero => exact absurd rfl h0
    | succ n => rfl
  | «break» n => cases n with
    | zero => exact absurd rfl h1
    | succ n => rfl
  | _ => rfl

private theorem crepToLoopResultLocalsHOL_exitLoop (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (r : CrepResultHOLExact width) (h : crepToLoopResultLocalsHOL ctxt l sl tl (some r)) :
    crepToLoopResultLocalsHOL ctxt l sl tl (exitLoopCrepResult (some r)) := by
  cases r <;> exact h

end WhileHelpers

/-- `ncompile_correct`, case `While e c` (`crep_to_loopProofScript.sml:110-134`
    statement; `Resume ncompile_correct[While]` at 2717-3130), with exactly
    `evaluate_ind`'s three While hypotheses: `P (While e c, s1)` after a body run
    ending in `SOME (Continue 0)` or `NONE`, and `P (c, dec_clock s)`, each under
    `eval s e = SOME (Word w) ∧ w ≠ 0w ∧ s.clock ≠ 0`. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_while {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c : CrepProgHOL width) (v1 : CrepSemHOLState width σ),
      (∀ (w : BitVec width) (res : Option (CrepResultHOLExact width))
          (s1 : CrepSemHOLState width σ),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 ∧
          evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (res, s1) ∧
          res = some (.continue 0) →
        crepToLoopNcompileCorrectAt (.while e c) s1) →
      (∀ (w : BitVec width) (res : Option (CrepResultHOLExact width))
          (s1 : CrepSemHOLState width σ),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 ∧
          evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (res, s1) ∧ res = none →
        crepToLoopNcompileCorrectAt (.while e c) s1) →
      (∀ (w : BitVec width),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 →
        crepToLoopNcompileCorrectAt c (decClockCrepSemHOL v1)) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.while e c) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.while e c))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = crepToLoopResultHOL res ∧
        crepToLoopResultLocalsHOL ctxt l s1.locals t1.locals res := by
  intro e c v1 ihc ihn ihb res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
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
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  have hlnl : ∀ k, sptDomain l k → sptDomain nl k :=
    fun k hk => hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
  have htmp : ctxt.vmax < tmp := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htA
  let B : HolLoopProg width := loopNestedSeqHOL (np ++
    [.assign tmp le,
     .ite .notEqual tmp (.imm (0 : BitVec width))
       (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])
  have hcomp : compileHOLExact ctxt l (.while e c) = .loop l B l := by
    rw [compileHOLExact, hC]
  rw [hcomp]
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  by_cases hw : w = 0
  · -- False case
    subst hw
    simp only [ne_eq, not_true_eq_false, if_false, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
      crepToLoop_comp_exp_preserves_eval v1 e (.word 0) { t with locals := sptInter t.locals l }
        ctxt (ctxt.vmax + 1) l np le tmp nl
        ⟨hev, hs, hm, hg, hc, locals_rel_inter ctxt l v1.locals t.locals hl, hC,
          Nat.lt_succ_self _⟩
    have hentry : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + (ck + 2) }) =
        (none, { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + 2) } hsub]
      simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + 2) = 0 by omega, if_false]
      simp only [Prod.mk.injEq, true_and]
      congr 1
    have h1' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
        { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) } =
          (none, { st with clock := st.clock + 1 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h1 (by simp)
      simpa [Nat.add_assoc] using this
    have hbody := while_body_eval np le tmp l (compileHOLExact ctxt l c) _ _ 0 h1'
      (by rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v)
    rw [if_pos rfl] at hbody
    have hloop := loop_step_break (L' := l) hentry hbody
    have hS : LoopSemStateFiniteExact.sptSubsetLive l
        (LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }).locals :=
      fun k hk => (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hlnl k hk)))
    have hexit : LoopSemStateFiniteExact.cutRes l
        (none, LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }) =
        (none, { st with locals := sptInter (sptInsert tmp (.word 0) st.locals) l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l _ hS]
      simp [LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.setVar]
    refine ⟨ck + 2, none, _, hloop.trans hexit, h1s, h1m, h1g, h1c, rfl, ?_⟩
    exact locals_rel_inter ctxt l v1.locals _
      (locals_rel_insert_of ctxt l nl v1.locals _ st.locals hl h1l hlnl tmp htmp _)
  · simp only [ne_eq, hw, not_false_eq_true, if_true] at he
    by_cases hz : v1.clock = 0
    · -- Timeout case
      simp only [hz, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have ht0 : t.clock = 0 := hs.2.2.1 ▸ hz
      have hcut : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + 0 }) =
          (some .timeOut, { t with clock := t.clock + 0, locals := .ln }) := by
        rw [LoopSemStateFiniteExact.cutRes]
        simp only
        rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + 0 } hsub]
        simp [ht0]
      exact ⟨0, some .timeOut, _, loop_step_cut_some hcut, hs, hm, hg, hc, rfl, trivial⟩
    · simp only [hz, if_false] at he
      rcases hbodyS : evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c with ⟨res', s1'⟩
      simp only [hbodyS] at he
      obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
      have htz : t.clock ≠ 0 := hs3 ▸ hz
      have hev' : evalCrepSemHOLExp (decClockCrepSemHOL v1) e = some (.word w) := by
        simp only [decClockCrepSemHOL, evalCrepSemHOLExp_upd_clock_eq, hev]
      have hsD : crepToLoopStateRelExact (decClockCrepSemHOL v1)
          { t with locals := sptInter t.locals l, clock := t.clock - 1 } :=
        ⟨hs1, hs2, by simp [decClockCrepSemHOL, hs3], hs4, hs5, hs6, hs7⟩
      obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
        crepToLoop_comp_exp_preserves_eval (decClockCrepSemHOL v1) e (.word w)
          { t with locals := sptInter t.locals l, clock := t.clock - 1 }
          ctxt (ctxt.vmax + 1) l np le tmp nl
          ⟨hev', hsD, hm, hg, hc, locals_rel_inter ctxt l v1.locals t.locals hl, hC,
            Nat.lt_succ_self _⟩
      have hne' : res' ≠ some .error := by
        rintro rfl
        simp only [exitLoopCrepResult, Prod.mk.injEq] at he
        exact hne he.1.symm
      obtain ⟨ck', res1', t1, h2, h2s, h2m, h2g, h2c, h2r, h2l⟩ :=
        ihb w ⟨hev, hw, hz⟩ res' s1' (LoopSemStateFiniteExact.setVar tmp (.word w) st) ctxt l
          ⟨hbodyS, hne', h1s, h1m, h1g, h1c,
            locals_rel_insert_of ctxt l nl v1.locals _ st.locals
              (locals_rel_inter ctxt l v1.locals t.locals hl) h1l hlnl tmp htmp _⟩
      -- the loop entry, condition and body run from any clock extension
      have hentryK : ∀ k, LoopSemStateFiniteExact.cutRes l
          (none, { t with clock := t.clock + (ck + k) }) =
          (none, { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) }) := by
        intro k
        rw [LoopSemStateFiniteExact.cutRes]
        simp only
        rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + k) } hsub]
        simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + k) = 0 by omega, if_false]
        simp only [Prod.mk.injEq, true_and]
        congr 1
        omega
      have hbodyK : ∀ k, LoopSemStateFiniteExact.evaluate B
          { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) } =
          LoopSemStateFiniteExact.cutRes l
            (LoopSemStateFiniteExact.evaluate (.seq (compileHOLExact ctxt l c) (.continue 0))
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + k }) := by
        intro k
        have h1k : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
            { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) } =
              (none, { st with clock := st.clock + k }) := by
          have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
          simpa [Nat.add_assoc] using this
        have := while_body_eval np le tmp l (compileHOLExact ctxt l c) _ _ w h1k
          (by rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v)
        rw [if_neg hw] at this
        exact this
      have h2' : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
          { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + ck' } =
            (res1', t1) := h2
      cases res' with
      | none =>
        have hr1 : res1' = none := by simpa [crepToLoopResultHOL] using h2r
        subst hr1
        obtain ⟨ck'', res1, t2, h3, h3s, h3m, h3g, h3c, h3r, h3l⟩ :=
          ihn w none s1' ⟨hev, hw, hz, hbodyS, rfl⟩ res s1 t1 ctxt l
            ⟨he, hne, h2s, h2m, h2g, h2c, h2l⟩
        rw [hcomp] at h3
        have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
            { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + ck'') } =
              (none, { t1 with clock := t1.clock + ck'' }) := by
          have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck'' h2' (by simp)
          simpa [Nat.add_assoc] using this
        have hb : LoopSemStateFiniteExact.evaluate B
            { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + ck'')) } =
            (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
          rw [hbodyK, seq_continue_none h2k]; rfl
        exact ⟨ck + (ck' + ck''), res1, t2, (loop_step_continue (hentryK _) hb).trans h3,
          h3s, h3m, h3g, h3c, h3r, h3l⟩
      | some r =>
        by_cases hr0 : r = .continue 0
        · subst hr0
          simp only at he
          have hr1 : res1' = some (.continue 0) := by simpa [crepToLoopResultHOL] using h2r
          subst hr1
          obtain ⟨ck'', res1, t2, h3, h3s, h3m, h3g, h3c, h3r, h3l⟩ :=
            ihc w (some (.continue 0)) s1' ⟨hev, hw, hz, hbodyS, rfl⟩ res s1 t1 ctxt l
              ⟨he, hne, h2s, h2m, h2g, h2c, h2l⟩
          rw [hcomp] at h3
          have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with
                  clock := st.clock + (ck' + ck'') } =
                (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
            have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck'' h2' (by simp)
            simpa [Nat.add_assoc] using this
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + ck'')) } =
              (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
            rw [hbodyK, seq_continue_some h2k]; rfl
          exact ⟨ck + (ck' + ck''), res1, t2, (loop_step_continue (hentryK _) hb).trans h3,
            h3s, h3m, h3g, h3c, h3r, h3l⟩
        by_cases hr1 : r = .break 0
        · subst hr1
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hr : res1' = some (.break 0) := by simpa [crepToLoopResultHOL] using h2r
          subst hr
          have h2l' : crepToLoopLocalsRelExact ctxt l s1'.locals t1.locals := h2l
          have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + 1) } =
                (some (.break 0), { t1 with clock := t1.clock + 1 }) := by
            have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2' (by simp)
            simpa [Nat.add_assoc] using this
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + 1)) } =
              (some (.break 0), { t1 with clock := t1.clock + 1 }) := by
            rw [hbodyK, seq_continue_some h2k]; rfl
          have hsub1 : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
          have hexit : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
              (none, { t1 with locals := sptInter t1.locals l }) := by
            rw [LoopSemStateFiniteExact.cutRes]
            simp only
            rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub1]
            simp [LoopSemStateFiniteExact.decClock]
          exact ⟨ck + (ck' + 1), none, _, (loop_step_break (hentryK _) hb).trans hexit,
            h2s, h2m, h2g, h2c, rfl, locals_rel_inter ctxt l s1'.locals t1.locals h2l'⟩
        · have he' : (exitLoopCrepResult (some r), s1') = (res, s1) := by
            cases r with
            | «continue» n => cases n with
              | zero => exact absurd rfl hr0
              | succ n => exact he
            | «break» n => cases n with
              | zero => exact absurd rfl hr1
              | succ n => exact he
            | _ => exact he
          simp only [Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          obtain ⟨x, hx⟩ : ∃ x, res1' = some x := by
            cases r <;> simp only [crepToLoopResultHOL] at h2r <;> exact ⟨_, h2r⟩
          subst hx
          have hx0 : x ≠ .continue 0 := by
            intro h; subst h; cases r <;> simp_all [crepToLoopResultHOL]
          have hx1 : x ≠ .break 0 := by
            intro h; subst h; cases r <;> simp_all [crepToLoopResultHOL]
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + ck') } =
              (some x, t1) := by
            rw [hbodyK, seq_continue_some h2']; rfl
          refine ⟨ck + ck', _, _, loop_step_exit (L' := l) hx0 hx1 (hentryK _) hb, h2s, h2m, h2g,
            h2c, ?_, crepToLoopResultLocalsHOL_exitLoop ctxt l _ _ r h2l⟩
          rw [h2r]
          exact crepToLoopResultHOL_exitLoop r hr0 hr1
end Flapjack
