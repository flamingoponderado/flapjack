import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect.Assembly

/-!
# crep_to_loop `code_rel_evaluate_call_correct`

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml:4072-4115`
(bead `flapjack-pxn.18.5.6.57`).  As in HOL, the source entry call is first
transported through `crep_arith$simp_prog_correct` to the `mapcs`-simplified
code, which `code_rel2` relates to the target code.  `ncompile_correct` then
runs at empty live set `LN`, and `compile (Call NONE start [])` is
`Seq (Call NONE (SOME (find_lab ctxt start)) [] NONE) Skip`, removed by
`evaluate_Seq_Skip`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-! Owning carriers of the finite maps the statement traverses; same-module
witnesses for the `fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopCodeRelEvaluateCallWitnesses

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

end CrepToLoopCodeRelEvaluateCallWitnesses

private theorem crepSimpProgHOL_call_none_nil {width : Nat} [NeZero width]
    (start : MlString) :
    crepSimpProgHOL (.call none start [] : CrepProgHOL width) = .call none start [] := by
  conv => lhs; unfold crepSimpProgHOL
  rfl

private theorem compileHOLExact_call_none_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (start : MlString) :
    compileHOLExact (width := width) ctxt .ln (.call none start []) =
      .seq (.call none (some (findLabExact ctxt start)) [] none) .skip := by
  simp [compileHOLExact, compileExpsHOLExact, genTemps, loopNestedSeqHOL]

/-- Exact HOL `code_rel_evaluate_call_correct`
    (`crep_to_loopProofScript.sml:4072-4108`).  The premises are HOL's, in
    order: `code_rel2`, the source entry run, the seven state equalities
    (`memaddrs`/`sh_memaddrs` in the reviewed set-as-Bool rendering of
    `state_rel`), `mem_rel`, `globals_rel`, empty source locals, the two code
    equalities, the `make_funcs` lookup, `find_lab = lc`, `alist_to_fmap`, the
    `make_funcs` context, the `ALOOKUP` entry, `distinct_vars`, `ctxt_max`, and
    the non-Error result.  The conclusion is HOL's target Loop entry call with an
    added clock, `state_rel`, and the result mapping (the canonical
    `resultToLoop`, as in `ncompile_correct`). -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "code_rel_evaluate_call_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals, s_code])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopCodeRelEvaluateCallCorrect {width : Nat} [NeZero width] {σ : Type}
    (nctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width))
    (start : MlString) (s : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s' : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width)) (lc : Nat)
    (prog : CrepProgHOL width) :
    crepToLoopCodeRel2Exact nctxt s_code t_code →
    evalCrepSemHOLProgExact s (.call none start []) = (res, s') →
    s.be = t.be ∧ s.shMemaddrs = (fun address => t.shMdomain address = true) ∧
      s.memaddrs = (fun address => t.mdomain address = true) ∧ s.clock = t.clock ∧
      s.ffi = t.ffi ∧ s.baseAddr = t.baseAddr ∧ s.topAddr = t.topAddr ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      s.locals = HolFiniteMapExact.empty ∧
      s.code = s_code ∧ t.code = t_code →
    (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
      some (findLabExact nctxt start, 0) →
    findLabExact nctxt start = lc ∧
      s.code = alistToFmapCodeExact crep_code ∧
      nctxt.funcs = crepToLoopMakeFuncsExactHOL crep_code ∧
      holAlookup crep_code start = some ([], prog) ∧
      crepToLoopDistinctVarsExact nctxt.vars ∧
      crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars →
    res ≠ some .error →
    ∃ (k : Nat) (res' : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (t' : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate
          (.call none (some (findLabExact nctxt start)) [] none)
          { t with clock := t.clock + k } = (res', t') ∧
      crepToLoopStateRelExact s' t' ∧
      res' = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res := by
  intro hcode2 he ⟨hbe, hsh, hmd, hclk, hffi, hbase, htop, hmem, hglob, hloc, hsc, htc⟩
    _hmf ⟨_hlc, _halist, _hfuncs, _halookup, hdistinct, hmax⟩ hne
  have hsimp := crepArithSimpProgCorrect (.call none start []) s res s' he hne
  rw [crepSimpProgHOL_call_none_nil] at hsimp
  have hcodeRel : crepToLoopCodeRelExact nctxt (crepSimpMapcsHOL s).code t.code := by
    have h : crepToLoopCodeRelExact nctxt
        (s_code.map2 (fun entry =>
          match entry with
          | (_, parameters, program) => (parameters, crepSimpProgHOL program))) t_code :=
      hcode2
    rw [← hsc, ← htc] at h
    exact h
  have hlocals : crepToLoopLocalsRelExact nctxt .ln (crepSimpMapcsHOL s).locals t.locals := by
    refine ⟨hdistinct, hmax, ?_, ?_⟩
    · intro n hn
      simp [sptMem, sptDomain, sptLookup] at hn
    · intro vname value hlookup
      change s.locals.lookup vname = some value at hlookup
      rw [hloc] at hlookup
      simp [HolFiniteMapExact.empty] at hlookup
  have hstate : crepToLoopStateRelExact (crepSimpMapcsHOL s) t :=
    ⟨hmd, hsh, hclk, hbe, hffi, hbase, htop⟩
  obtain ⟨ck, res1, t1, hrun, hstate', _, _, _, hres, _⟩ :=
    crepToLoop_ncompile_correct (.call none start []) (crepSimpMapcsHOL s) res
      (crepSimpMapcsHOL s') t nctxt .ln
      ⟨hsimp, hne, hstate, hmem, hglob, hcodeRel, hlocals⟩
  rw [compileHOLExact_call_none_nil, LoopSemStateFiniteExact.evaluate_Seq_Skip] at hrun
  exact ⟨ck, res1, t1, hrun, hstate', hres⟩

end Flapjack
