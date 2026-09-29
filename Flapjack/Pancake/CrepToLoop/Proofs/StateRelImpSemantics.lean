import Flapjack.Pancake.CrepToLoop.Proofs.CodeRelEvaluateCallCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.CrepNonFailStartLookup
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClock
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact

/-!
# crep_to_loop `state_rel_imp_semantics`

Exact port of `cakeml/pancake/proofs/crep_to_loopProofScript.sml:4320-4394`
(bead `flapjack-pxn.18.5.6.26`), the whole-program Crep-to-Loop semantics
preservation theorem.  As in HOL, both observational semantics are rewritten
as `semantics_wrapper` of their clock-indexed entry runs (`crep_sem_is_wrapper`,
`loop_sem_is_wrapper`), a start entry `ALOOKUP crep_code start = SOME ([], prog)`
is derived from the non-`Fail` premise, and `semantics_wrapper_eq` is applied.
Its premises come from `mk_ctxt_code_imp_code_rel2` with
`code_rel_evaluate_call_correct` (source runs transported to the target),
`evaluate_add_clock_eq` on both sides, and `evaluate_io_mono_rephrases`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm

/-! Owning carriers of the finite maps the statement traverses; same-module
witnesses for the `fmap_as_finite_support_relation` qualifier. -/
namespace CrepToLoopStateRelImpSemanticsWitnesses

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

end CrepToLoopStateRelImpSemanticsWitnesses

/-- The Crep result classification of `crep_sem_is_wrapper`. -/
private def crepEntryClass {width : Nat} [NeZero width] :
    Option (CrepResultHOLExact width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.return _) => .CompleteResult HolOutcome.success
  | _ => .RunError

/-- The Loop result classification of `loop_sem_is_wrapper`. -/
private def loopEntryClass {width : Nat} [NeZero width] :
    Option (LoopSemStateFiniteExact.LoopResultExact width) →
      CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.result _) => .CompleteResult HolOutcome.success
  | _ => .RunError

/-- The `ncompile_correct` result mapping preserves the wrapper classification. -/
private theorem loopEntryClass_resultToLoop {width : Nat} [NeZero width]
    (r : Option (CrepResultHOLExact width)) :
    loopEntryClass (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop r) =
      crepEntryClass r := by
  rcases r with _ | r
  · rfl
  · cases r <;> rfl

/-- Exact HOL `state_rel_imp_semantics`
    (`crep_to_loopProofScript.sml:4320-4332`):
    `∀s t crep_code start lc c. s.memaddrs = t.mdomain ∧ s.be = t.be ∧
      s.sh_memaddrs = t.sh_mdomain ∧ s.ffi = t.ffi ∧ s.base_addr = t.base_addr ∧
      s.top_addr = t.top_addr ∧ mem_rel s.memory t.memory s.memaddrs ∧
      globals_rel s.globals t.globals ∧ ALL_DISTINCT (MAP FST crep_code) ∧
      s.code = alist_to_fmap crep_code ∧
      t.code = fromAList (crep_to_loop$compile_prog c crep_code) ∧
      s.locals = FEMPTY ∧ FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) ∧
      semantics s start ≠ Fail ⇒ semantics t lc = semantics s start`.
    The two domain equalities use the reviewed set-as-Bool rendering of the
    tagged `state_rel`; `c` is the target architecture consumed by the tagged
    `compile_prog_def` port; `fromAList` is `sptFromAList`.  No other premise. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "state_rel_imp_semantics"
  (fmap_as_finite_support_relation := [CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoopStateRelImpSemantics {width : Nat} [NeZero width] {σ : Type} :
    ∀ (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
      (crep_code : List (MlString × List Nat × CrepProgHOL width))
      (start : MlString) (lc : Nat) (c : AsmArchitecture),
      s.memaddrs = (fun address => t.mdomain address = true) ∧
        s.be = t.be ∧ s.shMemaddrs = (fun address => t.shMdomain address = true) ∧
        s.ffi = t.ffi ∧ s.baseAddr = t.baseAddr ∧ s.topAddr = t.topAddr ∧
        crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
        (crep_code.map Prod.fst).Nodup ∧
        s.code = alistToFmapCodeExact crep_code ∧
        t.code = sptFromAList (compileProgHOLExact c crep_code) ∧
        s.locals = HolFiniteMapExact.empty ∧
        (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0) ∧
        crepSemantics s start ≠ .fail →
      LoopSemStateFiniteExact.semantics t lc = crepSemantics s start := by
  intro s t crep_code start lc c
    ⟨hmd, hbe, hsh, hffi, hbase, htop, hmem, hglob, hdist, hscode, htcode, hloc, hmf, hfail⟩
  obtain ⟨prog, hprog⟩ :=
    crepSemantics_ne_fail_imp_holAlookup s crep_code start hscode hloc hdist hfail
  let absf : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent :=
    (Prod.map crepEntryClass (fun st : CrepSemHOLState width σ => st.ffi.ioEvents)) ∘
      (fun k => evalCrepSemHOLProgExact { s with clock := k } (.call none start []))
  let concf : Nat → CrepToLoopSemanticsRunRes HolOutcome × List HolIoEvent :=
    (Prod.map loopEntryClass
        (fun st : LoopSemStateFiniteExact width σ => st.ffi.ioEvents)) ∘
      (fun k => LoopSemStateFiniteExact.evaluate
        (.call none (some lc) [] none : HolLoopProg width) { t with clock := k })
  have hfail' : crepToLoopSemanticsWrapper absf ≠ .fail := by
    have h := hfail
    rw [crepSemIsWrapper] at h
    exact h
  rw [loopSemIsWrapper, crepSemIsWrapper]
  change crepToLoopSemanticsWrapper concf = crepToLoopSemanticsWrapper absf
  -- The source-to-target context and code relation.
  let nctxt : CrepToLoopContextExact :=
    mkCtxtExact c HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL crep_code) 0
  have hcode2 : crepToLoopCodeRel2Exact nctxt s.code t.code := by
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRel2Exact c crep_code start prog ⟨hdist, hprog⟩
  have hlc : findLabExact nctxt start = lc := by
    simp [findLabExact, nctxt, mkCtxtExact, hmf]
  have hdv : crepToLoopDistinctVarsExact nctxt.vars := by
    intro x y n m hx
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hx
  have hcm : crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars := by
    intro v m hv
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hv
  apply crepToLoopSemanticsWrapper_eq absf concf hfail'
  · -- Source runs are matched by target runs with extra clock.
    intro k r ev habs hr
    rcases hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start [])
      with ⟨res, s1⟩
    have habs' : (crepEntryClass res, s1.ffi.ioEvents) = (r, ev) := by
      have h := habs
      simp only [absf, Function.comp, Prod.map, hev] at h
      exact h
    simp only [Prod.mk.injEq] at habs'
    obtain ⟨rfl, rfl⟩ := habs'
    have hne : res ≠ some .error := by
      intro h
      subst h
      exact hr rfl
    have hmf' : (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
        some (findLabExact nctxt start, 0) := by
      rw [hlc]
      exact hmf
    obtain ⟨k', res', t', hrun, hsr, hres⟩ :=
      crepToLoopCodeRelEvaluateCallCorrect nctxt s.code t.code start
        { s with clock := k } res s1 { t with clock := k } crep_code lc prog hcode2 hev
        ⟨hbe, hsh, hmd, rfl, hffi, hbase, htop, hmem, hglob, hloc, rfl, rfl⟩ hmf'
        ⟨hlc, hscode, rfl, hprog, hdv, hcm⟩ hne
    refine ⟨k', ?_⟩
    rw [hlc] at hrun
    have hrun' : LoopSemStateFiniteExact.evaluate (.call none (some lc) [] none : HolLoopProg width)
        { t with clock := k + k' } = (res', t') := by
      have heq : ({ { t with clock := k } with clock := k + k' } :
          LoopSemStateFiniteExact width σ) = { t with clock := k + k' } := by
        cases t; rfl
      rw [← heq]
      exact hrun
    simp only [concf, Function.comp, Prod.map, hrun', hres, loopEntryClass_resultToLoop]
    rw [hsr.2.2.2.2.1]
  · -- Target runs that complete are stable under more clock.
    intro k k' r ev hconc hr
    rcases hev : LoopSemStateFiniteExact.evaluate (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := k } with ⟨res, st⟩
    have hconc' : (loopEntryClass res, st.ffi.ioEvents) = (r, ev) := by
      have h := hconc
      simp only [concf, Function.comp, Prod.map, hev] at h
      exact h
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      simp only [loopEntryClass, Prod.mk.injEq] at hconc'
      exact hr hconc'.1.symm
    have hadd := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ res st k' hev hnt
    have heq : ({ { t with clock := k } with clock := k + k' } :
        LoopSemStateFiniteExact width σ) = { t with clock := k + k' } := by
      cases t; rfl
    rw [heq] at hadd
    simp only [concf, Function.comp, Prod.map, hadd]
    exact hconc'
  · -- Source runs that complete are stable under more clock.
    intro k k' r ev habs hr
    rcases hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start [])
      with ⟨res, st⟩
    have habs' : (crepEntryClass res, st.ffi.ioEvents) = (r, ev) := by
      have h := habs
      simp only [absf, Function.comp, Prod.map, hev] at h
      exact h
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      simp only [crepEntryClass, Prod.mk.injEq] at habs'
      exact hr habs'.1.symm
    have hadd := evalCrepSemHOLProgExact_add_clock_eq _ _ res st k' hev hnt
    have heq : ({ { s with clock := k } with clock := k + k' } :
        CrepSemHOLState width σ) = { s with clock := k + k' } := by
      cases s; rfl
    rw [heq] at hadd
    simp only [absf, Function.comp, Prod.map, hadd]
    exact habs'
  · -- Source traces grow with the clock.
    intro k k' ev habs
    refine ⟨(absf k).1, (absf k).2, rfl, ?_⟩
    have hev : ev = (absf (k + k')).2 := (congrArg Prod.snd habs).symm
    rw [hev]
    exact (evaluateIOMonoRephrases (.call none start []) s
      (.call none (some lc) [] none) t k).1 k'
  · -- Target traces grow with the clock.
    intro k k' ev hconc
    refine ⟨(concf k).1, (concf k).2, rfl, ?_⟩
    have hev : ev = (concf (k + k')).2 := (congrArg Prod.snd hconc).symm
    rw [hev]
    exact (evaluateIOMonoRephrases (.call none start []) s
      (.call none (some lc) [] none) t k).2 k'

end Flapjack
