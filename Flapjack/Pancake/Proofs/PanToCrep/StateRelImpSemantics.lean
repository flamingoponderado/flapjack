import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockIoEventsMono
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClock
import Flapjack.Pancake.Semantics.CrepProps.EvaluateAddClockIoEventsMono
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper

/-!
# pan_to_crep whole-program semantics

Counterparts of `cakeml/pancake/proofs/pan_to_crepProofScript.sml:4656-4961`:
* the entry-context lemmas `get_eids_imp_excp_rel` and `mk_ctxt_imp_locals_rel`
  (bead `flapjack-pxn.18.4.4.2`);
* `state_rel_imp_semantics_to_crep` (bead `flapjack-pxn.18.4.4`).

As in the Crep-to-Loop port, both observational semantics are rewritten as the
`semantics_wrapper` of their clock-indexed entry runs.  For panSem this is the
untagged `panSemIsWrapper` below; for crepSem it is the tagged
`crep_sem_is_wrapper`.  The equality then follows from the tagged
`semantics_wrapper_eq`.  Its premises come from:
* the tagged `pc_compile_correct` at the entry `Call NONE start []`;
* `evaluate_add_clock_eq` and `evaluate_add_clock_io_events_mono` on both
  sides.
HOL instead unfolds both `semantics_def`s directly; the statement is HOL's.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanToCrepStateRelImpSemanticsWitnesses

/-- Same-module roundtrip for the relation qualifier's context carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

/-- Same-module roundtrip for the relation qualifier's panSem state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Same-module roundtrip for the relation qualifier's crepSem state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CrepSemBroadState.ofBroad_toBroad state

end PanToCrepStateRelImpSemanticsWitnesses

/-- An entry of the `get_eids_from_decls` association list is an exception
    name paired with the word code of its index. -/
private theorem getEidsEntriesHOL_mem {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (entry : MlS × BitVec width)
    (h : entry ∈ getEidsEntriesHOL decls) :
    ∃ i, i < sizeOfEidsHOL decls ∧
      ∃ hi : i < ((exceptionsHOL decls).map Prod.fst).length,
        entry = (((exceptionsHOL decls).map Prod.fst)[i], BitVec.ofNat width i) := by
  unfold getEidsEntriesHOL at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_zip, List.length_map, List.length_range, Nat.lt_min] at hi
  refine ⟨i, hi.2, by simpa using hi.1, ?_⟩
  simp [List.getElem_zip]

/-- Exact HOL `get_eids_imp_excp_rel` (`pan_to_crepProofScript.sml:4656-4660`):

    ```
    !seids (pc:'a decl list).
      panLang$size_of_eids pc < dimword (:'a) /\
      FDOM seids = FDOM (get_eids_from_decls pc) ==>
        excp_rel (get_eids_from_decls pc) seids
    ```

    HOL `dimword (:'a)` is `2 ^ width`, and `FDOM` equality is pointwise
    definedness of the canonical finite-map lookups, as in the tagged
    `excp_rel_def`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "get_eids_imp_excp_rel"
  (fmap_as_finite_support_relation := [seids]) (words_as_type_indexed_bitvec)]
theorem getEidsImpExcpRelExact {width : Nat} [NeZero width] :
    ∀ (seids : HolFiniteMapExact MlS ShapeHOL) (pc : List (DeclHOL width)),
      sizeOfEidsHOL pc < 2 ^ width ∧
        (∀ key, (seids.lookup key).isSome = ((getEidsFromDeclsHOL pc).lookup key).isSome) →
      panToCrepExcpRelFiniteExact (getEidsFromDeclsHOL pc) seids := by
  intro seids pc ⟨hsize, hdom⟩
  refine ⟨hdom, ?_⟩
  intro e e' n n' he he' hnn
  obtain ⟨entry, hmem, hkey, hval⟩ :=
    flookupAlistToFmap_mem (getEidsEntriesHOL pc) e n he
  obtain ⟨entry', hmem', hkey', hval'⟩ :=
    flookupAlistToFmap_mem (getEidsEntriesHOL pc) e' n' he'
  obtain ⟨i, hi, hil, rfl⟩ := getEidsEntriesHOL_mem pc entry hmem
  obtain ⟨j, hj, hjl, rfl⟩ := getEidsEntriesHOL_mem pc entry' hmem'
  simp only at hkey hval hkey' hval'
  subst hkey hkey' hval hval'
  have hij : i = j := by
    have h := congrArg BitVec.toNat hnn
    simp only [BitVec.toNat_ofNat] at h
    rwa [Nat.mod_eq_of_lt (Nat.lt_trans hi hsize), Nat.mod_eq_of_lt (Nat.lt_trans hj hsize)] at h
  subst hij
  rfl

/-- Exact HOL `mk_ctxt_imp_locals_rel` (`pan_to_crepProofScript.sml:4677-4679`):
    `!pc lcl es. locals_rel (mk_ctxt FEMPTY (make_funcs pc) 0 es) FEMPTY lcl`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "mk_ctxt_imp_locals_rel"
  (fmap_as_finite_support_relation := [PanToCrepContextExact.vars, lcl, es])
  (words_as_type_indexed_bitvec)]
theorem mkCtxtImpLocalsRelExact {width : Nat} [NeZero width] :
    ∀ (pc : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (lcl : HolFiniteMapExact Nat (HolWordLab width))
      (es : HolFiniteMapExact MlS (BitVec width)),
      panToCrepLocalsRelFiniteExact
        (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL pc) 0 es)
        HolFiniteMapExact.empty lcl := by
  intro pc lcl es
  refine ⟨⟨?_, ?_⟩, ⟨Nat.zero_le _, ?_⟩, ?_⟩ <;>
    intros <;> simp_all [mkCtxtExactHOL, HolFiniteMapExact.empty]

/-- The panSem entry-run classification matching `panSem$semantics_def`:
    the Fail test rejects everything except `TimeOut`, `FinalFFI` and
    `Return`.  Flapjack-specific: HOL states no wrapper form of panSem. -/
def panEntryClass {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.returned _) => .CompleteResult HolOutcome.success
  | _ => .RunError

open Classical in
private theorem panSemIsWrapper_aux {width : Nat} {σ : Type} [NeZero width]
    (E : Nat → Option (PanSemResultExact width) × PanSemStateFiniteExact width σ) :
    (if ∃ k, (match (E k).1 with
        | some .timeOut => False
        | some (.finalFfi _) => False
        | some (.returned _) => False
        | _ => True)
      then HolBehaviour.fail
      else
        match holOptionSome (fun res => ∃ k t r outcome,
            E k = (r, t) ∧
            (match r with
             | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
             | some (.returned _) => outcome = HolOutcome.success
             | _ => False) ∧
            res = HolBehaviour.terminate outcome t.ffi.ioEvents) with
        | some res => res
        | none => .diverge (HolLList.buildLprefixLub (fun l => ∃ k,
            l = HolLList.fromList (E k).2.ffi.ioEvents))) =
      crepToLoopSemanticsWrapper
        (Prod.map panEntryClass
          (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) := by
  have hk : ∀ k, (match (E k).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.returned _) => False
      | _ => True) ↔
      ∃ v, (Prod.map panEntryClass
        (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) k = (.RunError, v) := by
    intro k
    simp only [Function.comp_apply]
    generalize E k = e
    rcases e with ⟨r, t⟩
    rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [panEntryClass]
  have hP : (fun res => ∃ k t r outcome,
      E k = (r, t) ∧
      (match r with
       | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
       | some (.returned _) => outcome = HolOutcome.success
       | _ => False) ∧
      res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
      (fun res => ∃ k r ev,
        (Prod.map panEntryClass
          (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘ E) k =
          (.CompleteResult r, ev) ∧ res = HolBehaviour.terminate r ev) := by
    funext res
    apply propext
    constructor
    · rintro ⟨k, t, r, outcome, he, hm, rfl⟩
      refine ⟨k, outcome, t.ffi.ioEvents, ?_, rfl⟩
      simp only [Function.comp_apply, he, Prod.map]
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp at hm <;>
        simp [panEntryClass, hm]
    · rintro ⟨k, r', ev, hf, rfl⟩
      simp only [Function.comp_apply] at hf
      rcases he : E k with ⟨r, t⟩
      rw [he] at hf
      simp only [Prod.map, Prod.mk.injEq] at hf
      obtain ⟨hg, rfl⟩ := hf
      refine ⟨k, t, r, r', he, ?_, rfl⟩
      rcases r with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp [panEntryClass] at hg ⊢ <;>
        exact hg.symm
  unfold crepToLoopSemanticsWrapper
  rw [exists_congr hk, hP]
  rfl

/-- `panSem$semantics_def` as the `semantics_wrapper` of its entry runs.
    Flapjack-specific: HOL states no panSem analogue of
    `crep_sem_is_wrapper`. -/
theorem panSemIsWrapper {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (start : MlS) :
    PanSemStateFiniteExact.semantics s start =
      crepToLoopSemanticsWrapper
        (Prod.map panEntryClass
            (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
          (fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
            (.call none start [] : ProgHOL width))) := by
  unfold PanSemStateFiniteExact.semantics
  exact panSemIsWrapper_aux _

/-- Exact HOL `state_rel_imp_semantics_to_crep`
    (`pan_to_crepProofScript.sml:4694-4705`):

    ```
    !(s:('a,'b) panSem$state) (t:('a,'b) crepSem$state) pan_code start.
      state_rel s t ∧
      ALL_DISTINCT (MAP FST (functions pan_code)) ∧
      s.code = alist_to_fmap(functions pan_code) ∧
      t.code = alist_to_fmap (pan_to_crep$compile_to_crep pan_code) ∧
      s.locals = FEMPTY ∧
      EVERY (localised_prog ∘ FST o SND ∘ SND) (functions pan_code) ∧
      panLang$size_of_eids pan_code < dimword (:'a) /\
      FDOM s.eshapes = FDOM (get_eids_from_decls pan_code) ∧
      semantics s start <> Fail ==>
        semantics t start = semantics s start
    ```

    HOL `alist_to_fmap l` is `HolFiniteMapExact.empty.updateList l.reverse`,
    as in the tagged `mk_ctxt_code_imp_code_rel`.  `FEMPTY` is
    `HolFiniteMapExact.empty`, and `dimword (:'a)` is `2 ^ width`.  `FDOM`
    equality is pointwise definedness of the canonical lookups.  The `EVERY`
    projection is each function's body.  There is no additional premise; see
    the module docstring for the proof route. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_imp_semantics_to_crep"
  (fmap_as_finite_support_relation :=
    [PanSemStateFiniteExact.locals, PanSemStateFiniteExact.globals,
      PanSemStateFiniteExact.code, PanSemStateFiniteExact.eshapes,
      CrepSemHOLState.code])
  (words_as_type_indexed_bitvec)]
theorem stateRelImpSemanticsToCrep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
      (pan_code : List (DeclHOL width)) (start : MlS),
      panToCrepStateRelFiniteExact s t ∧
        ((functionsHOL pan_code).map Prod.fst).Nodup ∧
        s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse ∧
        t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse ∧
        s.locals = HolFiniteMapExact.empty ∧
        (∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true) ∧
        sizeOfEidsHOL pan_code < 2 ^ width ∧
        (∀ key, (s.eshapes.lookup key).isSome =
          ((getEidsFromDeclsHOL pan_code).lookup key).isSome) ∧
        PanSemStateFiniteExact.semantics s start ≠ .fail →
      crepSemantics t start = PanSemStateFiniteExact.semantics s start := by
  intro s t pan_code start ⟨hsr, hdist, hscode, htcode, hloc, hlocal, hsize, hdom, hfail⟩
  have hfail' := hfail
  rw [panSemIsWrapper] at hfail'
  rw [panSemIsWrapper, crepSemIsWrapper]
  apply crepToLoopSemanticsWrapper_eq _ _ hfail'
  · -- Source runs are matched by target runs at the same clock (HOL's
    -- `pc_compile_correct` step on `Call NONE start []`).
    intro k r ev habs hr
    simp only [Function.comp, Prod.map] at habs
    rcases hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width) with ⟨res, s1⟩
    rw [hev] at habs
    simp only [Prod.mk.injEq] at habs
    obtain ⟨hcl, rfl⟩ := habs
    have hne : res ≠ some .error := by
      intro h
      subst h
      exact hr hcl.symm
    let ctxt : PanToCrepContextExact width :=
      mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL pan_code)) 0
        (getEidsFromDeclsHOL pan_code)
    have hsr' : panToCrepStateRelFiniteExact ({ s with clock := k } : PanSemStateFiniteExact width σ)
        ({ t with clock := k } : CrepSemHOLState width σ) := by
      obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10⟩ := hsr
      exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10⟩
    have hcode : codeRelExactHOLW ctxt ({ s with clock := k } : PanSemStateFiniteExact width σ).code
        ({ t with clock := k } : CrepSemHOLState width σ).code := by
      show codeRelExactHOLW ctxt s.code t.code
      rw [hscode, htcode]
      exact mkCtxtCodeImpCodeRelExactHOLW pan_code hdist hlocal
    have hexcp : panToCrepExcpRelFiniteExact ctxt.eids
        ({ s with clock := k } : PanSemStateFiniteExact width σ).eshapes :=
      getEidsImpExcpRelExact s.eshapes pan_code ⟨hsize, hdom⟩
    have hlocals : panToCrepLocalsRelFiniteExact ctxt
        ({ s with clock := k } : PanSemStateFiniteExact width σ).locals
        ({ t with clock := k } : CrepSemHOLState width σ).locals := by
      show panToCrepLocalsRelFiniteExact ctxt s.locals t.locals
      rw [hloc]
      exact mkCtxtImpLocalsRelExact _ _ _
    obtain ⟨res1, t1, hrun, hsr1, _, _, hres⟩ :=
      pcCompileCorrect (.call none start []) { s with clock := k } res s1 { t with clock := k } ctxt
        ⟨hev, hne, hsr', hcode, hexcp, hlocals, by simp [localisedProgHOL, everyExpListHOL]⟩
    have hcomp : compileProgExactHOLW ctxt (.call none start [] : ProgHOL width) =
        (.call none start [] : CrepProgHOL width) := by
      simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileExpExactHOLWList]
    rw [hcomp] at hrun
    refine ⟨0, ?_⟩
    simp only [Function.comp, Prod.map, Nat.add_zero]
    rw [hrun]
    have hffi : t1.ffi = s1.ffi := hsr1.2.2.2.2.2.2.2.1.symm
    rw [hffi, ← hcl]
    refine Prod.ext ?_ rfl
    rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp only at hres <;>
      simp_all [panEntryClass]
  · -- Target runs that complete are stable under more clock.
    intro k k' r ev hconc hr
    simp only [Function.comp, Prod.map] at hconc ⊢
    rcases hev : evalCrepSemHOLProgExact { t with clock := k }
        (.call none start [] : CrepProgHOL width) with ⟨res, st⟩
    rw [hev] at hconc
    simp only [Prod.mk.injEq] at hconc
    obtain ⟨hcl, rfl⟩ := hconc
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      exact hr hcl.symm
    have hadd := evalCrepSemHOLProgExact_add_clock_eq _ { t with clock := k } res st k' hev hnt
    have heq : ({ { t with clock := k } with clock := k + k' } : CrepSemHOLState width σ) =
        { t with clock := k + k' } := by cases t; rfl
    simp only at hadd
    rw [heq] at hadd
    rw [hadd]
    exact Prod.ext hcl rfl
  · -- Source runs that complete are stable under more clock.
    intro k k' r ev habs hr
    simp only [Function.comp, Prod.map] at habs ⊢
    rcases hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width) with ⟨res, st⟩
    rw [hev] at habs
    simp only [Prod.mk.injEq] at habs
    obtain ⟨hcl, rfl⟩ := habs
    have hnt : res ≠ some .timeOut := by
      intro h
      subst h
      exact hr hcl.symm
    have hadd := panPropsEvaluateAddClockEq _ { s with clock := k } res st k' ⟨hev, hnt⟩
    simp only at hadd
    rw [hadd]
    exact Prod.ext hcl rfl
  · -- Source traces grow with the clock.
    intro k k' ev habs
    refine ⟨_, _, rfl, ?_⟩
    have hev := (congrArg Prod.snd habs).symm
    simp only [Function.comp, Prod.map] at hev ⊢
    rw [hev]
    exact panPropsEvaluateAddClockIoEventsMono (.call none start []) { s with clock := k } k'
  · -- Target traces grow with the clock.
    intro k k' ev hconc
    refine ⟨_, _, rfl, ?_⟩
    have hev := (congrArg Prod.snd hconc).symm
    simp only [Function.comp, Prod.map] at hev ⊢
    rw [hev]
    exact crepPropsEvaluateAddClockIoEventsMono (.call none start []) { t with clock := k } k'

end Flapjack
