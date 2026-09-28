import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel
import Flapjack.Pancake.Proofs.PanToCrep.TotalEvaluateCases
import Flapjack.Pancake.Semantics.PanProps.ListRelFlatten
import Flapjack.Pancake.Proofs.PanToCrep.EvalDistinctLists

/-!
# `pc_compile_correct` Call case over the exact carriers

Support for the `Call` case of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3107-4231`), stated against
`pcCompileCorrectAt` and `pcCompileCorrectCallIH`. This file starts with the
shared prelude (bead `flapjack-pxn.18.4.3.94.4`). It relates a successful source
argument evaluation and `lookup_code` to the target's flattened argument
evaluation, the target `lookup_code`, and the callee-entry relations. Every
Call sub-case (`Call_TailCall`, `Call_Ret_*`, zero clock) uses these facts.
The helpers are untagged: HOL proves them inline inside the Call case.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ProgHOL ExpHOL sizeOfShapeHOL StructContextExact
  isWfShapeExactHOL)

private theorem listRel_of_zip_all {width : Nat} [NeZero width] :
    ∀ (vshapes : List (MlS × ShapeHOL)) (args : List (ValueHOL width)),
      vshapes.length = args.length →
      ((vshapes.zip args).all
        (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true →
      ListRel (fun vsh arg => vsh.2 = shapeOfHOLExact arg) vshapes args
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | vsh :: vshapes, arg :: args, hlen, hall => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      exact .cons ((shapeEqHOL_eq_true _ _).mp hall.1)
        (listRel_of_zip_all vshapes args (by simpa using hlen) hall.2)

/-- Inversion of a successful exact source `lookup_code`
    (`panSemScript.sml:458-467`): the code map holds `(vshapes, prog, rsh)`,
    the parameter names are distinct, the argument shapes match pointwise
    (`LIST_REL`), and the callee locals are `slc vshapes args`
    (`FEMPTY |++ ZIP (MAP FST vshapes, args)`). -/
theorem lookupCodeHOLFinite_some_inv {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname : MlS) (args : List (ValueHOL width)) (prog : ProgHOL width)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite code fname args =
      some (prog, newlocals, rsh)) :
    ∃ vshapes, code fname = some (vshapes, prog, rsh) ∧
      (vshapes.map Prod.fst).Nodup ∧
      ListRel (fun vsh arg => vsh.2 = shapeOfHOLExact arg) vshapes args ∧
      newlocals = slcHOL vshapes args := by
  have hexact := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some code fname args prog
    newlocals rsh h
  unfold lookupCodeHOLExact at hexact
  split at hexact
  · simp at hexact
  · rename_i parameters body returnShape hcode
    split at hexact
    · rename_i hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hexact
      obtain ⟨rfl, hcallee, rfl⟩ := hexact
      refine ⟨parameters, hcode, hcond.1,
        listRel_of_zip_all parameters args hcond.2.1 hcond.2.2, ?_⟩
      apply HolFiniteMapExact.ext
      rw [← hcallee]
      rfl
    · simp at hexact

private theorem everyExpHOL_root {width : Nat} [NeZero width]
    (P : ExpHOL width → Bool) (e : ExpHOL width) (h : everyExpHOL P e = true) :
    P e = true := by
  cases e <;> simp only [everyExpHOL, Bool.and_eq_true] at h <;>
    first | exact h | exact h.1 | exact h.1.1

private theorem everyExpListHOL_all {width : Nat} [NeZero width]
    (P : ExpHOL width → Bool) :
    ∀ (es : List (ExpHOL width)), everyExpListHOL P es = true → es.all P = true
  | [], _ => rfl
  | e :: es, h => by
      simp only [everyExpListHOL, Bool.and_eq_true] at h
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨everyExpHOL_root P e h.1, everyExpListHOL_all P es h.2⟩

private theorem compileExpExactHOLWList_eq_map {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) :
    ∀ (es : List (ExpHOL width)),
      compileExpExactHOLWList ctxt es = es.map (compileExpExactHOLW ctxt)
  | [] => by simp [compileExpExactHOLWList]
  | e :: es => by
      rw [compileExpExactHOLWList, compileExpExactHOLWList_eq_map ctxt es]
      rfl

private theorem mapM_some_of_map_eq {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.map f = ys.map some → xs.mapM f = some ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp [List.mapM_cons, h.1, mapM_some_of_map_eq f xs ys h.2]

private theorem evalListHOLExact_map {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    ∀ (es : List (ExpHOL width)) (vs : List (ValueHOL width)),
      evalListHOLExact state es = some vs → es.map (evalHOLExact state) = vs.map some
  | [], vs, h => by simp [evalListHOLExact] at h; subst vs; rfl
  | e :: es, vs, h => by
      cases hhead : evalHOLExact state e with
      | none => simp [evalListHOLExact, hhead] at h
      | some head =>
          cases htail : evalListHOLExact state es with
          | none => simp [evalListHOLExact, hhead, htail] at h
          | some tail =>
              have hvs : vs = head :: tail := by
                simpa [evalListHOLExact, hhead, htail] using h.symm
              subst vs
              simp [hhead, evalListHOLExact_map state es tail htail]

/-- Target argument evaluation for a Call (`pan_to_crepProofScript.sml:3113-3116`,
    `OPT_MMAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) =
    SOME (FLAT (MAP flatten args))`, by `opt_mmap_eq_some` and
    `eval_map_comp_exp_flat_eq`). The source premise is the exact argument
    evaluation used by the tagged Pan Call clause. The localisation premise is
    the `EVERY localised_exp argexps` conjunct of `localised_prog (Call ...)`.
    The conclusion is in the form of the target Call clause's `OPT_MMAP (eval t)`. -/
theorem pcCompileCorrectCallTargetArgs {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (ctxt : PanToCrepContextExact width)
    (argexps : List (ExpHOL width)) (args : List (ValueHOL width))
    (hargs : s.evalListHOLFinite
        (h := fun address => Classical.propDecidable (s.memaddrs address))
        argexps = some args)
    (hstate : panToCrepStateRelFiniteExact s t)
    (hcode : codeRelExactHOLW ctxt s.code t.code)
    (hlocals : panToCrepLocalsRelFiniteExact ctxt s.locals t.locals)
    (hlocalised : everyExpListHOL localisedExpHOL argexps = true) :
    ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst).mapM
        (@evalCrepSemHOLExp width _ σ t
          (fun address => Classical.propDecidable (t.memaddrs address))) =
      some (args.flatMap flattenHOL) := by
  classical
  have hmap : argexps.map s.evalHOLFinite = args.map some := by
    have := evalListHOLExact_map s.toExact argexps args
      (by simpa [PanSemStateFiniteExact.evalListHOLFinite] using hargs)
    simpa [PanSemStateFiniteExact.evalHOLFinite] using this
  have hflat := evalMapCompExpFlatEqHOL s ctxt t argexps args hmap hstate hcode hlocals
    (everyExpListHOL_all localisedExpHOL argexps hlocalised)
  rw [compileExpExactHOLWList_eq_map, List.flatMap_map]
  exact mapM_some_of_map_eq _ _ _ (by simpa using hflat)

/-- The shared prelude of the positive-clock Call sub-cases
    (`pan_to_crepProofScript.sml:3107-3131` and the openings of `Call_TailCall`
    `:3182-3215` and `Call_Ret_*`). From the source argument evaluation, the
    source `lookup_code`, and the pre-state relations, it gives:
    * the source code entry `(vshapes, prog, rsh)`, `localised_prog prog`, and the
      context signature (`code_rel_imp`);
    * the target flattened arguments evaluating to `FLAT (MAP flatten args)`;
    * the target `lookup_code` returning the compiled body under
      `nctxt = ctxt_fc ctxt.funcs ctxt.eids vs shs ns` and callee locals
      `tlc ns args`, with `ns = GENLIST I (size_of_shape (Comb shs))` of the
      flattened-argument length (`list_rel_length_shape_of_flatten`,
      `opt_mmap_eval_is_wf_shape_v`);
    * all four relations at the callee entry states
      (`call_preserve_state_code_locals_rel`), where the source entry is the
      tagged evaluator's `dec_clock s with locals := newlocals`.
    No target run or post-state is assumed. -/
theorem pcCompileCorrectCallPrelude {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (ctxt : PanToCrepContextExact width)
    (fname : MlS) (argexps : List (ExpHOL width)) (args : List (ValueHOL width))
    (prog : ProgHOL width) (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (rsh : ShapeHOL)
    (hargs : s.evalListHOLFinite
        (h := fun address => Classical.propDecidable (s.memaddrs address))
        argexps = some args)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args =
      some (prog, newlocals, rsh))
    (hstate : panToCrepStateRelFiniteExact s t)
    (hcode : codeRelExactHOLW ctxt s.code t.code)
    (hexcp : panToCrepExcpRelFiniteExact ctxt.eids s.eshapes)
    (hlocals : panToCrepLocalsRelFiniteExact ctxt s.locals t.locals)
    (hlocalised : everyExpListHOL localisedExpHOL argexps = true) :
    ∃ vshapes : List (MlS × ShapeHOL),
      let ns := List.range (sizeOfShapeHOL (.comb (vshapes.map Prod.snd)))
      let nctxt := ctxtFcExactHOL ctxt.funcs ctxt.eids
        (vshapes.map Prod.fst) (vshapes.map Prod.snd) ns
      s.code.lookup fname = some (vshapes, prog, rsh) ∧
      localisedProgHOL prog = true ∧
      ctxt.funcs.lookup fname = some (vshapes, rsh) ∧
      ns.length = (args.flatMap flattenHOL).length ∧
      ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) =
        some (args.flatMap flattenHOL) ∧
      lookupCodeFiniteHOL t.code fname (args.flatMap flattenHOL)
          (args.flatMap flattenHOL).length =
        some (compileProgExactHOLW nctxt prog, tlcHOL ns args) ∧
      panToCrepStateRelFiniteExact
        (PanSemStateFiniteExact.callEntryStateHOLFinite s newlocals)
        { decClockCrepSemHOL t with locals := tlcHOL ns args } ∧
      codeRelExactHOLW nctxt
        (PanSemStateFiniteExact.callEntryStateHOLFinite s newlocals).code
        { decClockCrepSemHOL t with locals := tlcHOL ns args }.code ∧
      panToCrepExcpRelFiniteExact nctxt.eids
        (PanSemStateFiniteExact.callEntryStateHOLFinite s newlocals).eshapes ∧
      panToCrepLocalsRelFiniteExact nctxt
        (PanSemStateFiniteExact.callEntryStateHOLFinite s newlocals).locals
        (tlcHOL ns args) := by
  classical
  obtain ⟨vshapes, hsrc, hnodup, hrel, rfl⟩ :=
    lookupCodeHOLFinite_some_inv s.code.lookup fname args prog newlocals rsh hlookup
  have hwfv := optMmapEvalIsWfShapeVHOL argexps args s t ctxt t.locals
    ⟨by simpa [evalListHOLFiniteClassical] using hargs, hstate, hlocals⟩
  have hsize := listRelLengthShapeOfFlattenHOL vshapes args ⟨hrel, hwfv⟩
  have hflatLen : (args.flatMap flattenHOL).length = ((args.map flattenHOL).flatten).length := by
    simp [List.flatMap]
  obtain ⟨hprogLoc, hfuncs, htgt⟩ :=
    codeRelExactHOLW_imp ctxt s.code t.code hcode fname vshapes prog rsh hsrc
  refine ⟨vshapes, hsrc, hprogLoc, hfuncs, ?_, ?_, ?_, ?_⟩
  · simp [List.length_range, hsize, hflatLen]
  · exact pcCompileCorrectCallTargetArgs s t ctxt argexps args hargs hstate hcode hlocals
      hlocalised
  · simp only [lookupCodeFiniteHOL, htgt]
    rw [if_pos ⟨by simp [List.length_range, hsize, hflatLen], List.nodup_range⟩]
    congr 3
    apply HolFiniteMapExact.ext
    funext k
    simp [tlcHOL, HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL_eq_FUPDATE_LIST, List.flatMap]
  · have hwf : ∀ arg, arg ∈ args →
        isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact arg) = true := by
      intro arg harg
      rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl arg]
      exact hwfv arg harg
    have hpres := panToCrepCallPreserveStateCodeLocalsRelExact rsh ctxt s t fname vshapes
      prog args (List.range (sizeOfShapeHOL (.comb (vshapes.map Prod.snd))))
      hnodup hrel hstate hcode hexcp hlocals hsrc hfuncs List.nodup_range
      (by rw [hsize]) htgt
      (by simp [List.length_range, hsize]) hwf
    simpa [PanSemStateFiniteExact.callEntryStateHOLFinite,
      PanSemStateFiniteExact.decClockHOLFinite] using hpres

/-- The target run of `compile ctxt (Call NONE fname argexps)`
    (`pan_to_crepScript.sml:221`, a tail `Call NONE` with the flattened compiled
    arguments), given the target argument evaluation, the target `lookup_code`,
    and a positive target clock. It is the tagged line-443 Crep Call clause with
    `caltyp = NONE`: a plain match on the dec-clocked callee run. -/
theorem pcCompileCorrectCallNoReturnTarget {width : Nat} {σ : Type} [NeZero width]
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (fname : MlS) (argexps : List (ExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (hargs : ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0) :
    evalCrepSemHOLProgExact t
        (compileProgExactHOLW ctxt (.call none fname argexps : ProgHOL width)) =
      match evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body with
      | (none, st) => (some .error, st)
      | (some (.break _), st) => (some .error, st)
      | (some (.continue _), st) => (some .error, st)
      | (some (.return retvs), st) => (some (.return retvs), CrepSemHOLState.emptyLocals st)
      | (some (.exception eid), st) => (some (.exception eid), CrepSemHOLState.emptyLocals st)
      | (res, st) => (res, CrepSemHOLState.emptyLocals st) := by
  classical
  simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
  rw [evalCrepSemHOLProgExact_call_holShape]
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_neg (by simp), if_neg hclock]
  rcases evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body with
    ⟨_ | r, st⟩
  · rfl
  · cases r <;> rfl
/-- `state_rel` does not read locals, so it survives `empty_locals` on both
    sides (the `state_rel` part of HOL's `rels_empty_tac`). -/
theorem panToCrepStateRelFiniteExact_emptyLocals {width : Nat} {σ : Type} [NeZero width]
    (st : PanSemStateFiniteExact width σ) (t1 : CrepSemHOLState width σ)
    (h : panToCrepStateRelFiniteExact st t1) :
    panToCrepStateRelFiniteExact (PanSemStateFiniteExact.emptyLocalsHOLFinite st)
      (CrepSemHOLState.emptyLocals t1) := by
  simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.emptyLocalsHOLFinite,
    CrepSemHOLState.emptyLocals] using h

/-- `code_rel` reads only `ctxt.funcs` and `ctxt.eids`, which `ctxt_fc` keeps, so
    a callee-context `code_rel` is the caller-context one (the `code_rel` part
    of HOL's `rels_empty_tac`). -/
theorem codeRelExactHOLW_ctxtFc {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat)
    (c1 : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (c2 : HolFiniteMapExact MlS (List Nat × CrepProgHOL width))
    (h : codeRelExactHOLW (ctxtFcExactHOL ctxt.funcs ctxt.eids vs shs ns) c1 c2) :
    codeRelExactHOLW ctxt c1 c2 := by
  simpa [codeRelExactHOLW, ctxtFcExactHOL] using h

/-- HOL `pc_compile_correct[Call_TailCall]`
    (`pan_to_crepProofScript.sml:3182-3230`) against `pcCompileCorrectAt`:
    `caltyp = NONE` with a positive source clock. The hypotheses are the Call
    IHs of the rebound `evaluate_ind` (only the callee IH is used here) and the
    positive-clock split of the HOL proof (`cases_on s.clock = 0`,
    `:3113`). The source Error/Break/Continue/no-result and failed-shape
    outcomes are excluded by `res ≠ SOME Error`. The remaining outcomes follow
    from the callee IH at the prelude's entry states, with `empty_locals` on
    both sides. No target run is assumed. Untagged: one sub-case of the Call
    case (bead `flapjack-pxn.18.4.3.94.6`). -/
theorem pcCompileCorrectAt_callTail {width : Nat} {σ : Type} [NeZero width]
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectCallIH none fname argexps source) (hclock : source.clock ≠ 0) :
    pcCompileCorrectAt (.call none fname argexps : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocArgs : everyExpListHOL localisedExpHOL argexps = true := by
    simpa [localisedProgHOL] using hloc
  rw [evaluateHOLFiniteState_call] at hrun
  cases hargs : source.evalListHOLFinite
      (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
      rw [hargs] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some args =>
      rw [hargs] at hrun
      dsimp only at hrun
      cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname args with
      | none =>
          rw [hlk] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | some triple =>
          obtain ⟨prog, newlocals, rsh⟩ := triple
          rw [hlk] at hrun
          dsimp only at hrun
          rw [if_neg hclock] at hrun
          obtain ⟨vshapes, _hsrc, hprogLoc, _hfuncs, _hlen, htargs, htlookup, hst', hcode',
            hexcp', hloc'⟩ :=
            pcCompileCorrectCallPrelude source t ctxt fname argexps args prog newlocals rsh
              hargs hlk hstate hcode hexcp hlocals hlocArgs
          have hih := ih.2 args prog newlocals rsh hargs hlk hclock
          have htclock : t.clock ≠ 0 := by
            rw [← hstate.2.2.2.2.2.1]; exact hclock
          have htarget := pcCompileCorrectCallNoReturnTarget t ctxt fname argexps _ _ _ htargs htlookup htclock
          rcases hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
              ).evaluateHOLFiniteState prog with ⟨bres, st⟩
          rw [hbody] at hrun
          have hIH := fun r (hr : some r ≠ some PanSemResultExact.error)
              (hb : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
                ).evaluateHOLFiniteState prog = (some r, st)) =>
            hih (some r) st _ _ hb hr hst' hcode' hexcp' hloc' hprogLoc
          rcases bres with _ | r
          · exact absurd (Prod.mk.inj hrun).1.symm hres
          · cases r with
            | error => exact absurd (Prod.mk.inj hrun).1.symm hres
            | «break» => exact absurd (Prod.mk.inj hrun).1.symm hres
            | «continue» => exact absurd (Prod.mk.inj hrun).1.symm hres
            | timeOut =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
                obtain ⟨res1, t1, hrun1, hs, hc, he, hr⟩ := hIH _ (by simp) hbody
                simp only [pcCompileCorrectResultRel] at hr
                subst hr
                refine ⟨_, _, by rw [htarget, hrun1], panToCrepStateRelFiniteExact_emptyLocals _ _ hs,
                  codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, rfl⟩
            | finalFfi f =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
                obtain ⟨res1, t1, hrun1, hs, hc, he, hr⟩ := hIH _ (by simp) hbody
                simp only [pcCompileCorrectResultRel] at hr
                subst hr
                refine ⟨_, _, by rw [htarget, hrun1], panToCrepStateRelFiniteExact_emptyLocals _ _ hs,
                  codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, rfl⟩
            | returned v =>
                dsimp only at hrun
                by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rsh = true
                · rw [if_pos hsh] at hrun
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
                  obtain ⟨res1, t1, hrun1, hs, hc, he, hr⟩ := hIH _ (by simp) hbody
                  simp only [pcCompileCorrectResultRel] at hr
                  subst hr
                  refine ⟨_, _, by rw [htarget, hrun1], panToCrepStateRelFiniteExact_emptyLocals _ _ hs,
                    codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, rfl⟩
                · rw [if_neg hsh] at hrun
                  exact absurd (Prod.mk.inj hrun).1.symm hres
            | exception eid v =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
                obtain ⟨res1, t1, hrun1, hs, hc, he, hr⟩ := hIH _ (by simp) hbody
                simp only [pcCompileCorrectResultRel, ctxtFcExactHOL] at hr
                cases hn : ctxt.eids.lookup eid with
                | none => rw [hn] at hr; exact hr.elim
                | some n =>
                    rw [hn] at hr
                    obtain ⟨rfl, hglob⟩ := hr
                    refine ⟨_, _, by rw [htarget, hrun1], panToCrepStateRelFiniteExact_emptyLocals _ _ hs,
                      codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc, he, ?_⟩
                    simp only [pcCompileCorrectResultRel, hn]
                    exact ⟨trivial, by simpa [globalsLookupHOL, CrepSemHOLState.emptyLocals] using hglob⟩

/-- The post-callee part of the tagged line-443 Crep Call clause
    (`crepSemScript.sml:335-366` after `fix_clock_evaluate`): what the caller does
    with the callee's `(res, st)`, given the caller state `t` and the call's
    return info. Flapjack infrastructure naming a sub-term of the tagged clause
    `evalCrepSemHOLProgExact_call_holShape`. -/
noncomputable def crepCallAfterBody {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width))) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ →
      Option (CrepResultHOLExact width) × CrepSemHOLState width σ
  | (none, st) => (some .error, st)
  | (some (.break _), st) => (some .error, st)
  | (some (.continue _), st) => (some .error, st)
  | (some (.return retvs), st) =>
      match returnInfo with
      | none => (some (.return retvs), CrepSemHOLState.emptyLocals st)
      | some (rts, _) =>
          if retvs.length ≠ rts.length then (some .error, st) else
          match rts.mapM t.locals.lookup with
          | some _ => (none, { st with locals := t.locals.updateListEq (rts.zip retvs) })
          | none => (some .error, st)
  | (some (.exception eid), st) =>
      match returnInfo with
      | none => (some (.exception eid), CrepSemHOLState.emptyLocals st)
      | some (_, none) => (some (.exception eid), CrepSemHOLState.emptyLocals st)
      | some (_, some (eid', p)) =>
          if eid = eid' then evalCrepSemHOLProgExact { st with locals := t.locals } p
          else (some (.exception eid), CrepSemHOLState.emptyLocals st)
  | (res, st) => (res, CrepSemHOLState.emptyLocals st)

/-- The target run of `Call ri fname cargs` from the tagged line-443 Crep Call
    clause: after a successful argument evaluation and `lookup_code`, a valid
    return-name guard, and a positive clock, it is `crepCallAfterBody` of the
    dec-clocked callee run. -/
theorem crepCallTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hguard : ∀ rts h, returnInfo = some (rts, h) → rts.Nodup)
    (hclock : t.clock ≠ 0) :
    evalCrepSemHOLProgExact t (.call returnInfo fname cargs) =
      crepCallAfterBody t returnInfo
        (evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body) := by
  classical
  rw [evalCrepSemHOLProgExact_call_holShape]
  change (match cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) with
    | some args => _ | none => _ : Option (CrepResultHOLExact width) × CrepSemHOLState width σ) = _
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_neg (by
    rcases returnInfo with _ | ⟨rts, h⟩
    · simp
    · simpa using hguard rts h rfl), if_neg hclock]
  rcases evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body with
    ⟨_ | r, st⟩
  · rfl
  · cases r <;> rfl
/-- The target run of a call wrapped in zero-initialised return slots,
    `nested_decs rts (REPLICATE (LENGTH rts) (Const 0w)) (Call ri fname cargs)`
    (the standalone and handler Ret arms of `compile_def`). By the tagged
    `eval_nested_decs_seq_res_var_eq` and `opt_mmap_eval_distinct_lists_not_affect`,
    it is the inner call's `crepCallAfterBody` on the slot-extended caller state,
    with the caller's slot bindings restored by `res_var`. -/
theorem crepNestedCallTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (rts : List Nat)
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hguard : ∀ rts' h, returnInfo = some (rts', h) → rts'.Nodup)
    (hclock : t.clock ≠ 0)
    (hnodup : rts.Nodup)
    (hdist : distinctListsHol rts (cargs.flatMap crepExpVarsHOL) = true) :
    evalCrepSemHOLProgExact t
        (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
          (.call returnInfo fname cargs)) =
      match crepCallAfterBody
          { t with locals := (t.locals.updateListEq
              (rts.zip (List.replicate rts.length (HolWordLab.word (0 : BitVec width))))) }
          returnInfo
          (evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body) with
      | (q, r) => (q, { r with locals :=
          ((rts.zip (rts.map t.locals.lookup)).foldl
            (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals) }) := by
  classical
  let zeros := List.replicate rts.length (HolWordLab.word (0 : BitVec width))
  let t' : CrepSemHOLState width σ := { t with locals := t.locals.updateListEq (rts.zip zeros) }
  have hnd := evalNestedDecsSeqResVarEqHOL
    (List.replicate rts.length (.const (0 : BitVec width))) rts t zeros
    (.call returnInfo fname cargs)
    ⟨by simp [zeros, evalCrepSemHOLExp], by simp, by
      simp [distinctListsHol, crepExpVarsHOL], hnodup⟩
  have hargs' : cargs.mapM (@evalCrepSemHOLExp width _ σ t'
      (fun address => Classical.propDecidable (t'.memaddrs address))) = some flat :=
    optMmapEvalDistinctListsNotAffectHOL cargs t flat rts zeros
      ⟨hargs, by simp [zeros], hdist⟩
  have hcall := crepCallTarget t' returnInfo fname cargs flat body locals hargs'
    hlookup hguard hclock
  have hentry : ({ decClockCrepSemHOL t' with locals := locals } : CrepSemHOLState width σ) =
      { decClockCrepSemHOL t with locals := locals } := rfl
  rw [hentry] at hcall
  rw [hcall] at hnd
  exact hnd

/-- Shape of `compile ctxt (Call (SOME (dest, hdl)) f args)`
    (`pan_to_crepScript.sml:221-261`) under `no_overlap ctxt.vars` and a context
    signature for `f`. It is a plain `Call ri f cargs` (the `wrap_rt` arms) or the
    same call wrapped in zero-initialised return slots `vmax + SUC x` (the
    standalone arms), and every return-name list in `ri` is distinct. -/
theorem compileCallSomeShape {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width))
    (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (hno : noOverlapFiniteExact ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh)) :
    let cargs := (compileExpExactHOLWList ctxt args).flatMap Prod.fst
    ∃ ri : Option (List Nat × Option (BitVec width × CrepProgHOL width)),
      (∀ rts h, ri = some (rts, h) → rts.Nodup) ∧
      (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) = .call ri f cargs ∨
        ∃ rts h, ri = some (rts, h) ∧
          rts = (List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1) ∧
          compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) =
            nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
              (.call ri f cargs)) := by
  intro cargs
  have hrtsNodup : ((List.range (sizeOfShapeHOL rsh)).map
      (fun i => ctxt.vmax + i + 1)).Nodup := by
    exact List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
  have hrts : ∀ (h : Option (BitVec width × CrepProgHOL width)) (rts : List Nat)
      (h' : Option (BitVec width × CrepProgHOL width)),
      some (((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)), h) =
        some (rts, h') → rts.Nodup := by
    intro h rts h' heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    rw [← heq.1]; exact hrtsNodup
  rcases dest with _ | ⟨kind, name⟩ <;> rcases hdl with _ | ⟨eid, evar, p⟩ <;>
    simp only [compileProgExactHOLW]
  · refine ⟨_, hrts none, Or.inr ⟨_, none, rfl, rfl, ?_⟩⟩
    simp [compileCallResultNoHandlerExactHOLW, hfuncs, cargs]
  · split
    · refine ⟨_, hrts none, Or.inr ⟨_, none, rfl, rfl, ?_⟩⟩
      simp [compileCallHandlerMissingEidExactHOLW, compileCallResultNoHandlerExactHOLW,
        hfuncs, cargs]
    · rename_i code _
      refine ⟨_, hrts (some (code, CrepProgHOL.seq (expHdlExact ctxt.vars evar)
        (compileProgExactHOLW ctxt p))), Or.inr ⟨_, _, rfl, rfl, ?_⟩⟩
      simp [compileCallHandlerPresentEidExactHOLW, hfuncs, cargs]
  · split
    · exact ⟨none, by simp, Or.inl (by simp [compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs])⟩
    · rename_i sh ns hwrap
      refine ⟨some (ns, none), ?_, Or.inl (by simp [compileCallWrappedResultNoHandlerExactHOLW, cargs])⟩
      intro rts h heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rw [← heq.1]
      exact noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns hno hwrap
  · split
    · split
      · exact ⟨none, by simp, Or.inl (by
          simp [compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
            compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs])⟩
      · refine ⟨_, ?_, Or.inl (by
          simp [compileCallWrappedResultFallbackHandlerPresentEidExactHOLW, cargs]; rfl)⟩
        intro rts h heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rw [← heq.1]; exact List.nodup_nil
    · rename_i sh ns hwrap
      have hns := noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns hno hwrap
      split
      · refine ⟨some (ns, none), ?_, Or.inl (by
          simp [compileCallWrappedResultHandlerMissingEidExactHOLW,
            compileCallWrappedResultNoHandlerExactHOLW, cargs])⟩
        intro rts h heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rw [← heq.1]; exact hns
      · refine ⟨_, ?_, Or.inl (by
          simp [compileCallWrappedResultHandlerPresentEidExactHOLW, cargs]; rfl)⟩
        intro rts h heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rw [← heq.1]; exact hns

/-- The zero-initialised return slots `GENLIST (λx. ctxt.vmax + SUC x) n` are
    disjoint from the variables of the compiled arguments, which are bounded by
    `vmax` under `ctxt_max` (HOL `mem_genlist_add_suc_val`/`MEM_compile_exp_vmax`,
    used inline at `pan_to_crepProofScript.sml:3259-3275`). -/
theorem pcCompileCorrectCallRetSlotsDistinct {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (args : List (ExpHOL width)) (n : Nat)
    (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars) :
    distinctListsHol ((List.range n).map (fun i => ctxt.vmax + i + 1))
      (((compileExpExactHOLWList ctxt args).flatMap Prod.fst).flatMap crepExpVarsHOL) = true := by
  simp only [distinctListsHol, List.all_eq_true, decide_eq_true_eq, List.mem_map, List.mem_range]
  rintro _ ⟨i, _, rfl⟩ hmem
  obtain ⟨src, sh, slots, hlk, hslot⟩ := (compileExpExactHOLW_vars_from_context ctxt).2 args _ hmem
  have := hmax.2 src sh slots hlk _ hslot
  omega

/-- For `Call (SOME (dest, hdl))`, if the callee's target run ends in a terminal
    outcome `r` that the caller propagates with `empty_locals` (TimeOut,
    FinalFFI), every compiled Ret arm returns `r`, in a state that agrees with
    the callee's post-state except for locals. -/
theorem pcCompileCorrectCallRetTerminalTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (r : CrepResultHOLExact width) (t1 : CrepSemHOLState width σ)
    (hno : noOverlapFiniteExact ctxt.vars) (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh))
    (hargs : ((compileExpExactHOLWList ctxt args).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code f flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hcallee : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
      (some r, t1))
    (hterm : ∀ (tt : CrepSemHOLState width σ) ri,
      crepCallAfterBody tt ri (some r, t1) = (some r, CrepSemHOLState.emptyLocals t1)) :
    ∃ t2, evalCrepSemHOLProgExact t
        (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args)) = (some r, t2) ∧
      { t2 with locals := t1.locals } = t1 := by
  obtain ⟨ri, hg, hshape⟩ := compileCallSomeShape ctxt dest hdl f args vshapes rsh hno hfuncs
  rcases hshape with h | ⟨rts, h', hri, hrtsEq, h⟩
  · rw [h, crepCallTarget t ri f _ flat body locals hargs hlookup hg hclock, hcallee, hterm]
    exact ⟨_, rfl, rfl⟩
  · have hnodup : rts.Nodup := hg rts h' hri
    have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt args (sizeOfShapeHOL rsh) hmax
    rw [← hrtsEq] at hdist
    rw [h, crepNestedCallTarget t ri f _ flat body locals rts hargs hlookup hg hclock hnodup hdist,
      hcallee, hterm]
    exact ⟨_, rfl, rfl⟩
/-- `state_rel` ignores locals, so it transfers to a target state that differs
    only in locals. -/
theorem panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals {width : Nat} {σ : Type} [NeZero width]
    (st : PanSemStateFiniteExact width σ) (t1 t2 : CrepSemHOLState width σ)
    (h : { t2 with locals := t1.locals } = t1) (hs : panToCrepStateRelFiniteExact st t1) :
    panToCrepStateRelFiniteExact (PanSemStateFiniteExact.emptyLocalsHOLFinite st) t2 := by
  rw [← h] at hs
  simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hs

/-- HOL `pc_compile_correct[Call_Ret_TimeOut]` and `[Call_Ret_FinalFFI]`
    (`pan_to_crepProofScript.sml:3232-3310, 3918-4231`) against
    `pcCompileCorrectAt`: `caltyp = SOME (dest, hdl)` with a positive clock, where
    the callee's source run on `dec_clock s with locals := newlocals` gives
    TimeOut or FinalFFI. These are the sub-case hypotheses of HOL's case split.
    The callee IH at the prelude's entry states yields the matching target
    outcome. Every compiled arm (standalone `nested_decs` return slots, `wrap_rt`
    destinations, with or without a handler) propagates it, with state/code/excp
    relations through `empty_locals`. No target run is assumed. Untagged (beads
    `flapjack-pxn.18.4.3.94.7`, `.94.10`). -/
theorem pcCompileCorrectAt_callRetTerminal {width : Nat} {σ : Type} [NeZero width]
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectCallIH (some (dest, hdl)) fname argexps source)
    (hclock : source.clock ≠ 0)
    (values : List (ValueHOL width)) (prog : ProgHOL width)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (st : PanSemStateFiniteExact width σ) (r : PanSemResultExact width)
    (hargs : source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        argexps = some values)
    (hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values =
      some (prog, newlocals, rsh))
    (hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
      ).evaluateHOLFiniteState prog = (some r, st))
    (hr : r = .timeOut ∨ ∃ ev, r = .finalFfi ev) :
    pcCompileCorrectAt (.call (some (dest, hdl)) fname argexps : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocArgs : everyExpListHOL localisedExpHOL argexps = true := by
    rcases dest with _ | ⟨k, n⟩ <;> rcases hdl with _ | ⟨a, b, c⟩ <;> (try rcases k) <;>
      simp_all [localisedProgHOL]
  rw [evaluateHOLFiniteState_call, hargs] at hrun
  dsimp only at hrun
  rw [hlk] at hrun
  dsimp only at hrun
  rw [if_neg hclock, hbody] at hrun
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode',
    hexcp', hloc'⟩ :=
    pcCompileCorrectCallPrelude source t ctxt fname argexps values prog newlocals rsh
      hargs hlk hstate hcode hexcp hlocals hlocArgs
  have htclock : t.clock ≠ 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
  rcases hr with rfl | ⟨ev, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
      ih.2 values prog newlocals rsh hargs hlk hclock (some .timeOut) st _ _ hbody (by simp)
        hst' hcode' hexcp' hloc' hprogLoc
    simp only [pcCompileCorrectResultRel] at hrr
    subst hrr
    obtain ⟨t2, hrun2, hsame⟩ := pcCompileCorrectCallRetTerminalTarget t ctxt dest hdl fname argexps vshapes rsh _ _ _
      .timeOut t1 hlocals.1 hlocals.2.1 hfuncs htargs htlookup htclock hrun1
      (fun _ _ => rfl)
    refine ⟨_, t2, hrun2, panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 t2 hsame hs, ?_, he, rfl⟩
    have hcode2 : t2.code = t1.code := by rw [← hsame]
    rw [hcode2]
    exact codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
      ih.2 values prog newlocals rsh hargs hlk hclock (some (.finalFfi ev)) st _ _ hbody (by simp)
        hst' hcode' hexcp' hloc' hprogLoc
    simp only [pcCompileCorrectResultRel] at hrr
    subst hrr
    obtain ⟨t2, hrun2, hsame⟩ := pcCompileCorrectCallRetTerminalTarget t ctxt dest hdl fname argexps vshapes rsh _ _ _
      (.finalFfi ev) t1 hlocals.1 hlocals.2.1 hfuncs htargs htlookup htclock hrun1
      (fun _ _ => rfl)
    refine ⟨_, t2, hrun2, panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 t2 hsame hs, ?_, he, rfl⟩
    have hcode2 : t2.code = t1.code := by rw [← hsame]
    rw [hcode2]
    exact codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc

/-- A Crep call with a zero clock (after successful argument evaluation,
    `lookup_code`, and a valid return-name guard) times out with empty locals
    (tagged line-443 Crep Call clause). -/
theorem crepCallTimeout {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hguard : ∀ rts h, returnInfo = some (rts, h) → rts.Nodup)
    (hclock : t.clock = 0) :
    evalCrepSemHOLProgExact t (.call returnInfo fname cargs) =
      (some .timeOut, CrepSemHOLState.emptyLocals t) := by
  classical
  rw [evalCrepSemHOLProgExact_call_holShape]
  change (match cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) with
    | some args => _ | none => _ : Option (CrepResultHOLExact width) × CrepSemHOLState width σ) = _
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  rw [if_neg (by
    rcases returnInfo with _ | ⟨rts, h⟩
    · simp
    · simpa using hguard rts h rfl), if_pos hclock]

/-- The zero-clock target run of a call wrapped in zero-initialised return slots:
    it times out, in a state that differs from the caller's only in locals. -/
theorem crepNestedCallTimeout {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ)
    (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlS) (cargs : List (CrepExpHOL width)) (flat : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (rts : List Nat)
    (hargs : cargs.mapM (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code fname flat flat.length = some (body, locals))
    (hguard : ∀ rts' h, returnInfo = some (rts', h) → rts'.Nodup)
    (hclock : t.clock = 0)
    (hnodup : rts.Nodup)
    (hdist : distinctListsHol rts (cargs.flatMap crepExpVarsHOL) = true) :
    ∃ t2, evalCrepSemHOLProgExact t
        (nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
          (.call returnInfo fname cargs)) = (some .timeOut, t2) ∧
      { t2 with locals := t.locals } = t := by
  classical
  let zeros := List.replicate rts.length (HolWordLab.word (0 : BitVec width))
  let t' : CrepSemHOLState width σ := { t with locals := t.locals.updateListEq (rts.zip zeros) }
  have hnd := evalNestedDecsSeqResVarEqHOL
    (List.replicate rts.length (.const (0 : BitVec width))) rts t zeros
    (.call returnInfo fname cargs)
    ⟨by simp [zeros, evalCrepSemHOLExp], by simp, by
      simp [distinctListsHol, crepExpVarsHOL], hnodup⟩
  have hargs' : cargs.mapM (@evalCrepSemHOLExp width _ σ t'
      (fun address => Classical.propDecidable (t'.memaddrs address))) = some flat :=
    optMmapEvalDistinctListsNotAffectHOL cargs t flat rts zeros
      ⟨hargs, by simp [zeros], hdist⟩
  have hcall := crepCallTimeout t' returnInfo fname cargs flat body locals hargs'
    hlookup hguard hclock
  rw [hcall] at hnd
  exact ⟨_, hnd, rfl⟩
/-- The zero-clock branch of HOL `pc_compile_correct[Call]`
    (`pan_to_crepProofScript.sml:3113-3165`, `cases_on s.clock = 0`) against
    `pcCompileCorrectAt`, for every `caltyp`. The source run times out with
    `empty_locals`. Every compiled arm (tail, `wrap_rt`, and standalone
    `nested_decs` return slots) times out in the target, and the
    state/code/excp relations transfer. HOL needs no IH for this branch, and none
    is taken; no target run is assumed. Untagged (bead
    `flapjack-pxn.18.4.3.94.5`). -/
theorem pcCompileCorrectAt_callZeroClock {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (hclock : source.clock = 0) :
    pcCompileCorrectAt (.call info fname argexps : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocArgs : everyExpListHOL localisedExpHOL argexps = true := by
    rcases info with _ | ⟨dest, hdl⟩
    · simpa [localisedProgHOL] using hloc
    · rcases dest with _ | ⟨k, n⟩ <;> rcases hdl with _ | ⟨a, b, c⟩ <;> (try rcases k) <;>
        simp_all [localisedProgHOL]
  rw [evaluateHOLFiniteState_call] at hrun
  cases hargs : source.evalListHOLFinite
      (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
      rw [hargs] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some values =>
      rw [hargs] at hrun
      dsimp only at hrun
      cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values with
      | none =>
          rw [hlk] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | some triple =>
          obtain ⟨prog, newlocals, rsh⟩ := triple
          rw [hlk] at hrun
          dsimp only at hrun
          rw [if_pos hclock] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          obtain ⟨vshapes, _hsrc, _hprogLoc, hfuncs, _hlen, htargs, htlookup, _⟩ :=
            pcCompileCorrectCallPrelude source t ctxt fname argexps values prog newlocals rsh
              hargs hlk hstate hcode hexcp hlocals hlocArgs
          have htclock : t.clock = 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
          have hstEmpty := panToCrepStateRelFiniteExact_emptyLocals source t hstate
          suffices h : ∃ t2, evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt
              (.call info fname argexps)) = (some .timeOut, t2) ∧
              { t2 with locals := t.locals } = t by
            obtain ⟨t2, hrun2, hsame⟩ := h
            refine ⟨_, t2, hrun2, ?_, ?_, hexcp, rfl⟩
            · exact panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals source t t2
                hsame hstate
            · have hcode2 : t2.code = t.code := by rw [← hsame]
              rw [hcode2]; exact hcode
          rcases info with _ | ⟨dest, hdl⟩
          · refine ⟨CrepSemHOLState.emptyLocals t, ?_, rfl⟩
            simp only [compileProgExactHOLW, compileCallNoReturnExactHOLW]
            exact crepCallTimeout t none fname _ _ _ _ htargs htlookup (by simp) htclock
          · obtain ⟨ri, hg, hshape⟩ := compileCallSomeShape ctxt dest hdl fname argexps vshapes rsh
              hlocals.1 hfuncs
            rcases hshape with h | ⟨rts, h', hri, hrtsEq, h⟩
            · rw [h]
              exact ⟨_, crepCallTimeout t ri fname _ _ _ _ htargs htlookup hg htclock, rfl⟩
            · have hnodup : rts.Nodup := hg rts h' hri
              have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt argexps (sizeOfShapeHOL rsh)
                hlocals.2.1
              rw [← hrtsEq] at hdist
              rw [h]
              exact crepNestedCallTimeout t ri fname _ _ _ _ rts htargs htlookup hg htclock
                hnodup hdist

/-- `compile ctxt (Call (SOME (NONE, hdl)) f args)` is always the standalone arm
    (`pan_to_crepScript.sml:224-239`): the call wrapped in zero-initialised return
    slots `GENLIST (λx. ctxt.vmax + SUC x) (size_of_shape rshape)`, where `rshape`
    is `f`'s context return shape. -/
theorem compileCallDestNoneShape {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (hdl : Option (MlS × MlS × ProgHOL width)) (f : MlS) (args : List (ExpHOL width))
    (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh)) :
    ∃ H, compileProgExactHOLW ctxt (.call (some (none, hdl)) f args) =
      nestedDecsHOL ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1))
        (List.replicate ((List.range (sizeOfShapeHOL rsh)).map
          (fun i => ctxt.vmax + i + 1)).length (.const (0 : BitVec width)))
        (.call (some ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1), H)) f
          ((compileExpExactHOLWList ctxt args).flatMap Prod.fst)) := by
  rcases hdl with _ | ⟨eid, evar, p⟩ <;> simp only [compileProgExactHOLW]
  · exact ⟨none, by simp [compileCallResultNoHandlerExactHOLW, hfuncs]⟩
  · split
    · exact ⟨none, by simp [compileCallHandlerMissingEidExactHOLW,
        compileCallResultNoHandlerExactHOLW, hfuncs]⟩
    · rename_i code _
      exact ⟨some (code, CrepProgHOL.seq (expHdlExact ctxt.vars evar)
        (compileProgExactHOLW ctxt p)), by simp [compileCallHandlerPresentEidExactHOLW, hfuncs]⟩

/-- For a `wrap_rt (FLOOKUP ctxt.vars rt) = SOME (sh, ns)` destination,
    `compile ctxt (Call (SOME (SOME (rk, rt), hdl)) f args)` is a plain call with
    return names `ns` (`pan_to_crepScript.sml:252-261`). -/
theorem compileCallDestSomeShape {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (kind : VarKind) (name : MlS) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (sh : ShapeHOL) (ns : List Nat)
    (hwrap : wrapRtHOL (ctxt.vars.lookup name) = some (sh, ns)) :
    ∃ H, compileProgExactHOLW ctxt (.call (some (some (kind, name), hdl)) f args) =
      .call (some (ns, H)) f ((compileExpExactHOLWList ctxt args).flatMap Prod.fst) := by
  rcases hdl with _ | ⟨eid, evar, p⟩ <;> simp only [compileProgExactHOLW]
  · split
    · rename_i h; rw [hwrap] at h; simp at h
    · rename_i sh' ns' hw
      rw [hwrap] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨none, by simp [compileCallWrappedResultNoHandlerExactHOLW]⟩
  · split
    · rename_i h; rw [hwrap] at h; simp at h
    · rename_i sh' ns' hw
      rw [hwrap] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      split
      · exact ⟨none, by simp [compileCallWrappedResultHandlerMissingEidExactHOLW,
          compileCallWrappedResultNoHandlerExactHOLW]⟩
      · rename_i code _
        exact ⟨some (code, CrepProgHOL.seq (expHdlExact ctxt.vars evar)
          (compileProgExactHOLW ctxt p)), by
            simp [compileCallWrappedResultHandlerPresentEidExactHOLW]⟩
private theorem fupdateListHOL_zip_mem_indep {α β : Type} [DecidableEq α] (k : α) :
    ∀ (xs : List α) (ys : List β) (f g : FiniteMap α β), k ∈ xs → xs.length = ys.length →
      FUPDATE_LIST_HOL f (xs.zip ys) k = FUPDATE_LIST_HOL g (xs.zip ys) k
  | [], _, _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, _, hlen => by simp at hlen
  | x :: xs, y :: ys, f, g, hk, hlen => by
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
      by_cases hkxs : k ∈ xs
      · exact fupdateListHOL_zip_mem_indep k xs ys _ _ hkxs (by simpa using hlen)
      · have hkx : k = x := by simpa [hkxs] using hk
        rw [fupdateListHOL_zip_not_mem_local k xs ys _ hkxs,
          fupdateListHOL_zip_not_mem_local k xs ys _ hkxs]
        simp [FUPDATE_HOL, hkx]
where
  fupdateListHOL_zip_not_mem_local (k : α) :
      ∀ (xs : List α) (ys : List β) (f : FiniteMap α β), k ∉ xs →
        FUPDATE_LIST_HOL f (xs.zip ys) k = f k
    | [], _, f, _ => by simp [FUPDATE_LIST_HOL]
    | _ :: _, [], f, _ => by simp [FUPDATE_LIST_HOL]
    | x :: xs, y :: ys, f, hk => by
        simp only [List.mem_cons, not_or] at hk
        rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons,
          fupdateListHOL_zip_not_mem_local k xs ys _ hk.2]
        simp [FUPDATE_HOL, hk.1]

theorem updateListEq_overwrite {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (xs : List α) (ys1 ys2 : List β)
    (_h1 : xs.length = ys1.length) (h2 : xs.length = ys2.length) :
    (m.updateListEq (xs.zip ys1)).updateListEq (xs.zip ys2) = m.updateListEq (xs.zip ys2) := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateListEq]
  by_cases hk : k ∈ xs
  · exact fupdateListHOL_zip_mem_indep k xs ys2 _ _ hk h2
  · rw [fupdateListHOL_zip_mem_indep.fupdateListHOL_zip_not_mem_local k xs ys2 _ hk,
      fupdateListHOL_zip_mem_indep.fupdateListHOL_zip_not_mem_local k xs ys2 _ hk]
    simp only [HolFiniteMapExact.lookup_updateListEq]
    rw [fupdateListHOL_zip_mem_indep.fupdateListHOL_zip_not_mem_local k xs ys1 _ hk]

theorem mapM_lookup_updateListEq {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (xs : List α) (ys : List β)
    (hnodup : xs.Nodup) (hlen : xs.length = ys.length) :
    xs.mapM (m.updateListEq (xs.zip ys)).lookup = some ys := by
  have hfun : (m.updateListEq (xs.zip ys)).lookup =
      fun key => FLOOKUP (FUPDATE_LIST m.lookup (xs.zip ys)) key := by
    funext key
    simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_eq_FUPDATE_LIST, FLOOKUP]
  rw [hfun]
  exact optMmapSomeEqZipFlookup xs m.lookup ys hnodup hlen

/-- Target run of the standalone Ret arm when the callee returns `retvs` of the
    context return size. The values are installed into the fresh slots, and the
    `nested_decs` restoration (`res_var_lookup_original_eq`) gives back exactly the
    caller's locals. -/
theorem pcCompileCorrectCallRetReturnTargetNested {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (retvs : List (HolWordLab width)) (t1 : CrepSemHOLState width σ)
    (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh))
    (hargs : ((compileExpExactHOLWList ctxt args).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code f flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hcallee : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
      (some (.return retvs), t1))
    (hlen : retvs.length = sizeOfShapeHOL rsh) :
    evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.call (some (none, hdl)) f args)) =
      (none, { t1 with locals := t.locals }) := by
  classical
  obtain ⟨H, hc⟩ := compileCallDestNoneShape ctxt hdl f args vshapes rsh hfuncs
  have hnodup0 : ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)).Nodup :=
    List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
  have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt args (sizeOfShapeHOL rsh) hmax
  have hrtsLen0 : ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)).length =
      sizeOfShapeHOL rsh := by simp
  generalize ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)) = rts
    at hc hnodup0 hdist hrtsLen0
  have hnodup := hnodup0
  have hrtsLen := hrtsLen0
  have hg : ∀ rts' h, (some (rts, H) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) =
      some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact hnodup
  rw [hc, crepNestedCallTarget t _ f _ flat body locals rts hargs hlookup hg hclock hnodup hdist,
    hcallee]
  have hzlen : rts.length = (List.replicate rts.length (HolWordLab.word (0 : BitVec width))).length :=
    by simp
  simp only [crepCallAfterBody]
  rw [if_neg (by rw [hlen, hrtsLen]; exact fun h => h rfl)]
  rw [mapM_lookup_updateListEq _ rts _ hnodup hzlen]
  dsimp only
  rw [updateListEq_overwrite t.locals rts _ retvs hzlen (by rw [hlen, hrtsLen]),
    resVarLookupOriginalEqHOL rts retvs t.locals ⟨hnodup, by rw [hlen, hrtsLen]⟩]

/-- Target run of a `wrap_rt` destination arm when the callee returns `retvs`
    matching the destination slots: normal completion with the slots updated to
    `retvs`. -/
theorem pcCompileCorrectCallRetReturnTargetWrap {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (kind : VarKind) (name : MlS) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (sh : ShapeHOL) (ns : List Nat)
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (retvs : List (HolWordLab width)) (t1 : CrepSemHOLState width σ) (ws : List (HolWordLab width))
    (hno : noOverlapFiniteExact ctxt.vars)
    (hwrap : wrapRtHOL (ctxt.vars.lookup name) = some (sh, ns))
    (hargs : ((compileExpExactHOLWList ctxt args).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code f flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hcallee : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
      (some (.return retvs), t1))
    (hlen : retvs.length = ns.length)
    (hns : ns.mapM t.locals.lookup = some ws) :
    evalCrepSemHOLProgExact t
        (compileProgExactHOLW ctxt (.call (some (some (kind, name), hdl)) f args)) =
      (none, { t1 with locals := t.locals.updateListEq (ns.zip retvs) }) := by
  classical
  obtain ⟨H, hc⟩ := compileCallDestSomeShape ctxt kind name hdl f args sh ns hwrap
  have hnodup := noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns hno hwrap
  have hg : ∀ rts' h, (some (ns, H) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) =
      some (rts', h) → rts'.Nodup := by
    intro rts' h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact hnodup
  rw [hc, crepCallTarget t _ f _ flat body locals hargs hlookup hg hclock, hcallee]
  simp only [crepCallAfterBody]
  rw [if_neg (by rw [hlen]; exact fun h => h rfl), hns]
/-- `locals_rel` survives writing a same-shaped value `v` to a source local whose
    context slots are `ns`, together with `ns := flatten v` on the target. This is
    the relation reasoning of HOL's `ret_call_shape_retv_*_tac`
    (`pan_to_crepProofScript.sml:2571-2780`, via `opt_mmap_some_eq_zip_flookup`,
    `opt_mmap_disj_zip_flookup`, and `no_overlap`). -/
theorem panToCrepLocalsRelFiniteExact_setVar {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width)
    (sl : HolFiniteMapExact MlS (ValueHOL width))
    (tl : HolFiniteMapExact Nat (HolWordLab width))
    (name : MlS) (v : ValueHOL width) (ns : List Nat)
    (hrel : panToCrepLocalsRelFiniteExact ctxt sl tl)
    (hvar : ctxt.vars.lookup name = some (shapeOfHOLExact v, ns))
    (hlen : ns.length = (flattenHOL v).length)
    (hwf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true) :
    panToCrepLocalsRelFiniteExact ctxt (sl.updateEq (name, v))
      (tl.updateListEq (ns.zip (flattenHOL v))) := by
  obtain ⟨hno, hmax, hlk⟩ := hrel
  have hlookupEq : ∀ k, (tl.updateListEq (ns.zip (flattenHOL v))).lookup k =
      FUPDATE_LIST tl.lookup (ns.zip (flattenHOL v)) k := by
    intro k
    simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  have hfun : (tl.updateListEq (ns.zip (flattenHOL v))).lookup =
      fun key => FLOOKUP (FUPDATE_LIST tl.lookup (ns.zip (flattenHOL v))) key :=
    funext (fun key => by rw [hlookupEq]; rfl)
  refine ⟨hno, hmax, ?_⟩
  intro k w hk
  by_cases hkn : k = name
  · subst hkn
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at hk
    subst hk
    refine ⟨ns, flattenHOL v, hvar, ?_, rfl, hwf⟩
    rw [hfun]
    exact optMmapSomeEqZipFlookup ns tl.lookup (flattenHOL v) (hno.1 _ _ _ hvar) hlen
  · have hk' : sl.lookup k = some w := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hkn] using hk
    obtain ⟨slots, words, hvk, hmm, hfl, hwfk⟩ := hlk k w hk'
    refine ⟨slots, words, hvk, ?_, hfl, hwfk⟩
    have hdisj : ListDisjoint ns slots := by
      intro x hx hy
      exact hkn (hno.2 k name _ _ slots ns hvk hvar ⟨x, hy, hx⟩)
    have := optMmapDisjZipFlookup ns tl.lookup slots (flattenHOL v) hdisj hlen
    rw [hfun, this]
    simpa [FLOOKUP] using hmm

/-- HOL `pc_compile_correct[Call_Ret_Return]` (`pan_to_crepProofScript.sml:3312-3597`)
    against `pcCompileCorrectAt`: `caltyp = SOME (dest, hdl)` with a positive
    clock, where the callee's source run returns `v`. These are the sub-case
    hypotheses of HOL's case split. A wrong return shape or an invalid
    destination is a source Error, excluded by `res ≠ SOME Error`. With no
    destination, the standalone arm restores the caller's locals. With a `Local`
    destination, the `wrap_rt` slots receive `flatten v` and `locals_rel` is
    re-established for the updated source local. Global destinations are
    excluded by `localised_prog`. No target run is assumed. Untagged (bead
    `flapjack-pxn.18.4.3.94.8`). -/
theorem pcCompileCorrectAt_callRetReturn {width : Nat} {σ : Type} [NeZero width]
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectCallIH (some (dest, hdl)) fname argexps source)
    (hclock : source.clock ≠ 0)
    (values : List (ValueHOL width)) (prog : ProgHOL width)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (st : PanSemStateFiniteExact width σ) (v : ValueHOL width)
    (hargs : source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        argexps = some values)
    (hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values =
      some (prog, newlocals, rsh))
    (hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
      ).evaluateHOLFiniteState prog = (some (.returned v), st)) :
    pcCompileCorrectAt (.call (some (dest, hdl)) fname argexps : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocArgs : everyExpListHOL localisedExpHOL argexps = true := by
    rcases dest with _ | ⟨k, n⟩ <;> rcases hdl with _ | ⟨a, b, c⟩ <;> (try rcases k) <;>
      simp_all [localisedProgHOL]
  rw [evaluateHOLFiniteState_call, hargs] at hrun
  dsimp only at hrun
  rw [hlk] at hrun
  dsimp only at hrun
  rw [if_neg hclock, hbody] at hrun
  dsimp only at hrun
  by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rsh = true
  case neg =>
    rw [if_neg hsh] at hrun
    exact absurd (Prod.mk.inj hrun).1.symm hres
  rw [if_pos hsh] at hrun
  have hshape : shapeOfHOLExact v = rsh := (shapeEqHOL_eq_true _ _).mp hsh
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode',
    hexcp', hloc'⟩ :=
    pcCompileCorrectCallPrelude source t ctxt fname argexps values prog newlocals rsh
      hargs hlk hstate hcode hexcp hlocals hlocArgs
  have htclock : t.clock ≠ 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
  obtain ⟨res1, t1, hrun1, hs, hc, he, hrr⟩ :=
    ih.2 values prog newlocals rsh hargs hlk hclock (some (.returned v)) st _ _ hbody (by simp)
      hst' hcode' hexcp' hloc' hprogLoc
  simp only [pcCompileCorrectResultRel] at hrr
  subst hrr
  have hwfv : isWfShapeValueHOLExact [] v = true := by
    have := panToCrepFiniteEvaluateShapeInvariantRetInst2 argexps source fname values prog newlocals
      rsh prog (.returned v) st t ctxt t.locals
      (by simpa [evalListHOLFiniteClassical] using hargs)
      (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hlk) hbody hstate hlocals
    simpa using this
  have hwf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact v) = true := by
    rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl v]; exact hwfv
  have hflen : (flattenHOL v).length = sizeOfShapeHOL (shapeOfHOLExact v) :=
    flattenHOL_length_eq_sizeOfShapeHOL v hwf
  rcases dest with _ | ⟨kind, name⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    have htgt := pcCompileCorrectCallRetReturnTargetNested t ctxt hdl fname argexps vshapes rsh _ _ _ _ t1
      hlocals.2.1 hfuncs htargs htlookup htclock hrun1 (by rw [hflen, hshape])
    refine ⟨none, _, htgt, ?_, ?_, he, rfl, hlocals⟩
    · simpa [panToCrepStateRelFiniteExact] using hs
    · exact codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc
  · cases kind with
    | global =>
        rcases hdl with _ | ⟨a, b, c⟩ <;> simp [localisedProgHOL] at hloc
    | «local» =>
        dsimp only at hrun
        by_cases hvalid : isValidValueHOLExact source.toExact .local name v = true
        case neg =>
          rw [if_neg hvalid] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
        rw [if_pos hvalid] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        cases hold : source.locals.lookup name with
        | none =>
            simp [isValidValueHOLExact, lookupKvarHOLExact, hold] at hvalid
        | some old =>
            have hse : shapeOfHOLExact v = shapeOfHOLExact old := by
              have : shapeEqHOL (shapeOfHOLExact v) (shapeOfHOLExact old) = true := by
                simpa [isValidValueHOLExact, lookupKvarHOLExact, PanSemStateFiniteExact.toExact,
                  hold] using hvalid
              exact (shapeEqHOL_eq_true _ _).mp this
            obtain ⟨ns, words, hvar, hmm, hfl, hwfo⟩ := hlocals.2.2 name old hold
            have hnslen : ns.length = (flattenHOL old).length := by
              rw [opt_mmap_length_eq _ _ _ hmm, ← hfl]
            have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
            have hwrap : wrapRtHOL (ctxt.vars.lookup name) = some (shapeOfHOLExact old, ns) := by
              rw [hvar]
              have hne : ¬ (shapeOfHOLExact old = .one ∧ ns = []) := by
                rintro ⟨h1, rfl⟩
                rw [h1] at hflo
                simp [sizeOfShapeHOL] at hflo
                simp [hflo] at hnslen
              unfold wrapRtHOL
              split
              · rename_i h; simp at h
              · rename_i h; simp only [Option.some.injEq, Prod.mk.injEq] at h
                exact absurd ⟨h.1, h.2⟩ hne
              · rfl
            have hlenv : (flattenHOL v).length = ns.length := by
              rw [hflen, hse, ← hflo, hnslen]
            have htgt := pcCompileCorrectCallRetReturnTargetWrap t ctxt .local name hdl fname argexps
              (shapeOfHOLExact old) ns _ _ _ (flattenHOL v) t1 words hlocals.1 hwrap htargs
              htlookup htclock hrun1 hlenv hmm
            refine ⟨none, _, htgt, ?_, ?_, he, rfl, ?_⟩
            · simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setKvarHOLFinite,
                PanSemStateFiniteExact.setVarHOLFinite] using hs
            · exact codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc
            · have hvar' : ctxt.vars.lookup name = some (shapeOfHOLExact v, ns) := by
                rw [hvar, hse]
              have hlr := panToCrepLocalsRelFiniteExact_setVar ctxt source.locals t.locals name v ns hlocals hvar'
                hlenv.symm hwf
              have hupd : source.locals.update (name, v) = source.locals.updateEq (name, v) := by
                apply HolFiniteMapExact.ext
                funext k
                simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
                  FUPDATE_HOL_eq_FUPDATE]
              simpa [PanSemStateFiniteExact.setKvarHOLFinite, PanSemStateFiniteExact.setVarHOLFinite,
                hupd] using hlr

/-- The Crep evaluation of `nested_seq (MAP2 Assign ns (load_globals a (LENGTH ns)))`
    (the body of `exp_hdl`) with distinct present destinations and loaded globals
    `ws`: normal completion with `ns` bound to `ws`. HOL uses the crepProps
    theorem `evaluate_seq_assign_load_globals` inline; this form takes the loaded
    values from a successful `OPT_MMAP` over the addresses instead of `THE`, so it
    is untagged. -/
theorem crepEvalAssignLoadGlobals {width : Nat} [NeZero width] {σ : Type} :
    ∀ (ns : List Nat) (t : CrepSemHOLState width σ) (a : BitVec 5) (ws : List (HolWordLab width)),
      ns.Nodup →
      (∀ n, n ∈ ns → t.locals.lookup n ≠ none) →
      ((List.range ns.length).map (fun i => a + BitVec.ofNat 5 i)).mapM t.globals.lookup = some ws →
      evalCrepSemHOLProgExact t
          (crepNestedSeqHOL (panMap2 (fun destination source => .assign destination source)
            ns (loadGlobalsHOL a ns.length))) =
        (none, { t with locals := t.locals.updateListEq (ns.zip ws) })
  | [], t, a, ws, _, _, hws => by
      simp at hws; subst hws
      simp only [panMap2, crepNestedSeqHOL]
      rw [evalCrepSemHOLProgExact_skip]
      congr 1
  | n :: ns, t, a, ws, hnd, hloc, hws => by
      classical
      have haddr : (List.range (n :: ns).length).map (fun i => a + BitVec.ofNat 5 i) =
          a :: (List.range ns.length).map (fun i => (a + 1) + BitVec.ofNat 5 i) := by
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1
        · simp
        · congr 1
          funext i
          simp only [Function.comp, Nat.succ_eq_add_one]
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
      rw [haddr, List.mapM_cons] at hws
      cases hw : t.globals.lookup a with
      | none => rw [hw] at hws; simp at hws
      | some w =>
          cases hrest : ((List.range ns.length).map (fun i => (a + 1) + BitVec.ofNat 5 i)).mapM
              t.globals.lookup with
          | none => rw [hw, hrest] at hws; simp at hws
          | some ws' =>
              have hwsEq : ws = w :: ws' := by
                rw [hw, hrest] at hws
                simp only [bind, pure, Option.bind, Option.some.injEq] at hws
                exact hws.symm
              subst hwsEq
              obtain ⟨hnn, hndTail⟩ := List.nodup_cons.mp hnd
              obtain ⟨old, hold⟩ := Option.ne_none_iff_exists'.mp (hloc n (by simp))
              simp only [List.length_cons, loadGlobalsHOL, panMap2, crepNestedSeqHOL]
              rw [evalCrepSemHOLProgExact_seq_holShape, evalCrepSemHOLProgExact_assign_holShape]
              simp only [evalCrepSemHOLExp, hw, hold]
              try simp only [if_true]
              let t1 : CrepSemHOLState width σ := { t with locals := t.locals.updateEq (n, w) }
              have hloc1 : ∀ m, m ∈ ns → t1.locals.lookup m ≠ none := by
                intro m hm
                have hmn : m ≠ n := fun h => hnn (h ▸ hm)
                simpa [t1, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hmn] using
                  hloc m (by simp [hm])
              have ih := crepEvalAssignLoadGlobals ns t1 (a + 1) ws' hndTail hloc1 hrest
              rw [ih]
              congr 1

/-- The handler component that `compile_def` gives a Ret call for `hdl`
    (`pan_to_crepScript.sml:224-261`): `SOME (neid, Seq (exp_hdl ctxt.vars evar)
    (compile ctxt p))` when the handler's eid has a code in `ctxt.eids`, otherwise
    none. -/
def compileCallHdlC {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) :
    Option (MlS × MlS × ProgHOL width) → Option (BitVec width × CrepProgHOL width)
  | none => none
  | some (eid, evar, p) => (ctxt.eids.lookup eid).map
      (fun code => (code, CrepProgHOL.seq (expHdlExact ctxt.vars evar) (compileProgExactHOLW ctxt p)))

/-- The compiled Ret call carries exactly the handler `compileCallHdlC ctxt hdl`.
    It is either the standalone `nested_decs` arm, a plain `Call NONE` (only when
    there is no compiled handler), or a plain call with distinct return names. -/
theorem compileCallSomeShapeHdl {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width))
    (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (hno : noOverlapFiniteExact ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh)) :
    let cargs := (compileExpExactHOLWList ctxt args).flatMap Prod.fst
    let rts := (List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)
    compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) =
        nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec width)))
          (.call (some (rts, compileCallHdlC ctxt hdl)) f cargs) ∨
      (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) = .call none f cargs ∧
        compileCallHdlC ctxt hdl = none) ∨
      ∃ rts0 : List Nat, rts0.Nodup ∧
        compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) =
          .call (some (rts0, compileCallHdlC ctxt hdl)) f cargs := by
  intro cargs rts
  rcases dest with _ | ⟨kind, name⟩ <;> rcases hdl with _ | ⟨eid, evar, p⟩ <;>
    simp only [compileProgExactHOLW]
  · exact Or.inl (by simp [compileCallResultNoHandlerExactHOLW, hfuncs, cargs, rts, compileCallHdlC])
  · split
    · rename_i hE
      exact Or.inl (by simp [compileCallHandlerMissingEidExactHOLW,
        compileCallResultNoHandlerExactHOLW, hfuncs, cargs, rts, compileCallHdlC, hE])
    · rename_i code hE
      exact Or.inl (by simp [compileCallHandlerPresentEidExactHOLW, hfuncs, cargs, rts,
        compileCallHdlC, hE])
  · split
    · exact Or.inr (Or.inl ⟨by simp [compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs],
        rfl⟩)
    · rename_i sh ns hwrap
      refine Or.inr (Or.inr ⟨ns, noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns
        hno hwrap, by simp [compileCallWrappedResultNoHandlerExactHOLW, cargs, compileCallHdlC]⟩)
  · split
    · split
      · rename_i hE
        exact Or.inr (Or.inl ⟨by simp [compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
            compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs],
          by simp [compileCallHdlC, hE]⟩)
      · rename_i code hE
        refine Or.inr (Or.inr ⟨[], List.nodup_nil, ?_⟩)
        simp [compileCallWrappedResultFallbackHandlerPresentEidExactHOLW, cargs, compileCallHdlC, hE]
    · rename_i sh ns hwrap
      have hns := noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns hno hwrap
      split
      · rename_i hE
        refine Or.inr (Or.inr ⟨ns, hns, ?_⟩)
        simp [compileCallWrappedResultHandlerMissingEidExactHOLW,
          compileCallWrappedResultNoHandlerExactHOLW, cargs, compileCallHdlC, hE]
      · rename_i code hE
        refine Or.inr (Or.inr ⟨ns, hns, ?_⟩)
        simp [compileCallWrappedResultHandlerPresentEidExactHOLW, cargs, compileCallHdlC, hE]

/-- `locals_rel` depends on target locals only at slots `≤ ctxt.vmax` (by `ctxt_max`),
    generalising the tagged `local_rel_gt_vmax_preserved`. -/
theorem panToCrepLocalsRelFiniteExact_agreeBelowVmax {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width)
    (sl : HolFiniteMapExact MlS (ValueHOL width))
    (tl tl' : HolFiniteMapExact Nat (HolWordLab width))
    (hrel : panToCrepLocalsRelFiniteExact ctxt sl tl)
    (hagree : ∀ k, k ≤ ctxt.vmax → tl'.lookup k = tl.lookup k) :
    panToCrepLocalsRelFiniteExact ctxt sl tl' := by
  refine ⟨hrel.1, hrel.2.1, ?_⟩
  intro name value hlookup
  obtain ⟨slots, words, hcontext, hmap, hflatten, hwf⟩ := hrel.2.2 name value hlookup
  refine ⟨slots, words, hcontext, ?_, hflatten, hwf⟩
  have hle : ∀ k, k ∈ slots → k ≤ ctxt.vmax := hrel.2.1.2 name _ slots hcontext
  have key : ∀ l : List Nat, (∀ k, k ∈ l → k ≤ ctxt.vmax) → l.mapM tl'.lookup = l.mapM tl.lookup := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons k ks ih =>
        intro hl
        simp only [List.mapM_cons]
        rw [hagree k (hl k (by simp)), ih (fun j hj => hl j (by simp [hj]))]
  rw [← hmap, key slots hle]

/-- Target run of a Ret call whose callee raises `n` and whose compiled handler
    does not fire: every arm propagates `Exception n` in a state equal to the
    callee's up to locals. -/
theorem pcCompileCorrectCallExcPropagateTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (n : BitVec width) (t1 : CrepSemHOLState width σ)
    (hno : noOverlapFiniteExact ctxt.vars) (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh))
    (hargs : ((compileExpExactHOLWList ctxt args).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code f flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hcallee : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
      (some (.exception n), t1))
    (hnofire : ∀ code h, compileCallHdlC ctxt hdl = some (code, h) → n ≠ code) :
    ∃ t2, evalCrepSemHOLProgExact t
        (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args)) =
          (some (.exception n), t2) ∧ { t2 with locals := t1.locals } = t1 := by
  classical
  have hafter : ∀ (tt : CrepSemHOLState width σ) (rts0 : List Nat),
      crepCallAfterBody tt (some (rts0, compileCallHdlC ctxt hdl)) (some (.exception n), t1) =
        (some (.exception n), CrepSemHOLState.emptyLocals t1) := by
    intro tt rts0
    cases hH : compileCallHdlC ctxt hdl with
    | none => rfl
    | some ch =>
        obtain ⟨code, h⟩ := ch
        simp only [crepCallAfterBody]
        rw [if_neg (hnofire code h hH)]
  rcases compileCallSomeShapeHdl ctxt dest hdl f args vshapes rsh hno hfuncs with
    hc | ⟨hc, _⟩ | ⟨rts0, hnd0, hc⟩
  · have hnodup : ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)).Nodup :=
      List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
    have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt args (sizeOfShapeHOL rsh) hmax
    rw [hc, crepNestedCallTarget t _ f _ flat body locals _ hargs hlookup
      (by intro r h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]
          exact hnodup) hclock hnodup hdist, hcallee, hafter]
    exact ⟨_, rfl, rfl⟩
  · rw [hc, crepCallTarget t none f _ flat body locals hargs hlookup (by simp) hclock, hcallee]
    exact ⟨_, rfl, rfl⟩
  · rw [hc, crepCallTarget t _ f _ flat body locals hargs hlookup
      (by intro r h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]
          exact hnd0) hclock, hcallee, hafter]
    exact ⟨_, rfl, rfl⟩

/-- Target run of a Ret call whose callee raises `n` and whose compiled handler has
    code `n`. The target runs the handler program on the callee's state with the
    caller's locals (plain arms), or with the slot-extended caller locals and then
    the slot restoration (standalone arm, slots above `vmax`). -/
theorem pcCompileCorrectCallExcCaughtTarget {width : Nat} [NeZero width] {σ : Type}
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (f : MlS) (args : List (ExpHOL width)) (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width))
    (n : BitVec width) (t1 : CrepSemHOLState width σ) (H : CrepProgHOL width)
    (hno : noOverlapFiniteExact ctxt.vars) (hmax : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh))
    (hargs : ((compileExpExactHOLWList ctxt args).flatMap Prod.fst).mapM
          (@evalCrepSemHOLExp width _ σ t
            (fun address => Classical.propDecidable (t.memaddrs address))) = some flat)
    (hlookup : lookupCodeFiniteHOL t.code f flat flat.length = some (body, locals))
    (hclock : t.clock ≠ 0)
    (hcallee : evalCrepSemHOLProgExact { decClockCrepSemHOL t with locals := locals } body =
      (some (.exception n), t1))
    (hfire : compileCallHdlC ctxt hdl = some (n, H)) :
    evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args)) =
        evalCrepSemHOLProgExact { t1 with locals := t.locals } H ∨
      ∃ rts : List Nat, (∀ k, k ∈ rts → ctxt.vmax < k) ∧ rts.Nodup ∧
        evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args)) =
          match evalCrepSemHOLProgExact
              { t1 with locals := (t.locals.updateListEq
                (rts.zip (List.replicate rts.length (HolWordLab.word (0 : BitVec width))))) } H with
          | (q, r) => (q, { r with locals :=
              ((rts.zip (rts.map t.locals.lookup)).foldl
                (fun current entry => HolFiniteMapExact.resVarEq current entry) r.locals) }) := by
  classical
  rcases compileCallSomeShapeHdl ctxt dest hdl f args vshapes rsh hno hfuncs with
    hc | ⟨_, hnone⟩ | ⟨rts0, hnd0, hc⟩
  · right
    have hnodup : ((List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)).Nodup :=
      List.pairwise_map.mpr (List.nodup_range.imp (fun h e => h (by omega)))
    have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt args (sizeOfShapeHOL rsh) hmax
    refine ⟨_, ?_, hnodup, ?_⟩
    · intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨i, _, rfl⟩ := hk
      omega
    · rw [hc, crepNestedCallTarget t _ f _ flat body locals _ hargs hlookup
        (by intro r h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]
            exact hnodup) hclock hnodup hdist, hcallee, hfire]
      simp only [crepCallAfterBody, if_true]
  · rw [hfire] at hnone; exact absurd hnone (by simp)
  · left
    rw [hc, crepCallTarget t _ f _ flat body locals hargs hlookup
      (by intro r h heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq; rw [← heq.1]
          exact hnd0) hclock, hcallee, hfire]
    simp only [crepCallAfterBody, if_true]

private theorem fupdListHOLZipNotMem {α β : Type} [DecidableEq α] (k : α) :
    ∀ (xs : List α) (ys : List β) (f : FiniteMap α β), k ∉ xs →
      FUPDATE_LIST_HOL f (xs.zip ys) k = f k
  | [], _, f, _ => by simp [FUPDATE_LIST_HOL]
  | _ :: _, [], f, _ => by simp [FUPDATE_LIST_HOL]
  | x :: xs, y :: ys, f, hk => by
      simp only [List.mem_cons, not_or] at hk
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons, fupdListHOLZipNotMem k xs ys _ hk.2]
      simp [FUPDATE_HOL, hk.1]

/-- The `pc_compile_correct` result relation survives replacing target locals by
    ones that agree at slots `≤ vmax`. -/
theorem pcCompileCorrectResultRel_agreeBelowVmax {width : Nat} {σ : Type} [NeZero width]
    (ctxt : PanToCrepContextExact width) (s1 : PanSemStateFiniteExact width σ)
    (t2 : CrepSemHOLState width σ) (L : HolFiniteMapExact Nat (HolWordLab width))
    (r : Option (PanSemResultExact width)) (r1 : Option (CrepResultHOLExact width))
    (hagree : ∀ k, k ≤ ctxt.vmax → L.lookup k = t2.locals.lookup k)
    (h : pcCompileCorrectResultRel ctxt s1 t2 r r1) :
    pcCompileCorrectResultRel ctxt s1 { t2 with locals := L } r r1 := by
  rcases r with _ | r
  · exact ⟨h.1, panToCrepLocalsRelFiniteExact_agreeBelowVmax ctxt _ _ _ h.2 hagree⟩
  · cases r with
    | error => exact h.elim
    | timeOut => exact h
    | «break» => exact ⟨h.1, panToCrepLocalsRelFiniteExact_agreeBelowVmax ctxt _ _ _ h.2 hagree⟩
    | «continue» => exact ⟨h.1, panToCrepLocalsRelFiniteExact_agreeBelowVmax ctxt _ _ _ h.2 hagree⟩
    | returned v => exact h
    | exception eid v =>
        simp only [pcCompileCorrectResultRel] at h ⊢
        split at h
        · exact h.elim
        · exact ⟨h.1, fun hsize => by simpa [globalsLookupHOL] using h.2 hsize⟩
    | finalFfi f => exact h

/-- HOL `pc_compile_correct[Call_Ret_Exception]` (`pan_to_crepProofScript.sml:3599-3916`)
    against `pcCompileCorrectAt`: `caltyp = SOME (dest, hdl)` with a positive clock,
    where the callee's source run raises `Exception eid exn`. These are the
    sub-case hypotheses of HOL's case split.
    * Without a handler, or with a different eid, the exception propagates. In
      the target, the handler cannot fire, by `excp_rel` injectivity.
    * With a matching handler, a valid shape and a valid local, `exp_hdl` loads
      the payload from globals: the callee IH gives `globals_lookup`. The
      handler body then satisfies the handler IH of the rebound `evaluate_ind`,
      at `set_var evar exn (st with locals := s.locals)` and the loaded target.
      The standalone arm's slot restoration touches only slots above `vmax`.
    No target run is assumed. Untagged (bead `flapjack-pxn.18.4.3.94.9`). -/
theorem pcCompileCorrectAt_callRetException {width : Nat} {σ : Type} [NeZero width]
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL width))
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectCallIH (some (dest, hdl)) fname argexps source)
    (hclock : source.clock ≠ 0)
    (values : List (ValueHOL width)) (prog : ProgHOL width)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (st : PanSemStateFiniteExact width σ) (eid : MlS) (exn : ValueHOL width)
    (hargs : source.evalListHOLFinite
        (h := fun address => Classical.propDecidable (source.memaddrs address))
        argexps = some values)
    (hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values =
      some (prog, newlocals, rsh))
    (hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
      ).evaluateHOLFiniteState prog = (some (.exception eid exn), st)) :
    pcCompileCorrectAt (.call (some (dest, hdl)) fname argexps : ProgHOL width) source := by
  classical
  intro res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
  have hlocArgs : everyExpListHOL localisedExpHOL argexps = true := by
    rcases dest with _ | ⟨k, n⟩ <;> rcases hdl with _ | ⟨a, b, c⟩ <;> (try rcases k) <;>
      simp_all [localisedProgHOL]
  rw [evaluateHOLFiniteState_call, hargs] at hrun
  dsimp only at hrun
  rw [hlk] at hrun
  dsimp only at hrun
  rw [if_neg hclock, hbody] at hrun
  dsimp only at hrun
  obtain ⟨vshapes, _hsrc, hprogLoc, hfuncs, _hlen, htargs, htlookup, hst', hcode',
    hexcp', hloc'⟩ :=
    pcCompileCorrectCallPrelude source t ctxt fname argexps values prog newlocals rsh
      hargs hlk hstate hcode hexcp hlocals hlocArgs
  have htclock : t.clock ≠ 0 := by rw [← hstate.2.2.2.2.2.1]; exact hclock
  obtain ⟨res1, t1, hrun1, hs, hc, he, hr⟩ :=
    ih.2 values prog newlocals rsh hargs hlk hclock (some (.exception eid exn)) st _ _ hbody
      (by simp) hst' hcode' hexcp' hloc' hprogLoc
  simp only [pcCompileCorrectResultRel, ctxtFcExactHOL] at hr
  cases hn : ctxt.eids.lookup eid with
  | none => rw [hn] at hr; exact hr.elim
  | some n =>
    rw [hn] at hr
    obtain ⟨rfl, hglob⟩ := hr
    have prop : res = some (.exception eid exn) →
        s1 = PanSemStateFiniteExact.emptyLocalsHOLFinite st →
        (∀ code h, compileCallHdlC ctxt hdl = some (code, h) → n ≠ code) →
        ∃ res1 t1', evalCrepSemHOLProgExact t
            (compileProgExactHOLW ctxt (.call (some (dest, hdl)) fname argexps)) = (res1, t1') ∧
          panToCrepStateRelFiniteExact s1 t1' ∧ codeRelExactHOLW ctxt s1.code t1'.code ∧
          panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
          pcCompileCorrectResultRel ctxt s1 t1' res res1 := by
      rintro rfl rfl hnf
      obtain ⟨t2, hrun2, hsame⟩ := pcCompileCorrectCallExcPropagateTarget t ctxt dest hdl fname argexps vshapes rsh
        _ _ _ n t1 hlocals.1 hlocals.2.1 hfuncs htargs htlookup htclock hrun1 hnf
      refine ⟨_, t2, hrun2,
        panToCrepStateRelFiniteExact_emptyLocals_of_sameExceptLocals st t1 t2 hsame hs, ?_, he, ?_⟩
      · have hcode2 : t2.code = t1.code := by rw [← hsame]
        rw [hcode2]; exact codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc
      · simp only [pcCompileCorrectResultRel, hn]
        refine ⟨trivial, fun hsize => ?_⟩
        have hg2 : t2.globals = t1.globals := by rw [← hsame]
        simpa [globalsLookupHOL, hg2] using hglob hsize
    rcases hdl with _ | ⟨hid, hv, hp⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      exact prop rfl rfl (by simp [compileCallHdlC])
    · dsimp only at hrun
      by_cases heq : eid = hid
      case neg =>
        rw [if_neg heq] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        apply prop rfl rfl
        intro code h hH hnc
        simp only [compileCallHdlC, Option.map_eq_some_iff] at hH
        obtain ⟨code', hcode', hpair⟩ := hH
        simp only [Prod.mk.injEq] at hpair
        exact heq (hexcp.2 eid hid n code hn (hpair.1 ▸ hcode') hnc)
      subst heq
      rw [if_pos rfl] at hrun
      cases hsh : source.eshapes.lookup eid with
      | none =>
          rw [hsh] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | some sh =>
        rw [hsh] at hrun
        dsimp only at hrun
        by_cases hok : (shapeEqHOL (shapeOfHOLExact exn) sh &&
            isValidValueHOLExact source.toExact .local hv exn) = true
        case neg =>
          rw [if_neg hok] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
        rw [if_pos hok] at hrun
        obtain ⟨hshb, hvalid⟩ := Bool.and_eq_true_iff.mp hok
        have hshape : shapeOfHOLExact exn = sh := (shapeEqHOL_eq_true _ _).mp hshb
        cases hold : source.locals.lookup hv with
        | none => simp [isValidValueHOLExact, lookupKvarHOLExact, hold] at hvalid
        | some old =>
          have hse : shapeOfHOLExact exn = shapeOfHOLExact old := by
            have : shapeEqHOL (shapeOfHOLExact exn) (shapeOfHOLExact old) = true := by
              simpa [isValidValueHOLExact, lookupKvarHOLExact, hold] using hvalid
            exact (shapeEqHOL_eq_true _ _).mp this
          obtain ⟨nsE, words, hvar, hmm, hfl, hwfo⟩ := hlocals.2.2 hv old hold
          have hwfvE : isWfShapeValueHOLExact [] exn = true := by
            have := panToCrepFiniteEvaluateShapeInvariantRetInst2 argexps source fname values prog
              newlocals rsh prog (.exception eid exn) st t ctxt t.locals
              (by simpa [evalListHOLFiniteClassical] using hargs)
              (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hlk) hbody hstate hlocals
            simpa using this
          have hwfE : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact exn) = true := by
            rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl exn]
            exact hwfvE
          have hflenE := flattenHOL_length_eq_sizeOfShapeHOL exn hwfE
          have hflo := flattenHOL_length_eq_sizeOfShapeHOL old hwfo
          have hnsE : nsE.length = (flattenHOL exn).length := by
            rw [opt_mmap_length_eq _ _ _ hmm, ← hfl, hflo, hflenE, hse]
          have hglobE : ((List.range nsE.length).map (fun i => (0 : BitVec 5) + BitVec.ofNat 5 i)).mapM
              t1.globals.lookup = some (flattenHOL exn) := by
            by_cases hz : sizeOfShapeHOL (shapeOfHOLExact exn) = 0
            · have h0 : nsE.length = 0 := by rw [hnsE, hflenE, hz]
              have hf0 : flattenHOL exn = [] := List.eq_nil_of_length_eq_zero (by rw [hflenE, hz])
              rw [h0, hf0]; rfl
            · have hg := (hglob (by omega)).1
              rw [hnsE, hflenE]
              simpa [globalsLookupHOL] using hg
          have hndE : nsE.Nodup := hlocals.1.1 hv _ nsE hvar
          have ihH := ih.1 values prog newlocals rsh st eid exn dest hv hp sh hargs hlk hclock
            hbody rfl hsh hshape hvalid
          have hlocP : localisedProgHOL hp = true := by
            rcases dest with _ | ⟨k, nm⟩ <;> (try rcases k) <;> simp_all [localisedProgHOL]
          have hfire : compileCallHdlC ctxt (some (eid, hv, hp)) =
              some (n, CrepProgHOL.seq (expHdlExact ctxt.vars hv) (compileProgExactHOLW ctxt hp)) := by
            simp [compileCallHdlC, hn]
          have hrunH : ∀ TT : HolFiniteMapExact Nat (HolWordLab width),
              (∀ k, k ≤ ctxt.vmax → TT.lookup k = t.locals.lookup k) →
              ∃ res2 t2, evalCrepSemHOLProgExact { t1 with locals := TT }
                  (CrepProgHOL.seq (expHdlExact ctxt.vars hv) (compileProgExactHOLW ctxt hp)) =
                    (res2, t2) ∧
                panToCrepStateRelFiniteExact s1 t2 ∧ codeRelExactHOLW ctxt s1.code t2.code ∧
                panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
                pcCompileCorrectResultRel ctxt s1 t2 res res2 := by
            intro TT hagree
            have hlocTT := panToCrepLocalsRelFiniteExact_agreeBelowVmax ctxt source.locals t.locals TT hlocals hagree
            obtain ⟨nsE', words', hvar', hmm', _, _⟩ := hlocTT.2.2 hv old hold
            rw [hvar] at hvar'
            simp only [Option.some.injEq, Prod.mk.injEq] at hvar'
            obtain ⟨_, rfl⟩ := hvar'
            have hpresent : ∀ m, m ∈ nsE → TT.lookup m ≠ none := by
              intro m hm
              have key : ∀ l : List Nat, ∀ ws, l.mapM TT.lookup = some ws → ∀ m, m ∈ l →
                  TT.lookup m ≠ none := by
                intro l
                induction l with
                | nil => intro _ _ m hm; simp at hm
                | cons x xs ih =>
                    intro ws hws m hm
                    rw [List.mapM_cons] at hws
                    cases hx : TT.lookup x with
                    | none => rw [hx] at hws; simp at hws
                    | some wx =>
                        cases hxs : xs.mapM TT.lookup with
                        | none => rw [hx, hxs] at hws; simp at hws
                        | some wxs =>
                            rcases List.mem_cons.mp hm with rfl | hm'
                            · rw [hx]; simp
                            · exact ih wxs hxs m hm'
              exact key nsE words' hmm' m hm
            have hexp : (expHdlExact ctxt.vars hv : CrepProgHOL width) =
                crepNestedSeqHOL (panMap2 (fun destination source => .assign destination source)
                  nsE (loadGlobalsHOL 0 nsE.length)) := by
              simp [expHdlExact, hvar]
            rw [evalCrepSemHOLProgExact_seq_holShape, hexp,
              crepEvalAssignLoadGlobals nsE { t1 with locals := TT } 0 (flattenHOL exn) hndE hpresent
                hglobE]
            simp only [if_true]
            have hsetE : panToCrepLocalsRelFiniteExact ctxt
                (PanSemStateFiniteExact.setVarHOLFinite hv exn
                  { st with locals := source.locals }).locals
                (TT.updateListEq (nsE.zip (flattenHOL exn))) := by
              have hvarE : ctxt.vars.lookup hv = some (shapeOfHOLExact exn, nsE) := by
                rw [hvar, hse]
              have hlr := panToCrepLocalsRelFiniteExact_setVar ctxt source.locals TT hv exn nsE
                hlocTT hvarE hnsE hwfE
              have hupd : source.locals.update (hv, exn) = source.locals.updateEq (hv, exn) := by
                apply HolFiniteMapExact.ext
                funext k
                simp [HolFiniteMapExact.lookup_update, HolFiniteMapExact.lookup_updateEq,
                  FUPDATE_HOL_eq_FUPDATE]
              simpa [PanSemStateFiniteExact.setVarHOLFinite, hupd] using hlr
            exact ihH res s1 _ ctxt hrun hres
              (by simpa [panToCrepStateRelFiniteExact, PanSemStateFiniteExact.setVarHOLFinite]
                using hs)
              (codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ hc) he hsetE hlocP
          rcases pcCompileCorrectCallExcCaughtTarget t ctxt dest (some (eid, hv, hp)) fname argexps vshapes rsh _ _ _ n t1
              _ hlocals.1 hlocals.2.1 hfuncs htargs htlookup htclock hrun1 hfire with
            htgt | ⟨rts, hgt, _hnd, htgt⟩
          · obtain ⟨res2, t2, h2, hs2, hc2, he2, hr2⟩ := hrunH t.locals (fun _ _ => rfl)
            exact ⟨res2, t2, htgt.trans h2, hs2, hc2, he2, hr2⟩
          · have hbelow : ∀ k, k ≤ ctxt.vmax → k ∉ rts := fun k hk hm => by
              have := hgt k hm; omega
            obtain ⟨res2, t2, h2, hs2, hc2, he2, hr2⟩ := hrunH
              (t.locals.updateListEq
                (rts.zip (List.replicate rts.length (HolWordLab.word (0 : BitVec width)))))
              (fun k hk => by
                simp only [HolFiniteMapExact.lookup_updateListEq]
                exact fupdListHOLZipNotMem k rts _ _ (hbelow k hk))
            rw [h2] at htgt
            refine ⟨res2, _, htgt, ?_, hc2, he2, ?_⟩
            · simpa [panToCrepStateRelFiniteExact] using hs2
            · apply pcCompileCorrectResultRel_agreeBelowVmax ctxt s1 t2 _ res res2 _ hr2
              intro k hk
              exact flookupResVarDistinctZipEqHOL rts _ t2.locals k ⟨by simp, hbelow k hk⟩

/-- The `Call` case of HOL `pc_compile_correct` (`pan_to_crepProofScript.sml:3107-4231`)
    against `pcCompileCorrectAt`. Its only hypotheses are the two Call IHs of
    HOL's rebound `panSem$evaluate_ind` (`pcCompileCorrectCallIH`). It assembles
    HOL's own case split:
    * zero clock: `pcCompileCorrectAt_callZeroClock`;
    * `caltyp = NONE`: `Call_TailCall`;
    * otherwise, by the callee's source outcome: `Call_Ret_TimeOut`/`FinalFFI`,
      `Call_Ret_Return`, `Call_Ret_Exception`.
    Failed argument evaluation, failed `lookup_code`, and the callee outcomes
    NONE/Break/Continue/Error are source Errors, excluded by `res ≠ SOME Error`.
    There is no target-run or post-state premise. Untagged: it is the Call
    constructor case of the theorem, and the assembled `pc_compile_correct` is not
    yet proved (bead `flapjack-pxn.18.4.3.94`). -/
theorem pcCompileCorrectAt_call {width : Nat} {σ : Type} [NeZero width]
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width)) (source : PanSemStateFiniteExact width σ)
    (ih : pcCompileCorrectCallIH info fname argexps source) :
    pcCompileCorrectAt (.call info fname argexps : ProgHOL width) source := by
  classical
  by_cases hclock : source.clock = 0
  · exact pcCompileCorrectAt_callZeroClock info fname argexps source hclock
  rcases info with _ | ⟨dest, hdl⟩
  · exact pcCompileCorrectAt_callTail fname argexps source ih hclock
  cases hargs : source.evalListHOLFinite
      (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
      intro res s1 t ctxt hrun hres
      rw [evaluateHOLFiniteState_call, hargs] at hrun
      exact absurd (Prod.mk.inj hrun).1.symm hres
  | some values =>
      cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname values with
      | none =>
          intro res s1 t ctxt hrun hres
          rw [evaluateHOLFiniteState_call, hargs] at hrun
          dsimp only at hrun
          rw [hlk] at hrun
          exact absurd (Prod.mk.inj hrun).1.symm hres
      | some triple =>
          obtain ⟨prog, newlocals, rsh⟩ := triple
          have herr : ∀ st, (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
                ).evaluateHOLFiniteState prog = (none, st) ∨
              (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
                ).evaluateHOLFiniteState prog = (some .break, st) ∨
              (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
                ).evaluateHOLFiniteState prog = (some .continue, st) ∨
              (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
                ).evaluateHOLFiniteState prog = (some .error, st) →
              pcCompileCorrectAt (.call (some (dest, hdl)) fname argexps : ProgHOL width) source := by
            intro st hb res s1 t ctxt hrun hres
            rw [evaluateHOLFiniteState_call, hargs] at hrun
            dsimp only at hrun
            rw [hlk] at hrun
            dsimp only at hrun
            rw [if_neg hclock] at hrun
            rcases hb with hb | hb | hb | hb <;> rw [hb] at hrun <;>
              exact absurd (Prod.mk.inj hrun).1.symm hres
          rcases hbody : (PanSemStateFiniteExact.callEntryStateHOLFinite source newlocals
              ).evaluateHOLFiniteState prog with ⟨bres, st⟩
          rcases bres with _ | r
          · exact herr st (Or.inl hbody)
          · cases r with
            | error => exact herr st (Or.inr (Or.inr (Or.inr hbody)))
            | «break» => exact herr st (Or.inr (Or.inl hbody))
            | «continue» => exact herr st (Or.inr (Or.inr (Or.inl hbody)))
            | timeOut =>
                exact pcCompileCorrectAt_callRetTerminal dest hdl fname argexps source ih hclock
                  values prog newlocals rsh st _ hargs hlk hbody (Or.inl rfl)
            | finalFfi ev =>
                exact pcCompileCorrectAt_callRetTerminal dest hdl fname argexps source ih hclock
                  values prog newlocals rsh st _ hargs hlk hbody (Or.inr ⟨ev, rfl⟩)
            | returned v =>
                exact pcCompileCorrectAt_callRetReturn dest hdl fname argexps source ih hclock
                  values prog newlocals rsh st v hargs hlk hbody
            | exception eid exn =>
                exact pcCompileCorrectAt_callRetException dest hdl fname argexps source ih hclock
                  values prog newlocals rsh st eid exn hargs hlk hbody

/-- HOL `pc_compile_correct`'s induction predicate `P (v, v1)` in HOL's own
    presentation: the single conjunctive premise and the inline `case res of`
    (`pan_to_crepProofScript.sml:442-468`). It is `pcCompileCorrectAt`
    (`pcCompileCorrectAt_iff_HOL`) with HOL's layout, and the tagged Call case
    uses it for its IHs. -/
def pcCompileCorrectAtHOL {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ) : Prop :=
  ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width),
    source.evaluateHOLFiniteState program = (res, s1) ∧
      res ≠ some .error ∧ panToCrepStateRelFiniteExact source t ∧
      codeRelExactHOLW ctxt source.code t.code ∧
      panToCrepExcpRelFiniteExact ctxt.eids source.eshapes ∧
      panToCrepLocalsRelFiniteExact ctxt source.locals t.locals ∧
      localisedProgHOL program = true →
    ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt program) =
        (res1, t1) ∧
      panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
      panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
      match res with
      | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
      | some .error => False
      | some .timeOut => res1 = some .timeOut
      | some .break =>
          res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
      | some .continue =>
          res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
      | some (.returned rv) => res1 = some (.return (flattenHOL rv))
      | some (.exception eid v') =>
          (match ctxt.eids.lookup eid with
           | none => False
           | some n =>
               res1 = some (.exception n) ∧
               (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                 globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                   sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
      | some (.finalFfi f) => res1 = some (.finalFfi f)

theorem pcCompileCorrectAt_iff_HOL {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt program source ↔ pcCompileCorrectAtHOL program source := by
  constructor
  · intro h res s1 t ctxt ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
    obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ := h res s1 t ctxt hrun hres hstate hcode hexcp
      hlocals hloc
    refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
    rcases res with _ | r
    · exact h5
    · cases r <;> exact h5
  · intro h res s1 t ctxt hrun hres hstate hcode hexcp hlocals hloc
    obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ := h res s1 t ctxt
      ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
    refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
    rcases res with _ | r
    · exact h5
    · cases r <;> exact h5

namespace PcCompileCorrectCallWitnesses

/-! Same-module canonical relation witnesses for the three carriers named by the
tagged Call case below (delegating to the imported checked witnesses). -/

theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact

theorem holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_PanToCrepContextExact
    context

theorem holFmapAsFiniteSupportRelationWitness_CrepSemHOLState
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) :
    CrepSemBroadState.ofBroad state.toBroad state.toBroad_finiteSupport = state :=
  CallPreservationFiniteMapWitnesses.holFmapAsFiniteSupportRelationWitness_CrepSemHOLState state

end PcCompileCorrectCallWitnesses

/-- HOL `pc_compile_correct`, `Call` constructor case
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442-468`, proved by
    `recInduct panSemTheory.evaluate_ind` with the case resumed at `:3107`).
    This is the `Call caltyp fname argexps` conjunct of the rebound
    `evaluate_ind` (`panSemScript.sml:777-778`) instantiated at HOL's
    induction predicate
    `P (v, v1) = ∀res s1 t ctxt. evaluate (v,v1) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel v1 t ∧ code_rel ctxt v1.code t.code ∧ excp_rel ctxt.eids v1.eshapes ∧
      locals_rel ctxt v1.locals t.locals ∧ localised_prog v ⇒ ∃res1 t1. ...`.

    The two IHs are transcribed binder for binder from HOL's printed
    `evaluate_ind` Call conjunct, including the TFL equation binders
    `v7 v12 eval_prog v4 v8 v v1 v2 v3 eid' v5` and the side conditions, in HOL
    order. Each is stated at `P` itself (`pcCompileCorrectAtHOL`, whose body is
    exactly the unfolded conclusion below). The conclusion is
    `P (Call caltyp fname argexps, s)` written out with HOL's conjunctive premise
    and inline `case res of`.

    Translation: `evaluate` is the tagged total `evaluateHOLFiniteState`
    (line-780 `evaluate_def`) or `evalCrepSemHOLProgExact` (line-443
    `evaluate_def`). `OPT_MMAP (eval s)` is the evaluator's classical-decision
    list step, and `lookup_code`/`is_valid_value`/`set_var`/`dec_clock` are the
    helpers the tagged Pan Call arm uses. `compile`/`state_rel`/`code_rel`/
    `excp_rel`/`locals_rel`/`globals_lookup`/`flatten`/`size_of_shape`/
    `shape_of`/`localised_prog` are the tagged exact ports. The finite-map fields
    are the canonical `HolFiniteMapExact` translation of the listed carriers, and
    `'a word` is `BitVec width`. -/
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, PanToCrepContextExact.vars, PanToCrepContextExact.funcs,
    PanToCrepContextExact.eids])
  (words_as_type_indexed_bitvec)]
theorem pcCompileCorrect_Call {width : Nat} {σ : Type} [NeZero width] :
    ∀ (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
      (fname : MlS) (argexps : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ),
      (∀ (args : List (ValueHOL width))
          (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL)
          (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
          (v4 : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
          (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
          (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
          (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
          (v3 : MlS × MlS × ProgHOL width) (eid' : MlS) (v5 : MlS × ProgHOL width)
          (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
            v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 ∧
            eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
              { s.decClockHOLFinite with locals := newlocals } prog ∧
            eval_prog = (v4, st) ∧ v4 = some v8 ∧ v8 = .exception eid exn ∧
            caltyp = some v ∧ v = (v1, v2) ∧ v2 = some v3 ∧ v3 = (eid', v5) ∧
            v5 = (evar, p) ∧ eid = eid' ∧ s.eshapes.lookup eid = some sh ∧
            shapeOfHOLExact exn = sh ∧ isValidValueHOLExact s.toExact .local evar exn = true →
          pcCompileCorrectAtHOL p
            (PanSemStateFiniteExact.setVarHOLFinite evar exn { st with locals := s.locals })) ∧
      (∀ (args : List (ValueHOL width))
          (v7 : ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (prog : ProgHOL width) (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
          (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (return_sh : ShapeHOL),
          s.evalListHOLFinite
              (h := fun address => Classical.propDecidable (s.memaddrs address))
              argexps = some args ∧
            PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname args = some v7 ∧
            v7 = (prog, v12) ∧ v12 = (newlocals, return_sh) ∧ s.clock ≠ 0 →
          pcCompileCorrectAtHOL prog { s.decClockHOLFinite with locals := newlocals }) →
      ∀ (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
        (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width),
        s.evaluateHOLFiniteState (.call caltyp fname argexps) = (res, s1) ∧
          res ≠ some .error ∧ panToCrepStateRelFiniteExact s t ∧
          codeRelExactHOLW ctxt s.code t.code ∧
          panToCrepExcpRelFiniteExact ctxt.eids s.eshapes ∧
          panToCrepLocalsRelFiniteExact ctxt s.locals t.locals ∧
          localisedProgHOL (.call caltyp fname argexps) = true →
        ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
          evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt (.call caltyp fname argexps)) =
            (res1, t1) ∧
          panToCrepStateRelFiniteExact s1 t1 ∧ codeRelExactHOLW ctxt s1.code t1.code ∧
          panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
          match res with
          | none => res1 = none ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
          | some .error => False
          | some .timeOut => res1 = some .timeOut
          | some .break =>
              res1 = some (.break 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
          | some .continue =>
              res1 = some (.continue 0) ∧ panToCrepLocalsRelFiniteExact ctxt s1.locals t1.locals
          | some (.returned rv) => res1 = some (.return (flattenHOL rv))
          | some (.exception eid v') =>
              (match ctxt.eids.lookup eid with
               | none => False
               | some n =>
                   res1 = some (.exception n) ∧
                   (1 ≤ sizeOfShapeHOL (shapeOfHOLExact v') →
                     globalsLookupHOL t1 v' = some (flattenHOL v') ∧
                       sizeOfShapeHOL (shapeOfHOLExact v') ≤ 32))
          | some (.finalFfi f) => res1 = some (.finalFfi f) := by
  intro caltyp fname argexps s ⟨ihHandler, ihBody⟩ res s1 t ctxt
    ⟨hrun, hres, hstate, hcode, hexcp, hlocals, hloc⟩
  have ih : pcCompileCorrectCallIH caltyp fname argexps s := by
    refine ⟨?_, ?_⟩
    · intro values prog newlocals returnShape st eid exn v1 evar p sh hargs hlk hclock hbody
        hinfo heshape hshape hvalid
      exact (pcCompileCorrectAt_iff_HOL _ _).mpr <| ihHandler values (prog, newlocals, returnShape) prog (newlocals, returnShape)
        newlocals returnShape (some (.exception eid exn), st) (some (.exception eid exn)) st
        (.exception eid exn) eid exn (v1, some (eid, evar, p)) v1 (some (eid, evar, p))
        (eid, evar, p) eid (evar, p) evar p sh
        ⟨hargs, hlk, rfl, rfl, hclock, hbody.symm, rfl, rfl, rfl, hinfo, rfl, rfl, rfl, rfl, rfl,
          heshape, hshape, hvalid⟩
    · intro values prog newlocals returnShape hargs hlk hclock
      exact (pcCompileCorrectAt_iff_HOL _ _).mpr <| ihBody values (prog, newlocals, returnShape) prog (newlocals, returnShape)
        newlocals returnShape ⟨hargs, hlk, rfl, rfl, hclock⟩
  obtain ⟨res1, t1, h1, h2, h3, h4, h5⟩ :=
    pcCompileCorrectAt_call caltyp fname argexps s ih res s1 t ctxt hrun hres hstate hcode
      hexcp hlocals hloc
  refine ⟨res1, t1, h1, h2, h3, h4, ?_⟩
  rcases res with _ | r
  · exact h5
  · cases r <;> exact h5

end Flapjack
