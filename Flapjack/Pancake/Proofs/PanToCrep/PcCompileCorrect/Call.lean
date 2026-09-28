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
      refine ⟨_, hrts (some (code, CrepProgHOL.seq (expHdlExact ⟨ctxt.vars⟩ evar)
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

end Flapjack
