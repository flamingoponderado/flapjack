import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect
import Flapjack.Pancake.Proofs.PanToCrep.CompileExpValRel
import Flapjack.Pancake.Proofs.PanToCrep.TotalEvaluateCases
import Flapjack.Pancake.Semantics.PanProps.ListRelFlatten

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

end Flapjack
