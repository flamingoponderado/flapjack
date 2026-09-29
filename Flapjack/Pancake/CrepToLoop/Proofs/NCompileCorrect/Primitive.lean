import Flapjack.HolRef
import Flapjack.Pancake.CrepToLoop.Proofs.LocalsRelOptMmap
import Flapjack.Pancake.CrepToLoop.Proofs.LocalListHelpers
import Flapjack.Pancake.CrepToLoop.Proofs.Primop
import Flapjack.Pancake.CrepToLoop.Proofs.RelationsExact
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

/-!
# The `Primitive` case of `crep_to_loop`'s `ncompile_correct`

This is the constructor case resumed at
`cakeml/pancake/proofs/crep_to_loopProofScript.sml:2357-2407`. The proof uses
only exact source/target evaluation, the reviewed local-list bridges, and the
exact primitive preservation theorem.
-/

namespace Flapjack

open LoopSemStateFiniteExact
open Pancake.CrepToLoop.Proofs.NCompileCorrect

namespace NCompileCorrectPrimitiveFmapWitnesses

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
    {width : Nat} [NeZero width] {σ : Type} :
    (∀ (state : LoopSemStateBroad width σ) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width σ,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end NCompileCorrectPrimitiveFmapWitnesses

private theorem fupdateListHOL_zip_not_mem {α β : Type} [DecidableEq α]
    (key : α) :
    ∀ (keys : List α) (values : List β) (base : α → Option β),
      key ∉ keys → FUPDATE_LIST_HOL base (keys.zip values) key = base key
  | [], _, _, _ => by simp [FUPDATE_LIST_HOL]
  | _ :: _, [], _, _ => by simp [FUPDATE_LIST_HOL]
  | head :: keys, value :: values, base, hnot => by
      simp only [List.mem_cons, not_or] at hnot
      rw [List.zip_cons_cons, FUPDATE_LIST_HOL_cons,
        fupdateListHOL_zip_not_mem key keys values _ hnot.2]
      simp [FUPDATE_HOL, hnot.1]

private theorem fupdateListHOL_zip_getElem {α β : Type} [DecidableEq α]
    (keys : List α) (values : List β) (base : α → Option β)
    (distinct : keys.Nodup) (lengths : keys.length = values.length)
    (index : Nat) (bound : index < keys.length) :
    FUPDATE_LIST_HOL base (keys.zip values) (keys[index]'bound) =
      some (values[index]'(by rw [← lengths]; exact bound)) := by
  induction keys generalizing values base index with
  | nil => simp at bound
  | cons head keys ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
        cases index with
        | zero =>
            simp only [List.getElem_cons_zero, List.zip_cons_cons,
              FUPDATE_LIST_HOL_cons]
            rw [fupdateListHOL_zip_not_mem head keys values
              (FUPDATE_HOL base (head, value)) (List.nodup_cons.mp distinct).1]
            simp [FUPDATE_HOL]
        | succ index =>
            have hindex : index < keys.length := by simpa using bound
            have hhead : keys[index]'(by omega) ≠ head := by
              intro heq
              have : head ∈ keys := heq ▸ List.getElem_mem hindex
              exact (List.nodup_cons.mp distinct).1 this
            simp only [List.getElem_cons_succ, List.zip_cons_cons,
              FUPDATE_LIST_HOL_cons]
            rw [ih values (FUPDATE_HOL base (head, value))
              (List.nodup_cons.mp distinct).2 (by simpa using lengths)
              index hindex]

private theorem holAlookup_zip_getElem {α β : Type} [DecidableEq α]
    (keys : List α) (values : List β) (distinct : keys.Nodup)
    (lengths : keys.length = values.length) (index : Nat)
    (bound : index < keys.length) :
    holAlookup (keys.zip values) (keys[index]'bound) = some (values[index]'(by
      rw [← lengths]; exact bound)) := by
  induction keys generalizing values index with
  | nil => simp at bound
  | cons head keys ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
        cases index with
        | zero => simp [holAlookup]
        | succ index =>
            have hindex : index < keys.length := by simpa using bound
            have hne : head ≠ keys[index]'(by omega) := by
              intro heq
              exact (List.nodup_cons.mp distinct).1
                (heq.symm ▸ List.getElem_mem hindex)
            simp only [List.getElem_cons_succ, List.zip_cons_cons, holAlookup,
              if_neg hne]
            exact ih values (List.nodup_cons.mp distinct).2
              (by simpa using lengths) index hindex

private theorem sptMem_sptAlistInsert_mono {α : Type} (key : Nat) :
    ∀ (names : List Nat) (values : List α) (tree : Spt α),
      sptMem key tree → sptMem key (sptAlistInsert names values tree)
  | [], _, tree, h => h
  | _ :: _, [], tree, h => h
  | name :: names, value :: values, tree, h => by
      apply (sptMem_sptInsert key name value _).2
      exact Or.inr (sptMem_sptAlistInsert_mono key names values tree h)

/-- Genuine `Primitive lhss pop rhss` induction case of HOL
    `ncompile_correct` (`crep_to_loopProofScript.sml:110-154`, resumed at
    `:2357-2407`). This case has no induction hypotheses. Its statement keeps
    the source evaluation, non-Error premise, five input relations, and full
    target evaluation/result/state existential with the HOL result and locals
    postconditions. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "ncompile_correct"
  (fmap_as_finite_support_relation := [CrepToLoopContextExact.vars,
    CrepToLoopContextExact.funcs, CrepSemHOLState.locals, CrepSemHOLState.globals,
    CrepSemHOLState.code, LoopSemStateFiniteExact.globals])
  (words_as_type_indexed_bitvec)]
theorem crepToLoop_ncompile_correct_primitive {width : Nat} [NeZero width]
    {σ : Type}
    (names : List Nat) (operator : PrimOp) (arguments : List Nat)
    (source : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width σ)
    (target : LoopSemStateFiniteExact width σ)
    (context : CrepToLoopContextExact) (live : NumSet)
    (hEval : evalCrepSemHOLProgExact source (.primitive names operator arguments) =
      (result, sourceFinal))
    (hNotError : result ≠ some .error)
    (hState : crepToLoopStateRelExact source target)
    (hMem : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (hGlobals : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (hCode : crepToLoopCodeRelExact context source.code target.code)
    (hLocals : crepToLoopLocalsRelExact context live source.locals target.locals) :
    ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width σ),
      LoopSemStateFiniteExact.evaluate
          (compileHOLExact context live (.primitive names operator arguments))
          { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal := by
  classical
  rw [evalCrepSemHOLProgExact_primitive_holShape] at hEval
  cases hArgs : arguments.mapM source.locals.lookup with
  | none =>
      simp [hArgs] at hEval
      exact False.elim (hNotError hEval.1.symm)
  | some values =>
      cases hPrim : crepPrimopHOLExact operator values with
      | none =>
          simp [hArgs, hPrim] at hEval
          exact False.elim (hNotError hEval.1.symm)
      | some results =>
          have hSourceGuard : names.length = results.length ∧
              (∀ name ∈ names, (source.locals.lookup name).isSome = true) ∧ names.Nodup := by
            by_cases hg : names.length = results.length ∧
                (∀ name ∈ names, (source.locals.lookup name).isSome = true) ∧ names.Nodup
            · exact hg
            · have hEvalError : (some .error, source) = (result, sourceFinal) := by
                simpa [hArgs, hPrim, hg] using hEval
              exact False.elim (hNotError (Prod.mk.inj hEvalError).1.symm)
          have hMapNames := crepToLoop_opt_mmap_lhss_locals_rel
            names source target context live ⟨hSourceGuard.2.1, hSourceGuard.2.2, hLocals⟩
          obtain ⟨loopNames, hMapNames, hNamesLength, hNamesLive, hNamesNodup⟩ := hMapNames
          have hMapArgs := crepToLoop_opt_mmap_rhss_locals_rel
            arguments values source target context live ⟨hArgs, hLocals⟩
          obtain ⟨loopArgs, hMapArgs, hArgsLength, hArgsLive, hGetArgs⟩ := hMapArgs
          have hTargetPrimop := crepPrimopLoopPrimopHOL operator values results hPrim
          have hSourceEval : (none, { source with
                locals := source.locals.updateListEq (names.zip results) }) =
                  (result, sourceFinal) := by
            have hEvalReduced := hEval
            simp only [hArgs, hPrim] at hEvalReduced
            rw [if_pos hSourceGuard] at hEvalReduced
            exact hEvalReduced
          have hResult : result = none := (congrArg Prod.fst hSourceEval).symm
          have hSourceFinal : sourceFinal = { source with
              locals := source.locals.updateListEq (names.zip results) } :=
            (congrArg Prod.snd hSourceEval).symm
          subst result
          have hLocalAfter : crepToLoopLocalsRelExact context live
              sourceFinal.locals
              (sptAlistInsert loopNames (results.map wlabWlocHOL) target.locals) := by
            rw [hSourceFinal]
            refine ⟨hLocals.1, hLocals.2.1, ?_, ?_⟩
            · intro key hk
              exact sptMem_sptAlistInsert_mono key loopNames _ target.locals
                (hLocals.2.2.1 key hk)
            · intro name value hvalue
              rw [HolFiniteMapExact.lookup_updateListEq] at hvalue
              by_cases hIn : name ∈ names
              · obtain ⟨index, bound, hname⟩ := (List.mem_iff_getElem).mp hIn
                have hUpdate : FUPDATE_LIST_HOL source.locals.lookup
                    (names.zip results) name = some (results[index]'(by omega)) := by
                  rw [← hname]
                  exact fupdateListHOL_zip_getElem names results source.locals.lookup
                    hSourceGuard.2.2 hSourceGuard.1 index bound
                have hvalueEq : value = results[index]'(by omega) := by
                  rw [hUpdate] at hvalue
                  exact (Option.some.inj hvalue).symm
                have hContextAt : context.vars.lookup (names[index]'bound) =
                    some (loopNames[index]'(by omega)) := by
                  exact opt_mmap_el names context.vars.lookup loopNames
                    index hMapNames bound
                have hContextAtName : context.vars.lookup name =
                    some (loopNames[index]'(by omega)) := by
                  rw [← hname]
                  exact hContextAt
                have hTargetAt : sptLookup (loopNames[index]'(by omega))
                    (sptAlistInsert loopNames (results.map wlabWlocHOL) target.locals) =
                      some (wlabWlocHOL (results[index]'(by omega))) := by
                  rw [lookup_alist_insert_any,
                    holAlookup_zip_getElem loopNames (results.map wlabWlocHOL)
                      hNamesNodup (by simp [hNamesLength, hSourceGuard.1]) index (by omega)]
                  simp
                have hLoopBound : index < loopNames.length := by omega
                refine ⟨loopNames[index]'(by omega), hContextAtName,
                  hNamesLive _ (List.getElem_mem hLoopBound), ?_⟩
                simpa [hname, hvalueEq] using hTargetAt
              · have hOld : source.locals.lookup name = some value := by
                  rw [fupdateListHOL_zip_not_mem name names results
                    source.locals.lookup hIn] at hvalue
                  exact hvalue
                obtain ⟨loopName, hLookupName, hLive, hOldTarget⟩ :=
                  hLocals.2.2.2 name value hOld
                have hNotMapped : loopName ∉ loopNames :=
                  crepToLoop_not_mem_nlhss_lemma context name names loopName loopNames
                    ⟨hLocals.1, hIn, hLookupName, hMapNames⟩
                refine ⟨loopName, hLookupName, hLive, ?_⟩
                rw [sptLookup_sptAlistInsert_not_mem loopName loopNames _ target.locals hNotMapped]
                exact hOldTarget
          refine ⟨0, none, { target with locals :=
              (sptAlistInsert loopNames (results.map wlabWlocHOL) target.locals) },
            ?_, ?_, ?_, ?_, ?_, rfl, hLocalAfter⟩
          · simp only [compileHOLExact, hMapNames, hMapArgs,
              LoopSemStateFiniteExact.evaluate]
            have hGetArgsClock : LoopSemStateFiniteExact.getVars loopArgs
                ({ target with clock := target.clock + 0 } : LoopSemStateFiniteExact width σ) =
                  some (List.map wlabWlocHOL values) := by
              have hClockState :
                  ({ target with clock := target.clock + 0 } : LoopSemStateFiniteExact width σ) =
                    target := by rfl
              rw [hClockState]
              exact hGetArgs
            simp only [hGetArgsClock, hTargetPrimop]
            have hTargetLength : loopNames.length =
                (List.map wlabWlocHOL results).length := by
              simpa using hNamesLength.trans hSourceGuard.1
            simp only [if_pos hTargetLength, setVars]
            rfl
          · simpa [crepToLoopStateRelExact, hSourceFinal] using hState
          · simpa [hSourceFinal] using hMem
          · simpa [hSourceFinal] using hGlobals
          · simpa [hSourceFinal] using hCode
