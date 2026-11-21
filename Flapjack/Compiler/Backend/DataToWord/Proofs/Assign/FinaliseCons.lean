module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Roots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolNot
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.FinaliseCons

@[expose] public section

/-! Finalising a mutable constructor in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace assignFinaliseConsMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignFinaliseConsMap

/-- Replacing the source references and timestamp counter preserves the state
relation when the new heap is related to the same roots. Flapjack factoring of
the source's `state_rel_thm` rewriting. -/
theorem stateRel_withRefsTstamps {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ts : Option Nat)
    (related : stateRel conf l1 l2 source target none locs) (some_ts : ts.isSome = true)
    (mem : memoryRel conf target.be (holThe ts) refs source.space target.store target.memory
      target.mdomain
      (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        [(theGlobal source.global, holFapply target.store .globals)] ++
        flatStack source.stack target.stack)) :
    stateRel conf l1 l2 { source with refs := refs, tstamps := ts } target none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    _, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
  exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, some_ts, hglobal, hzero,
    hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, by simpa using mem⟩

/-- Finalising a constructor satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_FinaliseCons"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignFinaliseCons_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (finOp : op = .memOp .finaliseCons)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    match values, run with
    | [value], run =>
      let next := DataSem.doStack (.memOp .finaliseCons) [value]
        (DataSem.doLimSafe source (.memOp .finaliseCons) [value])
      have nextRel : stateRel conf l1 l2 next target none locs :=
        stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
      simp only [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        Bool.false_eq_true, if_false, DataSem.doAppAux, DataSem.applyNonFfi] at run
      simp only [if_true] at run
      have refsEq : (DataSem.doStack (.memOp .finaliseCons) [value]
          (DataSem.doLimSafe source (.memOp .finaliseCons) [value])).refs = source.refs := rfl
      have tsEq : (DataSem.doStack (.memOp .finaliseCons) [value]
          (DataSem.doLimSafe source (.memOp .finaliseCons) [value])).tstamps = source.tstamps := rfl
      rw [refsEq, tsEq] at run
      have nextRefs : next.refs = source.refs := rfl
      have nextTs : next.tstamps = source.tstamps := rfl
      cases hf : DataSem.finaliseCons value source.refs source.tstamps with
      | none => simp [hf] at run
      | some triple =>
        obtain ⟨v', refs', ts'⟩ := triple
        simp only [hf] at run
        simp only [Option.bind_eq_bind, Option.bind_some, SemanticPrimitivesHOL.Result.val.injEq,
          Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have argLen : args.length = 1 := by
          have h := DataSpace.getVars_length args source.locals [value] argsEq
          simpa using h.symm
        match args, argLen, argsEq with
        | [arg], _, argsEq =>
          have sourceFound : DataSem.getVar arg source.locals = some value := by
            cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
          obtain ⟨word, targetFound⟩ :=
            stateRel_getVar conf l1 l2 source target none locs arg value related sourceFound
          let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
          let rest := [(theGlobal next.global, holFapply target.store .globals)] ++
            flatStack next.stack target.stack
          have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          obtain ⟨ts0, hts0⟩ := Option.isSome_iff_exists.mp nextRel.2.2.2.2.2.2.2.2.1
          have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
            target.store target.memory target.mdomain next.locals target rest [arg]
            [value] [word] (by
              refine ⟨?_, ?_, ?_⟩
              · simpa [locals, rest] using hmem
              · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
              · simp [WordSemStateFiniteExact.getVars, targetFound])
          rw [hts0] at roots
          have fin := memoryRel_finaliseCons conf target.be ts0 next.refs next.space target.store
            target.memory target.mdomain value word (locals ++ rest) v' refs' ts'
            ⟨by simpa [holThe, locals] using roots, by rw [nextRefs, ← hts0, nextTs]; exact hf⟩
          obtain ⟨someTs, finRel⟩ := fin
          have dropRel : memoryRel conf target.be (holThe ts') refs' next.space target.store
              target.memory target.mdomain (locals ++ rest) :=
            memoryRel_rearrange conf target.be _ _ _ target.store target.memory target.mdomain _ _
              (fun pair hp => List.mem_cons_of_mem _ hp) finRel
          have rel' := stateRel_withRefsTstamps conf l1 l2 next target locs refs' ts' nextRel someTs
            (by simpa [locals, rest, List.append_assoc] using dropRel)
          have updated := stateRel_insertRoot conf l1 l2 _ target locs dest v' word rel'
            (by simpa [locals, rest, List.append_assoc] using finRel)
          have compiled : compileAssign (width := width) conf n l dest (.memOp .finaliseCons) [arg] none =
              assignFinaliseCons l dest arg := by rfl
          refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) word target, ?_, ?_, ?_⟩
          · simp [compiled, assignFinaliseCons, WordSemStateFiniteExact.evaluate,
              WordSemStateFiniteExact.wordExp, targetFound]
          · simp
          · intro _
            refine ⟨?_, rfl⟩
            convert updated using 2
    | [], run => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | _ :: _ :: _, run => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset,
        DataSpace.opSpaceReq, DataSem.doAppAux, DataSem.applyNonFfi] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
