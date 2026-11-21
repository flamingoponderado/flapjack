module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GiveUp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StateTstamps
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.PartsToWordsNone
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreAnyConsts
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BuildTimestamp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.NumberSize
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BuildMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConstPartsGoodLoc

@[expose] public section

/-! Constant construction assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace BuildWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end BuildWitness

/-- Constant construction satisfies the original assignment simulation,
including invalid layouts, memory allocation, and target stores. The evaluator
inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Build"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignBuild_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ parts, op = .blockOp (.build parts))
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨parts, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  have hasStamp := stateRel_imp_tstamps conf l1 l2 source target none locs related
  cases values with
  | cons first tail =>
    simp only [DataSem.doApp] at run
    cases space : DataSem.doSpace (.blockOp (.build parts)) (first :: tail) source <;>
      simp [space, DataSem.doAppAux, DataSem.applyNonFfi] at run
  | nil =>
    have argsNil : args = [] := by
      have len := DataSpace.getVars_length args source.locals [] argsEq
      cases args <;> simp_all
    subst args
    have good := related.2.2.2.2.2.2.1
    obtain ⟨timestamp, timestampEq⟩ := hasStamp
    let needed := (parts.map DataSpace.partSpaceReq).sum
    have spaceRun : DataSem.doSpace (.blockOp (.build parts)) [] source =
        DataSem.consumeSpace needed source := by
      rw [DataSem.doSpaceAlt]
      simp [DataLang.opSpaceReset, DataSpace.opSpaceReq, needed]
    by_cases insufficient : source.space < needed
    · simp [DataSem.doApp, spaceRun, DataSem.consumeSpace, insufficient] at run
    · let next := DataSem.doStack (.blockOp (.build parts)) []
        (DataSem.doLimSafe source (.blockOp (.build parts)) [])
      cases built : DataSem.doBuildConst parts source.refs (some timestamp) with
      | mk value rem =>
        cases rem with
        | mk refs ts =>
          have tsSome := doBuildConstSome parts source.refs refs timestamp value ts built
          obtain ⟨timestampOut, rfl⟩ := tsSome
          have sourceRun : DataSem.doApp (.blockOp (.build parts)) [] source =
              .val (value, {next with
                refs := refs, tstamps := some timestampOut,
                space := source.space - needed}) := by
            simp [DataSem.doApp, spaceRun, DataSem.consumeSpace, insufficient,
              DataSem.doAppAux, DataSem.applyNonFfi, built, timestampEq, next,
              DataSem.doStack, DataSem.doLimSafe]
          rw [sourceRun] at run
          cases run
          have nextRel : stateRel conf l1 l2 next target none locs :=
            stateRel_doStack conf l1 l2 _ target locs _ _
              (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
          cases compiled : Build.partsWords (width := width) conf parts with
          | none =>
            obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ :=
              evaluateGiveUp2 conf l1 l2 source target locs related
            have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, hbound, hspace⟩ := mem
            have bad := partsToWords_none parts 0 .ln 0 target source heap a sp sp1 gens conf limit
              (by simpa [Build.partsWords] using compiled) good heapMem limits
            have noSafe : ¬ DataSem.limSafe source.limits (.blockOp (.build parts)) [] := by
              simpa [DataSem.limSafe] using bad
            refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
            · simpa [compileAssign, assignBuild, compiled] using outEval
            · intro _
              refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
              · exact BackendProps.optionLe_trans _ _ _
                  ⟨outMax, nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
              · intro _
                simp [next, DataSem.doStack, DataSem.doLimSafe, noSafe]
            · simp
          | some layout =>
            cases layout with
            | mk w ws =>
              have lenBound := constPartsWords_length conf parts w ws compiled good
              have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, hbound, hspace⟩ := mem
              have mem : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                  target.store target.memory target.mdomain
                  (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
                    [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack) :=
                ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, hbound, hspace⟩
              obtain ⟨h1, h2, shiftBound, h4, h5, h6, h7, curr, other, currAligned,
                otherAligned, currLookup, otherLookup, freeLookup, rest⟩ := heapMem
              let free := curr + StackRemove.bytesInWord width * BitVec.ofNat width a
              have freeLookup : target.store.lookup .nextFree = some (.word free) := by
                simpa [free] using freeLookup
              obtain ⟨memory, outputHeap, stored⟩ := memoryRel_doBuildConst conf target.be
                parts source.refs refs timestamp timestampOut result w ws source.space
                target.store target.memory target.mdomain _ free curr built compiled
                (by simpa [timestampEq, holThe] using mem) (by dsimp [needed] at insufficient; omega)
                freeLookup currLookup good
              let resultWord := wordCondAdd conf (free - curr) w
              let newStore := target.store.update (.nextFree,
                .word (free + wordSemBytesInWord * BitVec.ofNat width ws.length))
              let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                flatStack source.stack target.stack
              let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
              have rootHeap : memoryRel conf target.be timestampOut refs (source.space - needed)
                  newStore memory target.mdomain ((result, resultWord) :: locals ++ envs) := by
                apply memoryRel_lessSpace conf target.be timestampOut refs (source.space - ws.length)
                  (source.space - needed) newStore memory target.mdomain _
                refine ⟨?_, ?_⟩
                · simpa [newStore, resultWord, locals, envs] using outputHeap
                · dsimp [needed]; omega
              have shiftSmall : shiftLength conf - wordShiftAmount width < width := by
                have bound := related.2.2.2.2.2.2.2.1
                omega
              have widthBound : width < 2 ^ width := by
                rcases good with h | h <;> subst width <;> decide
              have shiftMod : (shiftLength conf - wordShiftAmount width) % (2 ^ width) =
                  shiftLength conf - wordShiftAmount width := Nat.mod_eq_of_lt (Nat.lt_trans shiftSmall widthBound)
              have shiftNot : ¬ width ≤ shiftLength conf - wordShiftAmount width := Nat.not_le_of_gt shiftSmall
              let shift := (free - curr) <<< (shiftLength conf - wordShiftAmount width)
              let t1 := WordSemStateFiniteExact.setVar 1 (.word free) target
              let t3 := WordSemStateFiniteExact.setVar 3 (.word shift) t1
              have validLoc : ∀ v ∈ w :: ws, goodLoc (sptDomain target.code) v.2 := by
                cases w with
                | mk bit value =>
                  obtain ⟨firstGood, restGood⟩ := constPartsWords_good conf parts (sptDomain target.code)
                    bit value ws compiled
                  intro v hv
                  rcases List.mem_cons.mp hv with eq | mem
                  · subst v; exact firstGood
                  · exact restGood v mem
              have distinct : [adjustVar dest, 1, 3].Nodup := by
                simp [adjustVar]
              obtain ⟨ll, storeEval, resultLookup, preserve⟩ :=
                evaluate_storeAnyConsts (adjustVar dest) 1 3 ws w t3 free (free - curr) conf
                  target.memory memory target.mdomain stored (by rfl) (by rfl) distinct
                  (by simpa [t3, t1, WordSemStateFiniteExact.setVar] using validLoc)
                  (by simp [t3, t1, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
                    sptLookup_sptInsert_same])
                  (by simp [t3, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, shift])
              let midSource := {next with
                refs := refs, tstamps := some timestampOut, space := source.space - needed}
              let midTarget := {target with store := newStore, memory := memory}
              have baseHeap : memoryRel conf target.be timestampOut refs (source.space - needed)
                  newStore memory target.mdomain (locals ++ envs) := by
                apply memoryRel_rearrange conf target.be timestampOut refs _ newStore memory target.mdomain _ _ ?_ rootHeap
                intro pair member
                exact List.mem_cons_of_mem _ member
              have midRel : stateRel conf l1 l2 midSource midTarget none locs := by
                rcases nextRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                  htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
                refine ⟨hffi, hclock, hhandler, hgc, hcode, ?_, hgood, hshift, by simp [midSource], ?_,
                  hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, ?_, ?_⟩
                · simpa [midSource, midTarget, newStore, codeOracleRel, HolFiniteMapExact.update, FUPDATE] using horacle
                · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hglobal
                · simpa [midSource, midTarget, newStore, HolFiniteMapExact.update, FUPDATE] using hlim
                · simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                    holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs, holThe] using baseHeap
              have referenceFinal := stateRel_insertRoot conf l1 l2 midSource midTarget locs dest result
                resultWord midRel (by
                  simpa [midSource, midTarget, newStore, next, DataSem.doStack, DataSem.doLimSafe,
                    holFapply, HolFiniteMapExact.update, FUPDATE, locals, envs, holThe] using rootHeap)
              let expectedLocals := sptInsert (adjustVar dest) resultWord target.locals
              have preserved : ∀ k, k ≠ adjustVar dest → k ≠ 1 → k ≠ 3 →
                  sptLookup k ll = sptLookup k target.locals := by
                intro k hd h1 h3
                have h := preserve k (by simp [hd, h1, h3])
                simpa [t3, t1, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
                  h1, h3] using h
              have atZero : sptLookup 0 ll = sptLookup 0 expectedLocals := by
                have hd : 0 ≠ adjustVar dest := by simp [adjustVar]
                rw [preserved 0 hd (by decide) (by decide)]
                simp [expectedLocals, sptLookup_sptInsert_ne, hd]
              let sourceLocals := sptInsert dest result source.locals
              have interEq : sptInter ll (adjustSet sourceLocals) =
                  sptInter expectedLocals (adjustSet sourceLocals) := by
                apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
                intro k
                rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
                by_cases hd : k = adjustVar dest
                · subst k
                  simp [resultLookup, expectedLocals, sptLookup_sptInsert_same, resultWord]
                · by_cases h1 : k = 1
                  · subst k; simp [lookup_one_adjustSet]
                  · by_cases h3 : k = 3
                    · subst k; simp [lookup_three_adjustSet]
                    · rw [preserved k hd h1 h3]
                      rw [sptLookup_sptInsert_ne _ _ _ _ hd]
              let finalSource := DataSem.setVar dest result midSource
              let finalTarget := {midTarget with locals := ll}
              have finalRel : stateRel conf l1 l2 finalSource finalTarget none locs := by
                have srcLocals : finalSource.locals = sourceLocals := by
                  simp [finalSource, midSource, next, DataSem.setVar, DataSem.doStack, DataSem.doLimSafe, sourceLocals]
                rcases referenceFinal with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                  htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
                have hzero' : sptLookup 0 ll = some (.loc l1 l2) := by
                  rw [atZero]
                  simpa [expectedLocals, WordSemStateFiniteExact.setVar] using hzero rfl
                have hpresent' : ∀ k, (sptLookup k finalSource.locals).isSome →
                    (sptLookup (adjustVar k) ll).isSome := by
                  intro k sourceFound
                  by_cases same : k = dest
                  · subst k; rw [resultLookup]; simp
                  · have hd : adjustVar k ≠ adjustVar dest := by simp [adjustVar]; omega
                    have h1 : adjustVar k ≠ 1 := by simp [adjustVar]
                    have h3 : adjustVar k ≠ 3 := by simp [adjustVar]
                    rw [preserved (adjustVar k) hd h1 h3]
                    have h := hpresent k sourceFound
                    simpa [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, hd] using h
                refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
                  by intro _; exact hzero', hpresent', hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
                simpa [finalSource, finalTarget, midSource, midTarget, expectedLocals,
                  WordSemStateFiniteExact.setVar, srcLocals, interEq] using hmem
              simp only [wordShiftAmount] at shiftMod shiftNot
              refine ⟨none, finalTarget, ?_, ?_, ?_⟩
              · have storeRun := storeEval
                simp only [t3, t1, shift, wordShiftAmount, WordSemStateFiniteExact.setVar] at storeRun
                simp [compileAssign, assignBuild, compiled, wordListSeq,
                  WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
                  freeLookup, currLookup, shiftN, wordShiftAmount,
                  theWords, wordOpHOL, wordOp, sptLookup_sptInsert_same,
                  BitVec.toNat_ofNat, shiftMod, shiftNot, wordShiftHOL]
                rw [storeRun]
                simp [finalTarget, midTarget, newStore, HolFiniteMapExact.updateEq,
                  HolFiniteMapExact.update, FUPDATE_HOL_eq_FUPDATE]
              · simp
              · simpa [finalSource, midSource] using finalRel
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
