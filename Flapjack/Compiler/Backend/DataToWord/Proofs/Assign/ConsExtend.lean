module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.ConsExtendExpand
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MakePtrBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.NumberVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Integer
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StateTstamps
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumHalt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVarNary
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsAltWritten
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemCopyCorrect
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemCopy.Loop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.EqualConst
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GetVars
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GetVarsCutEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FreeSpace
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.JoinEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreEach
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RefRead
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddrInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreUnused
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.OddInter
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutOdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvs
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax

@[expose] public section

/-! Constructor-extension assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000


namespace ConsExtendWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ConsExtendWitness

/-- Constructor extension satisfies the original assignment simulation, including
allocation failure, live-environment restoration and the copy call. The evaluator
inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_ConsExtend"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignConsExtend_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ tag, op = .blockOp (.consExtend tag))
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
  obtain ⟨tag, rfl⟩ := opIs
  cases names with
  | none => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | some live =>
    obtain ⟨wordCut, words, wordCutRun, wordReads, sourceLen, wordLen, cutRelated, targetCutRelated⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values live cut ⟨related, argsEq, cutEq⟩
    have hasStamp := stateRel_imp_tstamps conf l1 l2 source target none locs related
    rcases values with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩ <;>
      try (solve | simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset,
        DataSem.doAppAux, DataSem.applyNonFfi] at run)
    cases spaceRun : DataSem.doSpace (.blockOp (.consExtend tag)) (first :: second :: third :: fourth :: rest) cut with
    | none => simp [DataSem.doApp, spaceRun] at run
    | some next =>
      let prepared := DataSem.doStack (.blockOp (.consExtend tag)) (first :: second :: third :: fourth :: rest)
        (DataSem.doLimSafe next (.blockOp (.consExtend tag)) (first :: second :: third :: fourth :: rest))
      have auxRun : DataSem.doAppAux (.blockOp (.consExtend tag)) (first :: second :: third :: fourth :: rest) prepared =
          .val (result, resultState) := by
        simpa [DataSem.doApp, spaceRun, prepared] using run
      cases first <;> try (solve | simp [DataSem.doAppAux, DataSem.applyNonFfi] at auxRun)
      case block stamp oldTag previous =>
        cases second <;> try (solve | simp [DataSem.doAppAux, DataSem.applyNonFfi] at auxRun)
        case number lower =>
          cases third <;> try (solve | simp [DataSem.doAppAux, DataSem.applyNonFfi] at auxRun)
          case number length =>
            cases fourth <;> try (solve | simp [DataSem.doAppAux, DataSem.applyNonFfi] at auxRun)
            case number total =>
              simp only [DataSem.doAppAux, DataSem.applyNonFfi] at auxRun
              have valid : ¬ (lower < 0 ∨ length < 0 ∨ lower + length > Int.ofNat previous.length ∨
                  total = 0 ∨ total ≠ Int.ofNat rest.length + length) := by
                intro bad
                simp only [if_pos bad] at auxRun
                cases auxRun
              have lowerNonneg : 0 ≤ lower := by omega
              have lengthNonneg : 0 ≤ length := by omega
              obtain ⟨start, lowerEq⟩ := (int_eq_nat_iff lower).mp lowerNonneg
              obtain ⟨len, lengthEq⟩ := (int_eq_nat_iff length).mp lengthNonneg
              subst lower
              subst length
              have totalEq : total = Int.ofNat rest.length + Int.ofNat len := by omega
              subst total
              rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, tail⟩⟩⟩⟩ <;> simp at sourceLen
              have bounds : start + len ≤ previous.length := by
                have h : Int.ofNat start + Int.ofNat len ≤ Int.ofNat previous.length := by omega
                change (start : Int) + (len : Int) ≤ (previous.length : Int) at h
                exact_mod_cast h
              have nonempty : rest.length + len ≠ 0 := by
                have h : Int.ofNat rest.length + Int.ofNat len ≠ 0 := by omega
                change (rest.length : Int) + (len : Int) ≠ 0 at h
                exact_mod_cast h
              simp only [if_neg valid] at auxRun
              have preparedStamp : prepared.tstamps = cut.tstamps := by
                dsimp [prepared, DataSem.doStack, DataSem.doLimSafe]
                unfold DataSem.doSpace at spaceRun
                split at spaceRun
                · cases spaceRun; rfl
                · dsimp only at spaceRun
                  split at spaceRun
                  · cases spaceRun; rfl
                  · unfold DataSem.consumeSpace at spaceRun
                    split at spaceRun
                    · cases spaceRun
                    · cases spaceRun; rfl
              have nextStackMax : next.stackMax = cut.stackMax := by
                unfold DataSem.doSpace at spaceRun
                split at spaceRun
                · cases spaceRun; rfl
                · dsimp only at spaceRun
                  split at spaceRun
                  · cases spaceRun; rfl
                  · unfold DataSem.consumeSpace at spaceRun
                    split at spaceRun
                    · cases spaceRun
                    · cases spaceRun; rfl
              have nextLimits : next.limits = cut.limits := by
                unfold DataSem.doSpace at spaceRun
                split at spaceRun
                · cases spaceRun; rfl
                · dsimp only at spaceRun
                  split at spaceRun
                  · cases spaceRun; rfl
                  · unfold DataSem.consumeSpace at spaceRun
                    split at spaceRun
                    · cases spaceRun
                    · cases spaceRun; rfl
              have cutStamp : cut.tstamps = source.tstamps := by
                simp only [DataSem.cutStateOpt, DataSem.cutState] at cutEq
                cases env : DataSem.cutEnv live source.locals <;> simp [env] at cutEq
                subst cut
                rfl
              have cutStackMax : cut.stackMax = source.stackMax := by
                simp only [DataSem.cutStateOpt, DataSem.cutState] at cutEq
                cases env : DataSem.cutEnv live source.locals <;> simp [env] at cutEq
                subst cut
                rfl
              have cutLimits : cut.limits = source.limits := by
                simp only [DataSem.cutStateOpt, DataSem.cutState] at cutEq
                cases env : DataSem.cutEnv live source.locals <;> simp [env] at cutEq
                subst cut
                rfl
              obtain ⟨timestamp, timestampEq⟩ := hasStamp
              have preparedTimestamp : prepared.tstamps = some timestamp := by
                rw [preparedStamp, cutStamp, timestampEq]
              simp only [DataSem.withFreshTimestamp, preparedTimestamp,
                SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at auxRun
              rw [assignConsExtend_expand]
              dsimp only
              split
              · rename_i header headerEq
                have noSafe : ¬ DataSem.limSafe source.limits (.blockOp (.consExtend tag))
                    (.block stamp oldTag previous :: .number (Int.ofNat start) :: .number (Int.ofNat len) ::
                      .number (Int.ofNat rest.length + Int.ofNat len) :: rest) := by
                  intro safe
                  simp only [DataSem.limSafe, if_neg valid] at safe
                  have good := related.2.2.2.2.2.2.1
                  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                  have arch : DataSem.archSize source.limits = width := by
                    rcases good with h | h <;> subst width <;>
                      simp [DataSem.archSize, limits.2.2.1]
                  have lenEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
                  have tagSmall : 4 * tag < 2 ^ width / 16 := by simpa [arch] using safe.2.2.1
                  have tagBound : 4 * tag < 2 ^ (width - conf.lenSize - 2) := by
                    simpa [arch, lenEq] using safe.2.2.2
                  simp [encodeHeader, tagSmall, tagBound] at headerEq
                obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ :=
                  evaluateGiveUp2 conf l1 l2 source target locs related
                refine ⟨some .notEnoughSpace, out, outEval, ?_, ?_⟩
                · intro _
                  refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
                  · have targetBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                    have stateBound : optionLe target.stackMax resultState.stackMax := by
                      rw [← auxRun.2]
                      dsimp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe]
                      rw [nextStackMax, cutStackMax, BackendProps.optionLe_max_right]
                      exact Or.inl targetBound
                    exact BackendProps.optionLe_trans _ _ _ ⟨outMax, stateBound⟩
                  · intro _
                    rw [← auxRun.2]
                    change ¬ DataSem.limSafe source.limits (.blockOp (.consExtend tag))
                      (.block stamp oldTag previous :: .number (start : Int) :: .number (len : Int) ::
                        .number ((rest.length : Int) + (len : Int)) :: rest) at noSafe
                    simp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe,
                      nextLimits, cutLimits, noSafe]
                · simp
              · rename_i header headerEq
                have sourceReads1 := (getVars_some_iff_data source.locals a1 _ _ _).2.mp argsEq
                have sourceReads2 := (getVars_some_iff_data source.locals a2 _ _ _).2.mp sourceReads1.2
                have sourceReads3 := (getVars_some_iff_data source.locals a3 _ _ _).2.mp sourceReads2.2
                have sourceReads4 := (getVars_some_iff_data source.locals a4 _ _ _).2.mp sourceReads3.2
                have reads := wordReads
                simp only [List.map_cons] at reads
                obtain ⟨w1, ws1, _, wread1, reads1⟩ := (getVars_some_iff_eq target _ _ _).2.mp reads
                obtain ⟨w2, ws2, _, wread2, reads2⟩ := (getVars_some_iff_eq target _ _ _).2.mp reads1
                obtain ⟨w3, ws3, _, wread3, reads3⟩ := (getVars_some_iff_eq target _ _ _).2.mp reads2
                obtain ⟨w4, ws4, _, wread4, reads4⟩ := (getVars_some_iff_eq target _ _ _).2.mp reads3
                obtain ⟨numberWord, wordEq, bigIff⟩ := stateRel_getVar_number_alt conf l1 l2 source
                  target locs a4 (Int.ofNat rest.length + Int.ofNat len) w4 related sourceReads4.1
                  (by simpa [adjustVar, Nat.mul_comm] using wread4)
                subst w4
                obtain ⟨guardOut, guardEval, guardFfi, guardTargetFfi, guardMax⟩ :=
                  evaluateBignumHalt2 conf l1 l2 source target locs (adjustVar a4) numberWord related wread4
                cases bit : numberWord.getLsbD 0 with
                | true =>
                  simp only [bit, ↓reduceIte] at guardEval
                  let fixed := { guardOut with
                    clock := if target.clock < guardOut.clock then target.clock else guardOut.clock,
                    termdep := target.termdep }
                  refine ⟨some .notEnoughSpace, fixed, ?_, ?_, ?_⟩
                  · change WordSemStateFiniteExact.evaluate
                      (.seq (bignumHalt (adjustVar a4)) _) target = _
                    rw [WordSemStateFiniteExact.evaluate, guardEval]
                    rfl
                  · intro _
                    refine ⟨?_, ?_, ?_⟩
                    · exact guardFfi.trans guardTargetFfi.symm
                    · have targetBound := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                      have stateBound : optionLe target.stackMax resultState.stackMax := by
                        rw [← auxRun.2]
                        dsimp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe]
                        rw [nextStackMax, cutStackMax, BackendProps.optionLe_max_right]
                        exact Or.inl targetBound
                      exact BackendProps.optionLe_trans _ _ _ ⟨guardMax, stateBound⟩
                    · intro _
                      have notSmall := bigIff.mp bit
                      have good := related.2.2.2.2.2.2.1
                      have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                      have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                      obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
                      have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
                      have pbound : 2 ^ conf.lenSize ≤ 2 ^ width / 8 := by
                        rcases good with h | h <;> subst width
                        · have hpow : 2 ^ conf.lenSize ≤ 2 ^ 25 :=
                            Nat.pow_le_pow_right (by decide) (by omega)
                          norm_num at hpow ⊢
                          omega
                        · have hpow : 2 ^ conf.lenSize ≤ 2 ^ 57 :=
                            Nat.pow_le_pow_right (by decide) (by omega)
                          norm_num at hpow ⊢
                          omega
                      have large : 2 ^ conf.lenSize ≤ rest.length + len := by
                        by_contra h
                        have hn : rest.length + len < 2 ^ width / 8 := by omega
                        apply notSmall
                        unfold smallInt
                        change -((2 ^ width / 8 : Nat) : Int) ≤
                          (rest.length : Int) + (len : Int) ∧
                          (rest.length : Int) + (len : Int) < ((2 ^ width / 8 : Nat) : Int)
                        constructor
                        · omega
                        · exact_mod_cast hn
                      have resultLen : (rest ++ (previous.drop start).take len).length = rest.length + len := by
                        simp only [List.length_append, List.length_take, List.length_drop]
                        omega
                      rw [← auxRun.2]
                      simp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe,
                        nextLimits, cutLimits, limits.2.1, resultLen, Nat.not_lt.mpr large]
                  · simp
                | false =>
                  have small : smallInt width (Int.ofNat rest.length + Int.ofNat len) := by
                    by_contra h
                    have bad := bigIff.mpr h
                    simp [bit] at bad
                  have roots := memoryRel_getVar a4 (holThe source.tstamps) target target.store source.space
                    source target.memory
                    ([(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
                    target.mdomain conf target.be (.number (Int.ofNat rest.length + Int.ofNat len))
                    (.word numberWord) (by
                      refine ⟨?_, sourceReads4.1, ?_⟩
                      · simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                      · simpa using wread4)
                  have wordSmall := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
                    source.space target.store target.memory target.mdomain
                    (Int.ofNat rest.length + Int.ofNat len) (.word numberWord) _
                    ⟨related.2.2.2.2.2.2.1, small, by simpa using roots⟩
                  have wordEq : numberWord = smallnum (Int.ofNat rest.length + Int.ofNat len) := by
                    cases wordSmall
                    rfl
                  have wideCut : ∃ wide, DataSem.cutEnv (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live)
                      source.locals = some wide := by
                    have narrowLive : ∀ k, sptMem k live → sptMem k source.locals := by
                      cases narrow : DataSem.cutEnv live source.locals with
                      | none => simp [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
                      | some env =>
                        unfold DataSem.cutEnv at narrow
                        split at narrow
                        · assumption
                        · contradiction
                    have allLive : ∀ k, sptMem k (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live) →
                        sptMem k source.locals := by
                      intro k mem
                      change sptDomain (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live) k at mem
                      rw [Flapjack.Compiler.Backend.BviToData.domain_listInsert] at mem
                      rcases mem with member | member
                      · exact DataProps.getVars_imp_domain _ k source.locals _ ⟨member, argsEq⟩
                      · exact narrowLive k member
                    exact ⟨sptMkWf (sptInter source.locals (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live)),
                      by rw [DataSem.cutEnv, if_pos allLive]⟩
                  obtain ⟨wide, wideRun⟩ := wideCut
                  have wordEncoding : numberWord = BitVec.ofNat width (4 * (rest.length + len)) := by
                    rw [wordEq]
                    change smallnum ((rest.length : Int) + (len : Int)) = _
                    have positive : ¬ (rest.length : Int) + (len : Int) < 0 := by omega
                    simp only [smallnum, if_neg positive]
                    congr 1
                  let target1 := target.setVar 1 (.word numberWord)
                  have rel1 : stateRel conf l1 l2 source target1 none locs := by
                    change stateRel conf l1 l2 source
                      { target with locals := sptInsert 1 (.word numberWord) target.locals } none locs
                    rw [stateRel_insert_1]
                    exact related
                  have read1 : target1.getVar 1 = some (.word (BitVec.ofNat width (4 * (rest.length + len)))) := by
                    simp [target1, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same, wordEncoding]
                  have totalBound : 4 * (rest.length + len) < 2 ^ width := by
                    have h := small.2
                    change (rest.length : Int) + (len : Int) < ((2 ^ width / 8 : Nat) : Int) at h
                    have hn : rest.length + len < 2 ^ width / 8 := by exact_mod_cast h
                    omega
                  have limitBound : min (2 ^ conf.lenSize) (2 ^ width / 16) < 2 ^ width / 8 := by
                    have good := related.2.2.2.2.2.2.1
                    have minBound := Nat.min_le_right (2 ^ conf.lenSize) (2 ^ width / 16)
                    rcases good with h | h <;> subst width <;> norm_num at minBound ⊢
                  cases allocRun : WordSemStateFiniteExact.evaluate
                      (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16))
                        (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live)) target1 with
                  | mk allocResult target2 =>
                    have allocFacts := allocVar_nary conf l1 l2 source target1 locs
                      (a1 :: a2 :: a3 :: a4 :: tail) live wide
                      (.block stamp oldTag previous :: .number (Int.ofNat start) :: .number (Int.ofNat len) ::
                        .number (Int.ofNat rest.length + Int.ofNat len) :: rest)
                      (rest.length + len) (min (2 ^ conf.lenSize) (2 ^ width / 16)) allocResult target2
                      rel1 wideRun argsEq read1 totalBound allocRun limitBound
                    by_cases allocFail : allocResult = some .notEnoughSpace
                    · subst allocResult
                      have failed := allocFacts.1 rfl
                      let fixed2 := { target2 with
                        clock := if target1.clock < target2.clock then target1.clock else target2.clock,
                        termdep := target1.termdep }
                      refine ⟨some .notEnoughSpace, fixed2, ?_, ?_, ?_⟩
                      · change WordSemStateFiniteExact.evaluate
                          (.seq (bignumHalt (adjustVar a4)) _) target = _
                        simp only [bit, Bool.false_eq_true, ↓reduceIte] at guardEval
                        rw [WordSemStateFiniteExact.evaluate, guardEval]
                        simp only [WordSemStateFiniteExact.fixClock, Nat.lt_irrefl, ↓reduceIte]
                        change WordSemStateFiniteExact.evaluate
                          (.seq (.assign 1 (.var (adjustVar a4))) _) target = _
                        rw [WordSemStateFiniteExact.evaluate]
                        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wread4, WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.setVar,
                          Nat.lt_irrefl, ↓reduceIte]
                        change WordSemStateFiniteExact.evaluate
                          (.seq (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16))
                            (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live)) _) target1 = _
                        rw [WordSemStateFiniteExact.evaluate, allocRun]
                        rfl
                      · intro _
                        refine ⟨?_, ?_, ?_⟩
                        · exact failed.1.trans related.1.symm
                        · rw [← auxRun.2]
                          dsimp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe]
                          rw [nextStackMax, cutStackMax, BackendProps.optionLe_max_right]
                          exact Or.inl failed.2.1
                        · intro gc
                          by_contra safe
                          have safeTrue : resultState.safeForSpace = true := by
                            cases h : resultState.safeForSpace <;> simp_all
                          rw [← auxRun.2] at safeTrue
                          simp only [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe,
                            Bool.and_eq_true, decide_eq_true_eq] at safeTrue
                          have resultLen : (rest ++ (previous.drop start).take len).length = rest.length + len := by
                            simp only [List.length_append, List.length_take, List.length_drop]
                            omega
                          have limSafe := safeTrue.2.1.1
                          simp only [DataSem.limSafe, if_neg valid] at limSafe
                          have good := related.2.2.2.2.2.2.1
                          have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have arch : DataSem.archSize source.limits = width := by
                            rcases good with h | h <;> subst width <;>
                              simp [DataSem.archSize, limits.2.2.1]
                          have withinLimit : rest.length + len < min (2 ^ conf.lenSize) (2 ^ width / 16) := by
                            apply Nat.lt_min.mpr
                            constructor
                            · simpa [nextLimits, cutLimits, limits.2.1, resultLen] using limSafe.1
                            · simpa [nextLimits, cutLimits, arch, resultLen] using limSafe.2.1
                          have nextSafe := safeTrue.2.1.2
                          simp only [DataSem.doSpace, DataLang.opSpaceReset, ↓reduceIte,
                            Option.some.injEq] at spaceRun
                          subst next
                          simp only [Bool.and_eq_true, decide_eq_true_eq] at nextSafe
                          have cutRefs : cut.refs = source.refs := by
                            simp only [DataSem.cutStateOpt, DataSem.cutState] at cutEq
                            cases env : DataSem.cutEnv live source.locals <;> simp [env] at cutEq
                            subst cut
                            rfl
                          have cutLocalsEq : cutLocals live source = cut :=
                            cutStateOpt_imp_cutLocals live source cut cutEq
                          have noThunks : DataSem.noThunksInRefs source.refs := by
                            simpa [cutRefs] using nextSafe.2.1
                          have exceeded := failed.2.2 ⟨gc, withinLimit, noThunks⟩
                          rw [cutLocalsEq] at exceeded
                          have fits := nextSafe.2.2
                          simp only [DataSem.spaceConsumed] at fits
                          change DataSem.sizeOfHeapArgs _ cut +
                            (rest ++ (previous.drop start).take len).length + 1 ≤ cut.limits.heapLimit at fits
                          rw [resultLen, cutLimits] at fits
                          omega
                      · simp
                    · obtain ⟨withinLimit, rel2, temp29, code, codeBuffer, dataBuffer, oracle, resultNone⟩ :=
                        allocFacts.2 allocFail
                      subst allocResult
                      have clocks : target1.clock = target2.clock := by
                        have first := related.2.1
                        have second := rel2.2.1
                        simpa [target1, WordSemStateFiniteExact.setVar, first] using second.symm
                      simp only [bit, Bool.false_eq_true, ↓reduceIte] at guardEval
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (bignumHalt (adjustVar a4)) _) target = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, guardEval]
                      simp only [WordSemStateFiniteExact.fixClock, Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 1 (.var (adjustVar a4))) _) target = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate]
                      simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                        wread4, WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (allocVar conf (min (2 ^ conf.lenSize) (2 ^ width / 16))
                          (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live)) _) target1 = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, allocRun]
                      simp only [WordSemStateFiniteExact.fixClock, clocks, Nat.lt_irrefl, ↓reduceIte]
                      let allocatedSource := { source with locals := wide, space := rest.length + len + 1 }
                      let allocatedTarget := { target2 with termdep := target1.termdep }
                      have allocatedRel : stateRel conf l1 l2 allocatedSource allocatedTarget none locs := rel2
                      have allocatedDepth : allocatedTarget.termdep > 1 := by
                        simpa [allocatedTarget, target1, WordSemStateFiniteExact.setVar] using depth
                      have wideReads : DataSem.getVars (a1 :: a2 :: a3 :: a4 :: tail) wide =
                          some (.block stamp oldTag previous :: .number (Int.ofNat start) :: .number (Int.ofNat len) ::
                            .number (Int.ofNat rest.length + Int.ofNat len) :: rest) := by
                        apply getVars_cutEnv _ source.locals wide _ _
                        refine ⟨wideRun, argsEq, ?_⟩
                        intro k mem
                        change sptDomain (sptListInsert (a1 :: a2 :: a3 :: a4 :: tail) live) k
                        rw [Flapjack.Compiler.Backend.BviToData.domain_listInsert]
                        exact Or.inl mem
                      obtain ⟨newWords, newReads, newLength⟩ := stateRel_getVars conf l1 l2
                        allocatedSource allocatedTarget locs (a1 :: a2 :: a3 :: a4 :: tail)
                        (.block stamp oldTag previous :: .number (Int.ofNat start) :: .number (Int.ofNat len) ::
                          .number (Int.ofNat rest.length + Int.ofNat len) :: rest) allocatedRel wideReads
                      rcases newWords with _ | ⟨new1, _ | ⟨new2, _ | ⟨new3, _ | ⟨new4, newTail⟩⟩⟩⟩ <;>
                        simp at newLength
                      have newMemory := memoryRel_getVars conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain allocatedTarget
                        ([(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
                          flatStack allocatedSource.stack allocatedTarget.stack)
                        (a1 :: a2 :: a3 :: a4 :: tail)
                        (.block stamp oldTag previous :: .number (Int.ofNat start) :: .number (Int.ofNat len) ::
                          .number (Int.ofNat rest.length + Int.ofNat len) :: rest)
                        (new1 :: new2 :: new3 :: new4 :: newTail) (by
                          refine ⟨?_, wideReads, newReads⟩
                          simpa using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                      have blockRoot := newMemory
                      simp only [List.zip_cons_cons, List.cons_append] at blockRoot
                      obtain ⟨pointer, pointerEq, blockInfo⟩ := memoryRel_blockImp conf allocatedTarget.be
                        (holThe allocatedSource.tstamps) allocatedSource.refs allocatedSource.space
                        allocatedTarget.store allocatedTarget.memory allocatedTarget.mdomain stamp oldTag previous
                        new1 _ ⟨blockRoot, allocatedRel.2.2.2.2.2.2.1⟩
                      have previousBound : previous.length < 2 ^ (width - 4) := by
                        by_cases empty : previous = []
                        · simp [empty]
                        · simp only [empty, ↓reduceIte] at blockInfo
                          obtain ⟨_, _, _, _, _, _, _, _, _, lengthBound, _, _⟩ := blockInfo
                          exact lengthBound
                      have threshold : 2 ^ (width - 4) ≤ 2 ^ width / 8 := by
                        have good := allocatedRel.2.2.2.2.2.2.1
                        rcases good with h | h <;> subst width <;> norm_num
                      have mkSmall (value : Nat) (h : value < 2 ^ (width - 4)) :
                          smallInt width (Int.ofNat value) := by
                        have hn : value < 2 ^ width / 8 := lt_of_lt_of_le h threshold
                        change -((2 ^ width / 8 : Nat) : Int) ≤ (value : Int) ∧
                          (value : Int) < ((2 ^ width / 8 : Nat) : Int)
                        constructor
                        · omega
                        · exact_mod_cast hn
                      have smallStart : smallInt width (Int.ofNat start) := mkSmall start (by omega)
                      have smallLen : smallInt width (Int.ofNat len) := mkSmall len (by omega)
                      have memory2 := memoryRel_tl conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain _ _ blockRoot
                      have memory3 := memoryRel_tl conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain _ _ memory2
                      have memory4 := memoryRel_tl conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain _ _ memory3
                      have startWord := memoryRel_numberImp conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain (Int.ofNat start) new2 _ ⟨allocatedRel.2.2.2.2.2.2.1, smallStart, memory2⟩
                      have lengthWord := memoryRel_numberImp conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain (Int.ofNat len) new3 _ ⟨allocatedRel.2.2.2.2.2.2.1, smallLen, memory3⟩
                      have totalWord := memoryRel_numberImp conf allocatedTarget.be (holThe allocatedSource.tstamps)
                        allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                        allocatedTarget.mdomain (Int.ofNat rest.length + Int.ofNat len) new4 _
                        ⟨allocatedRel.2.2.2.2.2.2.1, small, memory4⟩
                      simp only [List.map_cons] at newReads
                      have newRead1 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newReads
                      have newRead2 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newRead1.2
                      have newRead3 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newRead2.2
                      have newRead4 := (getVars_some_iff allocatedTarget _ _ _ _).2.mp newRead3.2
                      obtain ⟨nextFree, currentHeap, other, nextFreeRead, currentHeapRead, freeSpace⟩ :=
                        memoryRel_freeSpace conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                          allocatedTarget.mdomain _ allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                      have smallNatWord (x : Nat) : smallnum (Int.ofNat x) = BitVec.ofNat width (4 * x) := by
                        change smallnum (x : Int) = _
                        have positive : ¬ (x : Int) < 0 := by omega
                        simp only [smallnum, if_neg positive]
                        congr 1
                      have newStart : allocatedTarget.getVar (adjustVar a2) =
                          some (.word (BitVec.ofNat width (4 * start))) := by
                        have read := newRead2.1
                        rw [startWord, smallNatWord] at read
                        exact read
                      have newLengthRead : allocatedTarget.getVar (adjustVar a3) =
                          some (.word (BitVec.ofNat width (4 * len))) := by
                        have read := newRead3.1
                        rw [lengthWord, smallNatWord] at read
                        exact read
                      have newTotal : allocatedTarget.getVar (adjustVar a4) =
                          some (.word (BitVec.ofNat width (4 * (rest.length + len)))) := by
                        have read := newRead4.1
                        rw [totalWord, ← wordEq, wordEncoding] at read
                        exact read
                      have newPointer : allocatedTarget.getVar (adjustVar a1) = some (.word pointer) := by
                        simpa [pointerEq] using newRead1.1
                      have pointerAddress : previous ≠ [] → ∃ address, getRealAddr conf allocatedTarget.store pointer = some address := by
                        intro nonemptyBlock
                        simp only [nonemptyBlock, ↓reduceIte] at blockInfo
                        obtain ⟨address, _, _, _, _, addressRead, _⟩ := blockInfo
                        exact ⟨address, addressRead⟩
                      have prunedMemory : memoryRel conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory allocatedTarget.mdomain
                          ((.block stamp oldTag previous, .word pointer) ::
                            (rest.zip newTail ++ joinEnv allocatedSource.locals
                              (sptToAList (sptInter allocatedTarget.locals (adjustSet allocatedSource.locals))) ++
                              [(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
                              flatStack allocatedSource.stack allocatedTarget.stack)) := by
                        apply memoryRel_rearrange conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                          allocatedTarget.mdomain _ _ ?_ blockRoot
                        intro pair member
                        simp only [List.mem_cons, List.mem_append] at member ⊢
                        subst new1
                        aesop
                      have narrowRun : DataSem.cutEnv live source.locals = some cut.locals := by
                        cases narrow : DataSem.cutEnv live source.locals with
                        | none => simp [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
                        | some env =>
                          simp [DataSem.cutStateOpt, DataSem.cutState, narrow] at cutEq
                          subst cut
                          rfl
                      have wideNarrow := cutEnv_cutEnv_listInsert (a1 :: a2 :: a3 :: a4 :: tail) live
                        source.locals wide cut.locals ⟨wideRun, narrowRun⟩
                      have subLookup : ∀ key value, sptLookup key cut.locals = some value →
                          sptLookup key wide = some value := by
                        intro key value found
                        rw [DataLive.cutEnv_lookup live wide cut.locals wideNarrow key] at found
                        split at found
                        · exact found
                        · contradiction
                      have narrowMemory : memoryRel conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory allocatedTarget.mdomain
                          ((.block stamp oldTag previous, .word pointer) ::
                            (rest.zip newTail ++ joinEnv cut.locals
                              (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) ++
                              [(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
                              flatStack allocatedSource.stack allocatedTarget.stack)) := by
                        apply memoryRel_rearrange conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store allocatedTarget.memory
                          allocatedTarget.mdomain _ _ ?_ prunedMemory
                        intro pair member
                        have subJoin : pair ∈ joinEnv cut.locals
                            (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) →
                            pair ∈ joinEnv allocatedSource.locals
                              (sptToAList (sptInter allocatedTarget.locals (adjustSet allocatedSource.locals))) := by
                          intro inJoin
                          exact joinEnv_submap_mem cut.locals wide allocatedTarget.locals allocatedTarget.locals pair
                            ⟨subLookup, by intros; assumption, inJoin⟩
                        simp only [List.mem_cons, List.mem_append] at member ⊢
                        aesop
                      let fullHeader : BitVec width :=
                        (BitVec.ofNat width (4 * (rest.length + len)) <<< (width - conf.lenSize - 2)) ||| header
                      obtain ⟨storedMemory, storedRun, storedSpace⟩ := storeList_exists
                        (.word fullHeader :: newTail) nextFree allocatedSource.space allocatedTarget.memory
                        allocatedTarget.mdomain other ⟨freeSpace, by simp [allocatedSource] at newLength ⊢; omega⟩
                      have goodWidth := allocatedRel.2.2.2.2.2.2.1
                      have wideEnough : 10 < width := by rcases goodWidth with h | h <;> omega
                      have widthPow : width < 2 ^ width := by
                        rcases goodWidth with h | h <;> subst width <;> decide
                      have shiftBound : width - conf.lenSize - 2 < width := by omega
                      have shiftMod : (width - conf.lenSize - 2) % (2 ^ width) = width - conf.lenSize - 2 :=
                        Nat.mod_eq_of_lt (Nat.lt_trans shiftBound widthPow)
                      have rightShift : (BitVec.ofNat width (4 * (rest.length + len))) >>> 2 =
                          BitVec.ofNat width (rest.length + len) := by
                        apply BitVec.eq_of_toNat_eq
                        have totalBelow : rest.length + len < 2 ^ width := by omega
                        have twoMod : 2 % (2 ^ width) = 2 := Nat.mod_eq_of_lt (by omega)
                        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.mod_eq_of_lt totalBound, Nat.mod_eq_of_lt totalBelow, twoMod]
                      let tA := allocatedTarget.setVar 1 (.word nextFree)
                      let tB := tA.setVar 5 (.word fullHeader)
                      let tC := tB.setVar 7 (.word (BitVec.ofNat width (rest.length + len)))
                      let tD := tC.setVar 9 (.word (BitVec.ofNat width tag))
                      have adjustedTail : WordSemStateFiniteExact.getVars (tail.map adjustVar) tD = some newTail := by
                        have r9 := getVarsAdjustVar tail tC tC.locals 9 (.word (BitVec.ofNat width tag)) (by decide)
                        have r7 := getVarsAdjustVar tail tB tB.locals 7 (.word (BitVec.ofNat width (rest.length + len))) (by decide)
                        have r5 := getVarsAdjustVar tail tA tA.locals 5 (.word fullHeader) (by decide)
                        have r1 := getVarsAdjustVar tail allocatedTarget allocatedTarget.locals 1 (.word nextFree) (by decide)
                        simpa [tD, tC, tB, tA, WordSemStateFiniteExact.setVar] using
                          r9.trans (r7.trans (r5.trans (r1.trans newRead4.2)))
                      have headRead : tD.getVar 5 = some (.word fullHeader) := by
                        simp [tD, tC, tB, tA, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                      have baseRead : tD.getVar 1 = some (.word nextFree) := by
                        simp [tD, tC, tB, tA, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                      have storeArgs : WordSemStateFiniteExact.getVars (5 :: tail.map adjustVar) tD =
                          some (.word fullHeader :: newTail) := by
                        simp only [WordSemStateFiniteExact.getVars, headRead, adjustedTail]
                      have storeEval := evaluate_storeEach (.word fullHeader :: newTail)
                        (5 :: tail.map adjustVar) tD 1 nextFree storedMemory
                        ⟨by simpa [tD, tC, tB, tA, WordSemStateFiniteExact.setVar] using storedRun,
                          storeArgs, baseRead⟩
                      have diff1 : adjustVar a4 ≠ 1 := by simp [adjustVar]
                      have diff5 : adjustVar a4 ≠ 5 := by simp [adjustVar]; omega
                      have readA : tA.getVar (adjustVar a4) =
                          some (.word (BitVec.ofNat width (4 * (rest.length + len)))) := by
                        simpa [tA, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne, diff1] using newTotal
                      have readB : tB.getVar (adjustVar a4) =
                          some (.word (BitVec.ofNat width (4 * (rest.length + len)))) := by
                        simpa [tB, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne, diff5] using readA
                      have evalA : WordSemStateFiniteExact.evaluate (.assign 1 (.lookup .nextFree)) allocatedTarget =
                          (none, tA) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          WordSemStateFiniteExact.getStore, nextFreeRead, tA]
                      have evalB : WordSemStateFiniteExact.evaluate
                          (.assign 5 (.op .or [shiftN .lsl (.var (adjustVar a4)) (width - conf.lenSize - 2),
                            .const header])) tA = (none, tB) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, shiftN,
                          readA, wordShiftHOL, BitVec.toNat_ofNat, shiftMod, Nat.not_le_of_gt shiftBound,
                          wordOpHOL, wordOp, theWords, OrOp.or, BitVec.or_zero, fullHeader, tB]
                      have evalC : WordSemStateFiniteExact.evaluate
                          (.assign 7 (shiftN .lsr (.var (adjustVar a4)) 2)) tB = (none, tC) := by
                        have twoMod : 2 % (2 ^ width) = 2 := Nat.mod_eq_of_lt (by omega)
                        have notWide : ¬ width ≤ 2 := by omega
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, shiftN,
                          readB, wordShiftHOL, BitVec.toNat_ofNat, twoMod, notWide,
                          tC]
                        congr 2
                        apply BitVec.eq_of_toNat_eq
                        have totalBelow : rest.length + len < 2 ^ width := by omega
                        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                          Nat.mod_eq_of_lt totalBound, Nat.mod_eq_of_lt totalBelow]
                      have evalD : WordSemStateFiniteExact.evaluate
                          (.assign 9 (.const (BitVec.ofNat width tag))) tC = (none, tD) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, tD]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 1 (.lookup .nextFree)) _) allocatedTarget = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, evalA]
                      simp only [WordSemStateFiniteExact.fixClock, tA, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 5 (.op .or [shiftN .lsl (.var (adjustVar a4)) (width - conf.lenSize - 2),
                          .const header])) _) tA = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, evalB]
                      simp only [WordSemStateFiniteExact.fixClock, tB, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 7 (shiftN .lsr (.var (adjustVar a4)) 2)) _) tB = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, evalC]
                      simp only [WordSemStateFiniteExact.fixClock, tC, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 9 (.const (BitVec.ofNat width tag))) _) tC = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, evalD]
                      simp only [WordSemStateFiniteExact.fixClock, tD, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (storeEach 1 (5 :: tail.map adjustVar) 0) _) tD = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, storeEval]
                      simp only [WordSemStateFiniteExact.fixClock, Nat.lt_irrefl, ↓reduceIte]
                      let storedTarget := { tD with memory := storedMemory }
                      have tagRead : sptLookup 9 storedTarget.locals = some (.word (BitVec.ofNat width tag)) := by
                        simp [storedTarget, tD, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                      have lenRead : sptLookup 7 storedTarget.locals =
                          some (.word (BitVec.ofNat width (rest.length + len))) := by
                        simp [storedTarget, tD, tC, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                      have tagBound : tag < 2 ^ width := by
                        have encoded := headerEq
                        unfold encodeHeader at encoded
                        split at encoded
                        · next condition => omega
                        · contradiction
                      have lenBound : rest.length + len < 2 ^ width := by omega
                      have shiftBound' : shiftLength conf < width := allocatedRel.2.2.2.2.2.2.2.1
                      have tagBits : conf.tagBits < width := by dsimp [shiftLength] at shiftBound'; omega
                      have lenBits : conf.lenBits < width := by dsimp [shiftLength] at shiftBound'; omega
                      have lenShift : conf.lenBits + 1 < width := by dsimp [shiftLength] at shiftBound'; omega
                      obtain ⟨_, ptrEval⟩ := makePtrBits_correct (β := Unit) conf 9 7 3 tag (rest.length + len)
                        storedTarget nextFree currentHeap (by decide) tagBound tagBits (by decide) lenBound lenBits
                        lenShift (by simpa [storedTarget, tD, tC, tB, tA, WordSemStateFiniteExact.setVar] using nextFreeRead)
                        (by simpa [storedTarget, tD, tC, tB, tA, WordSemStateFiniteExact.setVar] using currentHeapRead)
                        tagRead lenRead (by omega)
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (makePtrBitsCode conf 9 7 3) _) storedTarget = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, ptrEval]
                      simp only [WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      let ptrTarget := storedTarget.setVar 3 (Build.makeConsPtr conf (nextFree - currentHeap) tag (rest.length + len))
                      let nextAddress := nextFree + wordSemBytesInWord +
                        (BitVec.ofNat width (rest.length + len) <<< wordShiftAmount width)
                      have ptrRead1 : ptrTarget.getVar 1 = some (.word nextFree) := by
                        simpa [ptrTarget, storedTarget, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using baseRead
                      have ptrRead7 : ptrTarget.getVar 7 = some (.word (BitVec.ofNat width (rest.length + len))) := by
                        simpa [ptrTarget, storedTarget, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using lenRead
                      have machineShiftBound : wordShiftAmount width < width := by
                        rcases goodWidth with h | h <;> subst width <;> simp [wordShiftAmount]
                      have machineShiftMod : wordShiftAmount width % (2 ^ width) = wordShiftAmount width :=
                        Nat.mod_eq_of_lt (Nat.lt_trans machineShiftBound widthPow)
                      let afterNext := ptrTarget.setStore .nextFree (.word nextAddress)
                      have evalNext : WordSemStateFiniteExact.evaluate
                          (.set .nextFree (.op .add [.var 1, .const wordSemBytesInWord,
                            shiftN .lsl (.var 7) (wordShiftAmount width)])) ptrTarget = (none, afterNext) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          ptrRead1, ptrRead7, shiftN, wordShiftHOL, BitVec.toNat_ofNat, machineShiftMod,
                          Nat.not_le_of_gt machineShiftBound, wordOpHOL, wordOp, theWords, BitVec.add_assoc,
                          nextAddress, afterNext]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.set .nextFree (.op .add [.var 1, .const wordSemBytesInWord,
                          shiftN .lsl (.var 7) (wordShiftAmount width)])) _) ptrTarget = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, evalNext]
                      simp only [WordSemStateFiniteExact.fixClock, afterNext, WordSemStateFiniteExact.setStore,
                        Nat.lt_irrefl, ↓reduceIte]
                      have lenAfter : afterNext.getVar (adjustVar a3) =
                          some (.word (BitVec.ofNat width (4 * len))) := by
                        have ne1 : adjustVar a3 ≠ 1 := by simp [adjustVar]
                        have ne3 : adjustVar a3 ≠ 3 := by simp [adjustVar]
                        have ne5 : adjustVar a3 ≠ 5 := by simp [adjustVar]; omega
                        have ne7 : adjustVar a3 ≠ 7 := by simp [adjustVar]; omega
                        have ne9 : adjustVar a3 ≠ 9 := by simp [adjustVar]; omega
                        simpa [afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                          WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, ne1, ne3, ne5, ne7, ne9]
                          using newLengthRead
                      let after15 := afterNext.setVar 15 (.word (BitVec.ofNat width (4 * len)))
                      have eval15 : WordSemStateFiniteExact.evaluate (.assign 15 (.var (adjustVar a3))) afterNext =
                          (none, after15) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, lenAfter, after15]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 15 (.var (adjustVar a3))) _) afterNext = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, eval15]
                      simp only [WordSemStateFiniteExact.fixClock, after15, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      have base15 : after15.getVar 1 = some (.word nextFree) := by
                        simpa [after15, afterNext, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.setStore, sptLookup_sptInsert_ne] using ptrRead1
                      let destAddress := nextFree + wordSemBytesInWord * BitVec.ofNat width (tail.length + 1)
                      let after13 := after15.setVar 13 (.word destAddress)
                      have eval13 : WordSemStateFiniteExact.evaluate (.assign 13 (.op .add [
                          .var 1, .const (wordSemBytesInWord * BitVec.ofNat width (tail.length + 1))])) after15 =
                          (none, after13) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, base15, destAddress, after13]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 13 (.op .add [.var 1,
                          .const (wordSemBytesInWord * BitVec.ofNat width (tail.length + 1))])) _) after15 = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, eval13]
                      simp only [WordSemStateFiniteExact.fixClock, after13, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      have pointerAfter : after13.getVar (adjustVar a1) = some (.word pointer) := by
                        have ne1 : adjustVar a1 ≠ 1 := by simp [adjustVar]
                        have ne3 : adjustVar a1 ≠ 3 := by simp [adjustVar]
                        have ne5 : adjustVar a1 ≠ 5 := by simp [adjustVar]; omega
                        have ne7 : adjustVar a1 ≠ 7 := by simp [adjustVar]; omega
                        have ne9 : adjustVar a1 ≠ 9 := by simp [adjustVar]; omega
                        have ne13 : adjustVar a1 ≠ 13 := by simp [adjustVar]; omega
                        have ne15 : adjustVar a1 ≠ 15 := by simp [adjustVar]; omega
                        simpa [after13, after15, afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                          WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne,
                          ne1, ne3, ne5, ne7, ne9, ne13, ne15] using newPointer
                      have currAfter : after13.store.lookup .currHeap = some (.word currentHeap) := by
                        simpa [after13, after15, afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                          WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
                          HolFiniteMapExact.updateEq, FUPDATE_HOL, FUPDATE] using currentHeapRead
                      obtain ⟨realValue, realEval⟩ := wordExpRealAddrSomeValue conf after13 (adjustVar a1)
                        currentHeap pointer currAfter pointerAfter goodWidth shiftBound'
                      have startAfter : after13.getVar (adjustVar a2) =
                          some (.word (BitVec.ofNat width (4 * start))) := by
                        have ne1 : adjustVar a2 ≠ 1 := by simp [adjustVar]
                        have ne3 : adjustVar a2 ≠ 3 := by simp [adjustVar]
                        have ne5 : adjustVar a2 ≠ 5 := by simp [adjustVar]; omega
                        have ne7 : adjustVar a2 ≠ 7 := by simp [adjustVar]; omega
                        have ne9 : adjustVar a2 ≠ 9 := by simp [adjustVar]; omega
                        have ne13 : adjustVar a2 ≠ 13 := by simp [adjustVar]; omega
                        have ne15 : adjustVar a2 ≠ 15 := by simp [adjustVar]; omega
                        simpa [after13, after15, afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                          WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne,
                          ne1, ne3, ne5, ne7, ne9, ne13, ne15] using newStart
                      have shiftEval : after13.wordExp (shiftVar .lsl (adjustVar a2) (wordShiftAmount width - 2)) =
                          some (.word (BitVec.ofNat width (4 * start) <<< (wordShiftAmount width - 2))) := by
                        rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.wordExpShiftVar]
                        change sptLookup (adjustVar a2) after13.locals = _ at startAfter
                        simp [startAfter, Flapjack.SemanticPrimitivesProps.shiftLookup]
                      let sourceAddress := realValue + wordSemBytesInWord +
                        (BitVec.ofNat width (4 * start) <<< (wordShiftAmount width - 2))
                      let after11 := after13.setVar 11 (.word sourceAddress)
                      have eval11 : WordSemStateFiniteExact.evaluate (.assign 11 (.op .add [
                          realAddr conf (adjustVar a1), .const wordSemBytesInWord,
                          shiftVar .lsl (adjustVar a2) (wordShiftAmount width - 2)])) after13 = (none, after11) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          realEval, shiftEval, wordOpHOL, wordOp, theWords, BitVec.add_assoc, sourceAddress, after11]
                      change ∃ q r, WordSemStateFiniteExact.evaluate
                        (.seq (.assign 11 (.op .add [realAddr conf (adjustVar a1), .const wordSemBytesInWord,
                          shiftVar .lsl (adjustVar a2) (wordShiftAmount width - 2)])) _) after13 = (q, r) ∧ _
                      rw [WordSemStateFiniteExact.evaluate, eval11]
                      simp only [WordSemStateFiniteExact.fixClock, after11, WordSemStateFiniteExact.setVar,
                        Nat.lt_irrefl, ↓reduceIte]
                      have memoryAfterStore := memoryRel_storeListToUnused conf allocatedTarget.be
                        (holThe allocatedSource.tstamps) allocatedSource.refs allocatedSource.space
                        allocatedTarget.store allocatedTarget.memory storedMemory allocatedTarget.mdomain _ nextFree
                        (.word fullHeader :: newTail) narrowMemory storedRun nextFreeRead (by
                          simp [allocatedSource] at newLength ⊢
                          omega)
                      obtain ⟨realBefore, realBeforeEval⟩ := wordExpRealAddrSomeValue conf allocatedTarget
                        (adjustVar a1) currentHeap pointer currentHeapRead newPointer goodWidth shiftBound'
                      have suffixLength : allocatedSource.space - (newTail.length + 1) = len := by
                        simp [allocatedSource] at newLength ⊢
                        omega
                      have copySeparation : SetSep.star
                          (SetSep.star (Misc.wordList nextFree (.word fullHeader :: newTail))
                            (Misc.wordListExists (nextFree + StackRemove.bytesInWord width *
                              BitVec.ofNat width (newTail.length + 1)) len)) other
                          (SetSep.fun2Set (storedMemory, fun a => allocatedTarget.mdomain a = true)) := by
                        simpa [suffixLength, Nat.add_comm] using storedSpace
                      obtain ⟨copiedMemory, copiedWords, copiedRun, copiedSpace, copiedLength, copiedRel⟩ :=
                        impMemcopy conf allocatedTarget allocatedSource (holThe allocatedSource.tstamps)
                          allocatedSource.space a1 stamp oldTag previous pointer realBefore nextFree fullHeader
                          (joinEnv cut.locals (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) ++
                            [(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
                            flatStack allocatedSource.stack allocatedTarget.stack)
                          other len start len rest newTail storedMemory (by simpa [List.append_assoc] using memoryAfterStore)
                          copySeparation (by omega)
                          goodWidth newPointer realBeforeEval nextFreeRead bounds (by simp [allocatedSource] at newLength ⊢; omega)
                          (by omega)
                      have headerGood : 4 * tag < 2 ^ (width - conf.lenSize - 2) ∧
                          4 * tag < 2 ^ width / 16 := by
                        have eq := headerEq
                        unfold encodeHeader at eq
                        split at eq
                        · next condition => exact ⟨condition.1, condition.2.1⟩
                        · contradiction
                      have headerBase : header = makeHeader conf (BitVec.ofNat width (4 * tag)) 0 := by
                        have eq := headerEq
                        unfold encodeHeader at eq
                        split at eq
                        · simpa using eq.symm
                        · contradiction
                      have lenSizeBound : rest.length + len < 2 ^ conf.lenSize :=
                        (Nat.lt_min.mp withinLimit).1
                      have lenWidthBound : rest.length + len < 2 ^ (width - 4) := by
                        have h := (Nat.lt_min.mp withinLimit).2
                        rcases goodWidth with eq | eq <;> subst width <;> norm_num at h ⊢ <;> omega
                      have timesFour : BitVec.ofNat width (4 * (rest.length + len)) =
                          (BitVec.ofNat width (rest.length + len) <<< (2 : Nat)) := by
                        apply BitVec.eq_of_toNat_eq
                        simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                          Nat.mul_mod, Nat.mul_comm]
                      have addShift : 2 + (width - conf.lenSize - 2) = width - conf.lenSize := by
                        obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ :=
                          allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                        have h := heapMem.2.2.2.2.1
                        omega
                      have fullEncoded : encodeHeader conf (4 * tag) (rest.length + len) = some fullHeader := by
                        have condition : 4 * tag < 2 ^ (width - conf.lenSize - 2) ∧
                            4 * tag < 2 ^ width / 16 ∧ rest.length + len < 2 ^ (width - 4) ∧
                            rest.length + len < 2 ^ conf.lenSize :=
                          ⟨headerGood.1, headerGood.2, lenWidthBound, lenSizeBound⟩
                        simp only [encodeHeader, if_pos condition, Option.some.injEq]
                        dsimp [fullHeader, makeHeader] at *
                        rw [timesFour, ← BitVec.shiftLeft_add, addShift, headerBase]
                        simp [BitVec.or_assoc]
                      let payload := rest ++ (previous.drop start).take len
                      let payloadWords := newTail ++ copiedWords
                      let remainingRoots := joinEnv cut.locals
                        (sptToAList (sptInter allocatedTarget.locals (adjustSet cut.locals))) ++
                        [(theGlobal allocatedSource.global, holFapply allocatedTarget.store .globals)] ++
                        flatStack allocatedSource.stack allocatedTarget.stack
                      have payloadLen : payload.length = rest.length + len := by
                        simp only [payload, List.length_append, List.length_take, List.length_drop]
                        omega
                      have payloadWordsLen : payloadWords.length = rest.length + len := by
                        simp [payloadWords, copiedLength, ← newLength]
                      have payloadNonempty : payload ≠ [] := by
                        intro empty
                        simp [empty] at payloadLen
                        omega
                      obtain ⟨returnedFree, returnedCurr, _, freeEq, currEq, consStep⟩ :=
                        memoryRel_consAlt (β := Unit) conf allocatedTarget.be (holThe allocatedSource.tstamps)
                          allocatedSource.refs allocatedSource.space allocatedTarget.store copiedMemory allocatedTarget.mdomain
                          payload payloadWords remainingRoots tag fullHeader
                          (by simpa [payload, payloadWords, remainingRoots, List.append_assoc] using copiedRel)
                          (by omega) payloadNonempty (by simpa [payloadWordsLen] using fullEncoded)
                          (by simp [allocatedSource, payloadWordsLen]) goodWidth
                      have sameFree : returnedFree = nextFree := by
                        rw [nextFreeRead] at freeEq
                        exact (WordLocW.word.inj (Option.some.inj freeEq)).symm
                      have sameCurr : returnedCurr = currentHeap := by
                        rw [currentHeapRead] at currEq
                        exact (WordLocW.word.inj (Option.some.inj currEq)).symm
                      subst returnedFree
                      subst returnedCurr
                      have finalMemory := consStep (by simpa [payloadWords] using copiedSpace)
                      have hasRealAddress : ∃ address, getRealAddr conf allocatedTarget.store pointer = some address := by
                        simp only [getRealAddr, currentHeapRead]
                        split <;> (try split) <;> exact ⟨_, rfl⟩
                      obtain ⟨realAddress, realAddressEq⟩ := hasRealAddress
                      have afterAddressEq : getRealAddr conf after13.store pointer = some realAddress := by
                        simpa [getRealAddr, currAfter, currentHeapRead] using realAddressEq
                      have evalBeforeActual := Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.getRealAddr_lemma
                        conf (adjustVar a1) allocatedTarget pointer realAddress
                        ⟨shiftBound', goodWidth, newPointer, realAddressEq⟩
                      have evalAfterActual := Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.getRealAddr_lemma
                        conf (adjustVar a1) after13 pointer realAddress
                        ⟨shiftBound', goodWidth, pointerAfter, afterAddressEq⟩
                      have realBeforeEq : realBefore = realAddress := by
                        rw [realBeforeEval] at evalBeforeActual
                        exact WordLocW.word.inj (Option.some.inj evalBeforeActual)
                      have realValueEq : realValue = realAddress := by
                        rw [realEval] at evalAfterActual
                        exact WordLocW.word.inj (Option.some.inj evalAfterActual)
                      have shiftStart : (BitVec.ofNat width (4 * start) <<< (wordShiftAmount width - 2)) =
                          wordSemBytesInWord * BitVec.ofNat width start := by
                        rcases goodWidth with h | h <;> subst width <;>
                          apply BitVec.eq_of_toNat_eq <;>
                          simp [wordShiftAmount, wordSemBytesInWord, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
                            BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]; omega
                      have shiftTotal : (BitVec.ofNat width (rest.length + len) <<< wordShiftAmount width) =
                          wordSemBytesInWord * BitVec.ofNat width (rest.length + len) := by
                        rcases goodWidth with h | h <;> subst width <;>
                          apply BitVec.eq_of_toNat_eq <;>
                          simp [wordShiftAmount, wordSemBytesInWord, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
                            BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]
                      have sourceAddressEq : sourceAddress = realBefore + StackRemove.bytesInWord width +
                          StackRemove.bytesInWord width * BitVec.ofNat width start := by
                        simp [sourceAddress, shiftStart, realBeforeEq, realValueEq,
                          wordSemBytesInWord, StackRemove.bytesInWord]
                      have destAddressEq : destAddress = nextFree + StackRemove.bytesInWord width *
                          BitVec.ofNat width (newTail.length + 1) := by
                        have lengths : tail.length = newTail.length := by omega
                        simp [destAddress, lengths, wordSemBytesInWord, StackRemove.bytesInWord]
                      have nextAddressEq : nextAddress = nextFree + wordSemBytesInWord *
                          BitVec.ofNat width (payloadWords.length + 1) := by
                        dsimp only [nextAddress]
                        rw [shiftTotal, payloadWordsLen, BitVec.ofNat_add, BitVec.mul_add]
                        simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, BitVec.add_comm]
                        ac_rfl
                      have cutShape := cutStateOpt_some_eq live source cut cutEq
                      have nextFields : ∃ safe peak, next =
                          { cut with space := 0, safeForSpace := safe, peakHeapLength := peak } := by
                        simp only [DataSem.doSpace, DataLang.opSpaceReset, ↓reduceIte,
                          Option.some.injEq] at spaceRun
                        exact ⟨_, _, spaceRun.symm⟩
                      obtain ⟨nextSafe, nextPeak, nextShape⟩ := nextFields
                      have resultValue : result = .block timestamp tag payload := by
                        simpa [payload] using auxRun.1.symm
                      let finalTarget := { allocatedTarget with
                        store := allocatedTarget.store.update (.nextFree, .word nextAddress), memory := copiedMemory }
                      have finalRoot : memoryRel conf finalTarget.be (holThe resultState.tstamps) resultState.refs
                          resultState.space finalTarget.store finalTarget.memory finalTarget.mdomain
                          ((result, Build.makeConsPtr conf (nextFree - currentHeap) tag (rest.length + len)) ::
                            (joinEnv resultState.locals (sptToAList (sptInter finalTarget.locals (adjustSet resultState.locals))) ++
                              [(theGlobal resultState.global, holFapply finalTarget.store .globals)] ++
                              flatStack resultState.stack finalTarget.stack)) := by
                        rw [resultValue, ← auxRun.2]
                        simpa [finalTarget, remainingRoots, allocatedSource, payloadWordsLen, nextAddressEq,
                          DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe, nextShape, cutShape,
                          timestampEq, holThe, holFapply, HolFiniteMapExact.update, FUPDATE] using finalMemory
                      have finalBase := memoryRel_tl conf finalTarget.be (holThe resultState.tstamps) resultState.refs
                        resultState.space finalTarget.store finalTarget.memory finalTarget.mdomain _ _ finalRoot
                      have resultLocals : resultState.locals = cut.locals := by
                        rw [← auxRun.2]
                        simp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe, nextShape]
                      have finalRelated : stateRel conf l1 l2 resultState finalTarget none locs := by
                        rcases allocatedRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                          htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, _⟩
                        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hgood, hshift, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hffi
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hclock
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hhandler
                        · exact hgc
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hcode
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource, codeOracleRel,
                            HolFiniteMapExact.update, FUPDATE] using horacle
                        · simp [← auxRun.2, DataSem.checkLim]
                        · simpa [finalTarget, HolFiniteMapExact.update, FUPDATE] using hglobal
                        · exact hzero
                        · intro k found
                          rw [resultLocals] at found
                          cases lookup : sptLookup k cut.locals with
                          | none => simp [lookup] at found
                          | some value =>
                            have wideFound := subLookup k value lookup
                            apply hpresent k
                            simp [allocatedSource, wideFound]
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hstack
                        · exact hlocs
                        · exact hacc
                        · rw [← auxRun.2]
                          dsimp [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe]
                          rw [nextStackMax, cutStackMax, BackendProps.optionLe_max_right]
                          exact Or.inl hmax
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hsizes
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource] using hlocals
                        · simpa [finalTarget, ← auxRun.2, DataSem.checkLim, prepared, DataSem.doStack,
                            DataSem.doLimSafe, nextShape, cutShape, allocatedSource, limitsInv,
                            HolFiniteMapExact.update, FUPDATE] using hlim
                        · simpa [finalTarget] using finalBase
                      let resultPointer := Build.makeConsPtr conf (nextFree - currentHeap) tag (rest.length + len)
                      let oddLocals := sptInsert 11 (.word sourceAddress) (sptInsert 13 (.word destAddress)
                          (sptInsert 15 (.word (BitVec.ofNat width (4 * len))) (sptInsert 3 resultPointer
                            (sptInsert 9 (.word (BitVec.ofNat width tag))
                              (sptInsert 7 (.word (BitVec.ofNat width (rest.length + len)))
                                (sptInsert 5 (.word fullHeader) (sptInsert 1 (.word nextFree) finalTarget.locals)))))))
                      let finalOdd := { finalTarget with locals := oddLocals }
                      have oddRelated : stateRel conf l1 l2 resultState finalOdd none locs := by
                        have addOdd (t : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width)
                            (odd : k % 2 = 1) (h : stateRel conf l1 l2 resultState t none locs) :
                            stateRel conf l1 l2 resultState (t.setVar k v) none locs := by
                          exact (stateRel_insertOdd conf l1 l2 resultState t none locs k v odd).mpr h
                        let s1 := finalTarget.setVar 1 (.word nextFree)
                        let s5 := s1.setVar 5 (.word fullHeader)
                        let s7 := s5.setVar 7 (.word (BitVec.ofNat width (rest.length + len)))
                        let s9 := s7.setVar 9 (.word (BitVec.ofNat width tag))
                        let s3 := s9.setVar 3 resultPointer
                        let s15 := s3.setVar 15 (.word (BitVec.ofNat width (4 * len)))
                        let s13 := s15.setVar 13 (.word destAddress)
                        have r1 := addOdd finalTarget 1 (.word nextFree) (by decide) finalRelated
                        have r5 := addOdd s1 5 (.word fullHeader) (by decide) r1
                        have r7 := addOdd s5 7 (.word (BitVec.ofNat width (rest.length + len))) (by decide) r5
                        have r9 := addOdd s7 9 (.word (BitVec.ofNat width tag)) (by decide) r7
                        have r3 := addOdd s9 3 resultPointer (by decide) r9
                        have r15 := addOdd s3 15 (.word (BitVec.ofNat width (4 * len))) (by decide) r3
                        have r13 := addOdd s15 13 (.word destAddress) (by decide) r15
                        have r11 := addOdd s13 11 (.word sourceAddress) (by decide) r13
                        simpa [finalOdd, oddLocals, s13, s15, s3, s9, s7, s5, s1,
                          WordSemStateFiniteExact.setVar] using r11
                      have oddRoot : memoryRel conf finalOdd.be (holThe resultState.tstamps) resultState.refs
                          resultState.space finalOdd.store finalOdd.memory finalOdd.mdomain
                          ((result, resultPointer) ::
                            (joinEnv resultState.locals (sptToAList (sptInter finalOdd.locals (adjustSet resultState.locals))) ++
                              [(theGlobal resultState.global, holFapply finalOdd.store .globals)] ++
                              flatStack resultState.stack finalOdd.stack)) := by
                        simpa [finalOdd, oddLocals, resultPointer, inter_insertOdd_adjustSet] using finalRoot
                      have finalDestRel := Flapjack.Compiler.Backend.DataToWord.Proofs.stateRel_insertRoot
                        conf l1 l2 resultState finalOdd locs dest result resultPointer oddRelated oddRoot
                      by_cases zero : len = 0
                      · have copiedSame : copiedMemory = storedMemory := by
                          simpa [zero, memcopy] using copiedRun.symm
                        have storesEqual : allocatedTarget.store.updateEq (.nextFree, .word nextAddress) =
                            allocatedTarget.store.update (.nextFree, .word nextAddress) := by
                          apply HolFiniteMapExact.ext_lookup
                          intro key
                          by_cases h : key = .nextFree
                          · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h]
                          · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h, Ne.symm h]
                        have targetSame : after11 = finalOdd := by
                          simp [after11, after13, after15, afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                            finalOdd, oddLocals, finalTarget, resultPointer, copiedSame, storesEqual,
                            WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar]
                        have zeroRead : after11.getVar 15 = some (.word (BitVec.ofNat width 0)) := by
                          simp [after11, after13, after15, WordSemStateFiniteExact.getVar,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne,
                            sptLookup_sptInsert_same, zero]
                        have pointerRead : after11.getVar 3 = some resultPointer := by
                          simp [after11, after13, after15, afterNext, ptrTarget, resultPointer,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have evalZero : WordSemStateFiniteExact.evaluate
                            (.ite .test 15 (.reg 15) (.assign (adjustVar dest) (.var 3))
                              (.mustTerminate (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
                                (some memCopyLocation) [15, 11, 13, 3] none))) after11 =
                            (none, after11.setVar (adjustVar dest) resultPointer) := by
                          have cmp : wordSemWordCmp .test (.word (0 : BitVec width)) (.word (0 : BitVec width)) =
                              some true := by
                            simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, AndOp.and]
                          rw [WordSemStateFiniteExact.evaluate]
                          simp only [WordSemStateFiniteExact.getVarImm, zeroRead]
                          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, AndOp.and]
                          rw [WordSemStateFiniteExact.evaluate]
                          simp [WordSemStateFiniteExact.wordExp, pointerRead]
                        refine ⟨none, after11.setVar (adjustVar dest) resultPointer, ?_, ?_, ?_⟩
                        · exact evalZero
                        · simp
                        · intro _
                          exact ⟨by simpa [targetSame] using finalDestRel, rfl⟩
                      · have stubMember : (memCopyLocation, 5, memCopyCode) ∈ stubs (width := width) conf := by
                          simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
                            fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
                            replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
                            divLocation, modLocation, compare1Location, compareLocation, equal1Location,
                            equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
                            byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
                            installLocation, installCodeLocation, installDataLocation, dummyLocation,
                            appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
                            unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
                        have codeRead : sptLookup memCopyLocation allocatedTarget.code = some (5, memCopyCode) := by
                          exact allocatedRel.2.2.2.2.1.2.1 _ stubMember
                        obtain ⟨gcCut, gcCutRun⟩ := cutEnv_imp_wordCutEnv conf l1 l2 allocatedSource
                          allocatedTarget locs live cut.locals ⟨allocatedRel, wideNarrow⟩
                        have afterCutRun : wordSemCutEnv (adjustSets live) after11.locals = some gcCut := by
                          simpa [after11, after13, after15, afterNext, ptrTarget, storedTarget, tD, tC, tB, tA,
                            WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar,
                            cutEnv_adjustSets_insertOdd] using gcCutRun
                        obtain ⟨env1, env2, envRun, envEq⟩ :=
                          cutEnv_imp_cutEnvs (adjustSets live) after11.locals gcCut afterCutRun
                        have lenWordBound : 4 * len < 2 ^ width := by omega
                        have enoughClock : len ≤ wordSemMustTerminateLimit width - 1 := by
                          dsimp [wordSemMustTerminateLimit]
                          omega
                        have callRead15 : after11.getVar 15 = some (.word (BitVec.ofNat width (4 * len))) := by
                          simp [after11, after13, after15, WordSemStateFiniteExact.getVar,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have callRead11 : after11.getVar 11 = some (.word sourceAddress) := by
                          simp [after11, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_same]
                        have callRead13 : after11.getVar 13 = some (.word destAddress) := by
                          simp [after11, after13, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have callRead3 : after11.getVar 3 = some resultPointer := by
                          simp [after11, after13, after15, afterNext, ptrTarget, resultPointer,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have callArgs : WordSemStateFiniteExact.getVars [15, 11, 13, 3] after11 =
                            some [.word (BitVec.ofNat width (4 * len)), .word sourceAddress,
                              .word destAddress, resultPointer] := by
                          simp [WordSemStateFiniteExact.getVars, callRead15, callRead11, callRead13, callRead3]
                        let mustState := { after11 with clock := wordSemMustTerminateLimit width, termdep := after11.termdep - 1 }
                        let callInputs := [.loc n l, .word (BitVec.ofNat width (4 * len)), .word sourceAddress,
                          .word destAddress, resultPointer]
                        let callSize := sptLookup memCopyLocation mustState.stackSize
                        let entry := WordSemStateFiniteExact.callEnv callInputs callSize
                          (WordSemStateFiniteExact.pushEnv (env1, env2) none (WordSemStateFiniteExact.decClock mustState))
                        have copyAtAddresses : memcopy len sourceAddress destAddress storedMemory
                            allocatedTarget.mdomain = some copiedMemory := by
                          simpa [sourceAddressEq, destAddressEq] using copiedRun
                        have entryPremises : memcopy len sourceAddress destAddress storedMemory
                              allocatedTarget.mdomain = some copiedMemory ∧
                            entry.memory = storedMemory ∧ entry.mdomain = allocatedTarget.mdomain ∧
                            sptLookup memCopyLocation entry.code = some (5, memCopyCode) ∧
                            len ≤ entry.clock ∧ 4 * len < 2 ^ width ∧
                            entry.getVar 0 = some (.loc n l) ∧
                            entry.getVar 2 = some (.word (BitVec.ofNat width (4 * len))) ∧
                            entry.getVar 4 = some (.word sourceAddress) ∧
                            entry.getVar 6 = some (.word destAddress) ∧ entry.getVar 8 = some resultPointer := by
                          refine ⟨copyAtAddresses, ?_, ?_, ?_, ?_, lenWordBound, ?_, ?_, ?_, ?_, ?_⟩
                          · simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, mustState, after11, after13, after15, afterNext,
                              ptrTarget, storedTarget, tD, tC, tB, tA, WordSemStateFiniteExact.setVar,
                              WordSemStateFiniteExact.setStore]
                          · simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, mustState, after11, after13, after15, afterNext,
                              ptrTarget, storedTarget, tD, tC, tB, tA, WordSemStateFiniteExact.setVar,
                              WordSemStateFiniteExact.setStore]
                          · simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, mustState, after11, after13, after15, afterNext,
                              ptrTarget, storedTarget, tD, tC, tB, tA, WordSemStateFiniteExact.setVar,
                              WordSemStateFiniteExact.setStore] using codeRead
                          · simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, mustState] using enoughClock
                          all_goals simp [entry, WordSemStateFiniteExact.callEnv, callInputs,
                            WordSemStateFiniteExact.getVar, sptFromList2, sptInsert, sptLookup]
                        obtain ⟨calleeStackMax, calleeRun, calleeStackBound⟩ := memCopy_correct resultPointer n l len
                          sourceAddress destAddress entry storedMemory allocatedTarget.mdomain copiedMemory entryPremises
                        have maxStable (a b : Option Nat) :
                            Option.map₂ max (Option.map₂ max a b) b = Option.map₂ max a b := by
                          cases a <;> cases b <;> simp
                        have entryMaxStable : Option.map₂ max entry.stackMax
                            (Option.map₂ (· + ·) (wordSemStackSize entry.stack)
                              (sptLookup memCopyLocation entry.stackSize)) = entry.stackMax := by
                          have pushedSize : (WordSemStateFiniteExact.pushEnv (env1, env2) none
                              (WordSemStateFiniteExact.decClock mustState)).stackSize = mustState.stackSize := by
                            cases h : wordSemEnvToList env2 mustState.permute with
                            | mk entries permutation =>
                              simp [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, h]
                          simp only [entry, WordSemStateFiniteExact.callEnv, callSize, pushedSize]
                          cases h1 : (WordSemStateFiniteExact.pushEnv (env1, env2) none
                              (WordSemStateFiniteExact.decClock mustState)).stackMax <;>
                            cases h2 : wordSemStackSize (WordSemStateFiniteExact.pushEnv (env1, env2) none
                              (WordSemStateFiniteExact.decClock mustState)).stack <;>
                            cases h3 : sptLookup memCopyLocation mustState.stackSize <;>
                            simp [wordSemOptionMax, wordSemOptionAdd]
                        have calleeMaxLower := WordSemStateFiniteExact.evaluate_stack_max_le memCopyCode entry
                          (some (.result (.loc n l) [resultPointer])) _ calleeRun
                        have calleeMaxEqual : calleeStackMax = entry.stackMax := by
                          have upper : optionLe calleeStackMax entry.stackMax := by
                            simpa [entryMaxStable] using calleeStackBound
                          have lower : optionLe entry.stackMax calleeStackMax := by
                            simpa using calleeMaxLower
                          have antisymm (x y : Option Nat) (hxy : optionLe x y) (hyx : optionLe y x) : x = y := by
                            cases x <;> cases y <;> simp [optionLe] at hxy hyx ⊢
                            exact Nat.le_antisymm hxy hyx
                          exact antisymm _ _ upper lower
                        cases envList : wordSemEnvToList env2 mustState.permute with
                        | mk entries permutation =>
                          have cutsWf := cutEnvs_wf (adjustSets live) after11.locals env1 env2 envRun
                          have firstRestore : sptFromAList (sptToAList env1) = env1 := by
                            apply (sptEqThm _ _ ⟨sptWfFromAList _, cutsWf.1⟩).2
                            intro key
                            exact sptLookup_sptFromAList_sptToAList key env1
                          have secondRestore : sptFromAList entries = env2 := by
                            apply (sptEqThm _ _ ⟨sptWfFromAList _, cutsWf.2⟩).2
                            intro key
                            rw [sptLookup_sptFromAList]
                            exact (wordSemEnvToListLookupEquiv env2 mustState.permute entries permutation envList).1 key
                          let returned := { entry with clock := entry.clock - len, memory := copiedMemory, locals := .ln, localsSize := some 0, stackMax := calleeStackMax }
                          let restored := { returned with
                            locals := sptUnion (sptFromAList entries) (sptFromAList (sptToAList env1))
                            stack := mustState.stack
                            localsSize := mustState.localsSize }
                          have popRun : WordSemStateFiniteExact.popEnv returned = some restored := by
                            simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
                              WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv,
                              WordSemStateFiniteExact.decClock, envList]
                          have restoredDomain : sptDomainEqUnion restored.locals env1 env2 := by
                            intro key
                            change sptMem key (sptUnion (sptFromAList entries) (sptFromAList (sptToAList env1))) ↔ _
                            rw [secondRestore, firstRestore, sptMem_sptUnion]
                            exact or_comm
                          have narrowSelf : DataSem.cutEnv live resultState.locals = some resultState.locals := by
                            rw [resultLocals]
                            exact cutEnv_idempotent live source.locals cut.locals narrowRun
                          have finalCutRun : wordSemCutEnv (adjustSets live) finalTarget.locals = some gcCut := by
                            simpa [finalTarget] using gcCutRun
                          have finalCutRel : stateRel conf l1 l2 resultState { finalTarget with locals := gcCut } none locs := by
                            simpa using stateRel_cutEnv_cutEnv conf l1 l2 resultState finalTarget locs live
                              resultState.locals gcCut ⟨finalRelated, narrowSelf, finalCutRun⟩
                          have cutNames : ∀ key, sptMem key resultState.locals → sptMem key live := by
                            intro key present
                            obtain ⟨value, found⟩ := (sptMem_iff_lookup key resultState.locals).mp present
                            have cutRun := narrowSelf
                            unfold DataSem.cutEnv at cutRun
                            split at cutRun
                            · simp only [Option.some.injEq] at cutRun
                              conv at found => rw [← cutRun]
                              rw [sptLookup_mkWf, sptLookup_sptInterCases] at found
                              cases h : sptLookup key live with
                              | none => simp [h] at found
                              | some entry => exact (sptMem_iff_lookup key live).mpr ⟨entry, h⟩
                            · contradiction
                          have wordCutEq : gcCut = sptUnion (sptInter finalTarget.locals (adjustSet live))
                              (sptInter finalTarget.locals (.ls ())) := by
                            have wordRun := finalCutRun
                            by_cases h1 : LoopSemStateFiniteExact.sptSubsetLive (.ls ()) finalTarget.locals <;>
                              by_cases h2 : LoopSemStateFiniteExact.sptSubsetLive (adjustSet live) finalTarget.locals <;>
                              simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, adjustSets, h1, h2] at wordRun
                            exact wordRun.symm
                          have cutLookup : ∀ key, sptMem key (adjustSet live) →
                              sptLookup key gcCut = sptLookup key finalTarget.locals := by
                            intro key member
                            obtain ⟨value, found⟩ := (sptMem_iff_lookup key (adjustSet live)).mp member
                            rw [wordCutEq, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases]
                            cases sptLookup key finalTarget.locals <;> simp [found]
                          have rootsEq : sptInter gcCut (adjustSet resultState.locals) =
                              sptInter finalTarget.locals (adjustSet resultState.locals) := by
                            apply (sptEqThm _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩).2
                            intro key
                            rw [sptLookup_sptInterCases, sptLookup_sptInterCases]
                            cases lookup : sptLookup key (adjustSet resultState.locals) with
                            | none => simp
                            | some value =>
                              have member := (sptMem_iff_lookup key (adjustSet resultState.locals)).mpr ⟨value, lookup⟩
                              obtain ⟨name, eq, present⟩ := (adjustSet_domain resultState.locals key).mp member
                              have kept := (adjustSet_domain live key).mpr ⟨name, eq, cutNames name present⟩
                              rw [cutLookup key kept]
                          have cutRoot : memoryRel conf finalTarget.be (holThe resultState.tstamps) resultState.refs
                              resultState.space finalTarget.store finalTarget.memory finalTarget.mdomain
                              ((result, resultPointer) ::
                                (joinEnv resultState.locals (sptToAList (sptInter gcCut (adjustSet resultState.locals))) ++
                                  [(theGlobal resultState.global, holFapply finalTarget.store .globals)] ++
                                  flatStack resultState.stack finalTarget.stack)) := by
                            simpa [rootsEq, resultPointer] using finalRoot
                          have cutDestRel := Flapjack.Compiler.Backend.DataToWord.Proofs.stateRel_insertRoot
                            conf l1 l2 resultState { finalTarget with locals := gcCut } locs dest result resultPointer
                            finalCutRel cutRoot
                          have firstLive : ¬ sptDomainEmpty (adjustSets live).1 := by
                            intro empty
                            have absent := empty 0
                            exact absent (by simp [adjustSets, sptMem, sptDomain, sptLookup])
                          have mustClock : mustState.clock ≠ 0 := by
                            simp only [mustState]
                            omega
                          have argsMust : WordSemStateFiniteExact.getVars [15, 11, 13, 3] mustState =
                              some [.word (BitVec.ofNat width (4 * len)), .word sourceAddress,
                                .word destAddress, resultPointer] := by
                            simpa [mustState, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar] using callArgs
                          have codeMust : sptLookup memCopyLocation mustState.code = some (5, memCopyCode) := by
                            simpa [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore] using codeRead
                          have envMust : wordSemCutEnvs (adjustSets live) mustState.locals = some (env1, env2) := by
                            simpa [mustState] using envRun
                          have directCall : WordSemStateFiniteExact.evaluate
                              (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
                                (some memCopyLocation) [15, 11, 13, 3] none) mustState =
                              (none, WordSemStateFiniteExact.setVars [adjustVar dest] [resultPointer] restored) := by
                            rw [WordSemStateFiniteExact.evaluate]
                            simp only [argsMust, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
                              wordSemFindCode, codeMust, List.length_cons, List.length_nil, if_true, firstLive,
                              not_false_eq_true, List.nodup_cons, List.mem_nil_iff, not_false_eq_true, envMust, mustClock]
                            simp only [List.nodup_nil, true_and, not_true_eq_false, false_or, if_false]
                            rw [WordSemStateFiniteExact.fix_clock_evaluate]
                            simp only [dif_neg, not_false_eq_true]
                            have directCallee : WordSemStateFiniteExact.evaluate memCopyCode
                                (WordSemStateFiniteExact.callEnv
                                  [.loc n l, .word (BitVec.ofNat width (4 * len)), .word sourceAddress,
                                    .word destAddress, resultPointer] (sptLookup memCopyLocation mustState.stackSize)
                                  (WordSemStateFiniteExact.pushEnv (env1, env2) none
                                    (WordSemStateFiniteExact.decClock mustState))) =
                                (some (.result (.loc n l) [resultPointer]), returned) := by
                              simpa [entry, callInputs, callSize, returned] using calleeRun
                            rw [directCallee]
                            simp only [List.length_cons, List.length_nil]
                            change (match WordSemStateFiniteExact.popEnv returned with | _ => _) = _
                            rw [popRun]
                            simp [restoredDomain, WordSemStateFiniteExact.evaluate]
                          let finalCallState := { WordSemStateFiniteExact.setVars [adjustVar dest] [resultPointer] restored with
                            clock := after11.clock, termdep := after11.termdep }
                          have nonzeroDepth : after11.termdep ≠ 0 := by
                            have h : after11.termdep = allocatedTarget.termdep := by
                              simp [after11, after13, after15, afterNext, ptrTarget, storedTarget,
                                tD, tC, tB, tA, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                            omega
                          have terminateCall : WordSemStateFiniteExact.evaluate
                              (.mustTerminate (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
                                (some memCopyLocation) [15, 11, 13, 3] none)) after11 =
                              (none, finalCallState) := by
                            rw [WordSemStateFiniteExact.evaluate]
                            simp only [nonzeroDepth]
                            rw [directCall]
                            rfl
                          have nonzeroWord : BitVec.ofNat width (4 * len) ≠ 0 := by
                            intro h
                            have natEq := congrArg BitVec.toNat h
                            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lenWordBound] at natEq
                            omega
                          have testFalse : wordSemWordCmp .test (.word (BitVec.ofNat width (4 * len)))
                              (.word (BitVec.ofNat width (4 * len))) = some false := by
                            simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, AndOp.and]
                            intro h
                            apply nonzeroWord
                            simpa using h
                          have nonzeroBranch : WordSemStateFiniteExact.evaluate
                              (.ite .test 15 (.reg 15) (.assign (adjustVar dest) (.var 3))
                                (.mustTerminate (.call (some ([adjustVar dest], adjustSets live, .skip, n, l))
                                  (some memCopyLocation) [15, 11, 13, 3] none))) after11 =
                              (none, finalCallState) := by
                            rw [WordSemStateFiniteExact.evaluate]
                            simp only [WordSemStateFiniteExact.getVarImm, callRead15, testFalse]
                            exact terminateCall
                          let usage := Option.map₂ (· + ·) (wordSemStackSize finalTarget.stack) finalTarget.localsSize
                          have baseStack : mustState.stack = finalTarget.stack := by
                            simp [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, finalTarget, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                          have baseSize : mustState.localsSize = finalTarget.localsSize := by
                            simp [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, finalTarget, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                          have baseFrames : mustState.stackSize = finalTarget.stackSize := by
                            simp [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, finalTarget, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                          have baseMax : mustState.stackMax = finalTarget.stackMax := by
                            simp [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, finalTarget, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                          have pushedStack : wordSemStackSize (WordSemStateFiniteExact.pushEnv (env1, env2) none
                              (WordSemStateFiniteExact.decClock mustState)).stack = usage := by
                            simp only [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock,
                              envList, wordSemStackSize, List.foldr_cons, wordSemStackSizeFrame, baseSize, baseStack]
                            change wordSemOptionAdd finalTarget.localsSize (wordSemStackSize finalTarget.stack) = usage
                            dsimp only [usage]
                            cases finalTarget.localsSize <;> cases wordSemStackSize finalTarget.stack <;>
                              simp [wordSemOptionAdd, Nat.add_comm]
                          have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
                            cases x <;> cases y <;> rfl
                          have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
                            cases x <;> cases y <;> rfl
                          have entryMaxEq : entry.stackMax = Option.map₂ max
                              (Option.map₂ max finalTarget.stackMax usage)
                              (Option.map₂ (· + ·) usage (sptLookup memCopyLocation finalTarget.stackSize)) := by
                            simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, envList, callSize, baseFrames, baseMax, optMax, optAdd]
                            rw [← pushedStack]
                            simp [WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, envList,
                              baseStack, baseSize, optMax]
                          have sourceStackEq : wordSemStackSize finalTarget.stack = DataSem.sizeOfStack source.stack := by
                            simpa [finalTarget, allocatedSource] using
                              stackRel_sizeOfStack allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have frameEq : finalTarget.stackSize = source.stackFrameSizes := by
                            simpa [finalTarget, allocatedSource] using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have sizeEq : finalTarget.localsSize = source.localsSize := by
                            simpa [finalTarget, allocatedSource] using allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have resultMaxEq : resultState.stackMax = Option.map₂ max source.stackMax
                              (Option.map₂ (· + ·) (sptLookup memCopyLocation finalTarget.stackSize) usage) := by
                            rw [← auxRun.2]
                            simp only [DataSem.checkLim, prepared, DataSem.doStack, DataSem.doLimSafe,
                              DataSem.stackConsumed, nextShape, cutShape]
                            simp [usage, frameEq, sizeEq, sourceStackEq]
                          have optionBound (a b c d : Option Nat) (h : optionLe a d) :
                              optionLe (Option.map₂ max (Option.map₂ max a b) (Option.map₂ (· + ·) b c))
                                (Option.map₂ max d (Option.map₂ (· + ·) c b)) := by
                            cases a <;> cases b <;> cases c <;> cases d <;> simp [optionLe] at h ⊢
                            all_goals omega
                          have oldMaxBound : optionLe finalTarget.stackMax source.stackMax := by
                            simpa [finalTarget, allocatedSource] using
                              allocatedRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                          have entryBound : optionLe entry.stackMax resultState.stackMax := by
                            rw [entryMaxEq, resultMaxEq]
                            exact optionBound finalTarget.stackMax usage
                              (sptLookup memCopyLocation finalTarget.stackSize) source.stackMax oldMaxBound
                          have usageBound : optionLe usage entry.stackMax := by
                            rw [entryMaxEq, BackendProps.optionLe_max_right, BackendProps.optionLe_max_right]
                            exact Or.inl (Or.inr (BackendProps.optionLe_refl _))
                          let cutWithStack := { finalTarget with locals := gcCut, stackMax := entry.stackMax }
                          have cutStackRel : stateRel conf l1 l2 resultState cutWithStack none locs := by
                            rcases finalCutRel with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
                              htstamp, hglobal, hzero, hpresent, hstack, hlocs, _, _, hsizes, hlocals, hlim, hmem⟩
                            exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
                              hzero, hpresent, hstack, hlocs, usageBound, entryBound, hsizes, hlocals, hlim, hmem⟩
                          have stackRoot : memoryRel conf cutWithStack.be (holThe resultState.tstamps) resultState.refs
                              resultState.space cutWithStack.store cutWithStack.memory cutWithStack.mdomain
                              ((result, resultPointer) ::
                                (joinEnv resultState.locals (sptToAList (sptInter cutWithStack.locals (adjustSet resultState.locals))) ++
                                  [(theGlobal resultState.global, holFapply cutWithStack.store .globals)] ++
                                  flatStack resultState.stack cutWithStack.stack)) := by
                            exact cutRoot
                          have stackDestRel := Flapjack.Compiler.Backend.DataToWord.Proofs.stateRel_insertRoot
                            conf l1 l2 resultState cutWithStack locs dest result resultPointer cutStackRel stackRoot
                          have storesEqual : allocatedTarget.store.updateEq (.nextFree, .word nextAddress) =
                              allocatedTarget.store.update (.nextFree, .word nextAddress) := by
                            apply HolFiniteMapExact.ext_lookup
                            intro key
                            by_cases h : key = .nextFree
                            · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h]
                            · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.update, FUPDATE_HOL, FUPDATE, h, Ne.symm h]
                          have finalCallShape : finalCallState =
                              { cutWithStack.setVar (adjustVar dest) resultPointer with permute := permutation } := by
                            simp [finalCallState, setVars_singleton, restored, returned, entry, callInputs, callSize,
                              WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                              WordSemStateFiniteExact.decClock, firstRestore, secondRestore, ← envEq,
                              calleeMaxEqual, mustState, after11, after13, after15, afterNext, ptrTarget,
                              storedTarget, tD, tC, tB, tA, finalTarget, cutWithStack,
                              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore, storesEqual]
                            simpa [mustState, after11, after13, after15, afterNext, ptrTarget, storedTarget,
                              tD, tC, tB, tA, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setStore]
                              using congrArg Prod.snd envList
                          have finalCallRel : stateRel conf l1 l2 (DataSem.setVar dest result resultState)
                              finalCallState none locs := by
                            rw [finalCallShape]
                            exact stackDestRel
                          refine ⟨none, finalCallState, nonzeroBranch, ?_, ?_⟩
                          · simp
                          · intro _
                            exact ⟨finalCallRel, rfl⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
