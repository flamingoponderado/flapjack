module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WriteBignum
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordShift64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.TagEq
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemoryLemmas
@[expose] public section

/-! Word64-to-integer conversion in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace WordToIntAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordToIntAssignmentWitness

private theorem wordToIntSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp .wordToInt) values source = .val (result, resultState)) :
    ∃ word next, values = [.word64 word] ∧ DataSem.consumeSpace 3 source = some next ∧
      result = .number (word.toNat : Int) ∧
      resultState = DataSem.doStack (.wordOp .wordToInt) values
        (DataSem.doLimSafe next (.wordOp .wordToInt) values) := by
  cases h : DataSem.consumeSpace 3 source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h] at run
  | some next =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons value rest =>
      cases rest with
      | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases value <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]

/-- Lowering the reserved space preserves the state relation. Flapjack proof
infrastructure; HOL applies `memory_rel_less_space` inline. -/
theorem stateRel_lessSpace {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (k : Nat)
    (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 {source with space := source.space - k} target none locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  exact ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim,
    memoryRel_lessSpace conf target.be _ _ source.space (source.space - k) _ _ _ _ ⟨hmem, by omega⟩⟩

/-- The header facts needed by `assign_WordToInt` follow from the source
limit check. Flapjack proof infrastructure; HOL derives them by contradiction
from `limits_inv_def` and `encode_header_def`. -/
theorem wordToIntHeaders {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    (∃ hd, encodeHeader (width := width) conf 3 1 = some hd) ∧
    (∀ vs, DataSem.limSafe source.limits (.wordOp .wordToInt) vs →
      ∃ hd, encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) = some hd) := by
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
  have lenPos : 0 < conf.lenSize := by
    have h := heapMem.2.2.2.1
    omega
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have limitEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
  have one : 1 < 2 ^ conf.lenSize := by
    have h : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rcases good with h | h <;> subst width
  · have three : 3 < 2 ^ (32 - conf.lenSize - 2) := by
      have h : 2 ^ 3 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine ⟨⟨makeHeader conf (BitVec.ofNat 32 3) 1, by simp [encodeHeader, one, three]⟩, ?_⟩
    intro vs safe
    have safeLen : 1 < conf.lenSize := by
      simp [DataSem.limSafe, limitEq] at safe
      exact safe
    have countBound : 2 < 2 ^ conf.lenSize := by
      have h : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    exact ⟨makeHeader conf (BitVec.ofNat 32 3) 2, by simp [encodeHeader, countBound, three]⟩
  · have three : 3 < 2 ^ (64 - conf.lenSize - 2) := by
      have h : 2 ^ 3 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have header : ∃ hd, encodeHeader (width := 64) conf 3 1 = some hd :=
      ⟨makeHeader conf (BitVec.ofNat 64 3) 1, by simp [encodeHeader, one, three]⟩
    exact ⟨header, fun _ _ => by simpa using header⟩

/-- A natural word is a small integer exactly when its top three bits are
clear. Flapjack arithmetic infrastructure for `assign_WordToInt`. -/
theorem smallInt_word_iff (k : Nat) [NeZero k] (hk : 3 ≤ k) (w : BitVec k) :
    smallInt k (w.toNat : Int) ↔ w >>> (k - 3) = 0 := by
  have pos : 2 ^ k / 8 = 2 ^ (k - 3) := by
    rw [show k = (k - 3) + 3 from by omega, Nat.pow_add]
    simp
  have toNatEq : (w >>> (k - 3)).toNat = w.toNat / 2 ^ (k - 3) := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have powPos : 0 < 2 ^ (k - 3) := Nat.two_pow_pos _
  have zero : (0 : BitVec k).toNat = 0 := by simp
  unfold smallInt
  simp only [Int.ofNat_eq_natCast, pos]
  constructor
  · rintro ⟨_, h⟩
    apply BitVec.eq_of_toNat_eq
    rw [toNatEq, zero]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    have := congrArg BitVec.toNat h
    rw [toNatEq, zero, Nat.div_eq_zero_iff] at this
    omega

/-- The tagged encoding of a natural word is its left shift by two.
Flapjack arithmetic infrastructure for `assign_WordToInt`. -/
theorem smallnum_word {k : Nat} [NeZero k] (w : BitVec k) :
    (smallnum (w.toNat : Int) : BitVec k) = w <<< (2 : Nat) := by
  unfold smallnum
  rw [if_neg (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have : (4 * (w.toNat : Int)).toNat = w.toNat * 2 ^ 2 := by omega
  rw [this]

/-- Word64-to-integer conversion satisfies the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordToInt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordToInt_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .wordOp .wordToInt)
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
  obtain ⟨word, next, valuesEq, spaceEq, resultEq, stateEq⟩ := wordToIntSource values source resultState result run
  subst values
  subst result
  subst resultState
  have argLen := DataSpace.getVars_length args source.locals [.word64 word] argsEq
  match args, argLen with
  | [arg], _ =>
  have nextEq : next = { source with space := source.space - 3 } := by
    unfold DataSem.consumeSpace at spaceEq
    split at spaceEq <;> simp_all
  subst next
  have spaceEnough : 3 ≤ source.space := by
    unfold DataSem.consumeSpace at spaceEq
    split at spaceEq <;> simp_all
  let spaced : DataSem.State C F := { source with space := source.space - 3 }
  let nextSource := DataSem.doStack (.wordOp .wordToInt) [.word64 word]
    (DataSem.doLimSafe spaced (.wordOp .wordToInt) [.word64 word])
  have nextRel : stateRel conf l1 l2 nextSource target none locs :=
    stateRel_doStack conf l1 l2 _ target locs _ _
      (stateRel_doLimSafe conf l1 l2 spaced target locs _ _
        (stateRel_lessSpace conf l1 l2 source target locs 3 related))
  obtain ⟨⟨hd1, header1⟩, headerOfSafe⟩ := wordToIntHeaders conf source target l1 l2 locs related
  let unspaced := DataSem.doStack (.wordOp .wordToInt) [.word64 word]
    (DataSem.doLimSafe source (.wordOp .wordToInt) [.word64 word])
  have unspacedRel : stateRel conf l1 l2 unspaced target none locs :=
    stateRel_doStack conf l1 l2 _ target locs _ _
      (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
  obtain ⟨words, getWords, lengthEq⟩ :=
    stateRel_getVars conf l1 l2 source target locs [arg] [.word64 word] related argsEq
  match words, lengthEq with
  | [loc], _ =>
  let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
    flatStack source.stack target.stack
  let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
  have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
    target.store target.memory target.mdomain target envs [arg] [.word64 word] [loc] (by
      refine ⟨?_, argsEq, getWords⟩
      simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have good := related.2.2.2.2.2.2.1
  have shiftBound := related.2.2.2.2.2.2.2.1
  have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
    cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
      simp_all [WordSemStateFiniteExact.getVars]
  have rootsRel : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.word64 word, loc) :: (locals ++ envs)) := by
    simpa [locals, envs, List.append_assoc] using roots
  have baseHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain (joinEnvLocals source.locals target.locals ++ envs) := by
    simpa [envs, joinEnvLocals] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have oldPresent : ∀ k, (sptLookup k source.locals).isSome →
      (sptLookup (adjustVar k) target.locals).isSome := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
    exact presentOld
  rcases good with width32 | width64
  · subst width
    cases header : encodeHeader (width := 32) conf 3 2 with
    | none =>
      obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
      have noSafe : ¬ DataSem.limSafe source.limits (.wordOp .wordToInt) [.word64 word] := by
        intro safe
        obtain ⟨hd, encoded⟩ := headerOfSafe _ safe
        simp only [show (32 = 64) = False by decide, if_false] at encoded
        rw [header] at encoded
        contradiction
      refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
      · simpa [compileAssign, arg1, assignWordToInt, header] using outEval
      · intro _
        refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
        · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
          simpa [nextSource, spaced, DataSem.doStack, DataSem.doLimSafe] using targetBound
        · intro _
          simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
      · simp
    | some hd =>
    obtain ⟨index, addr, originalHeader, locEq, realAddrEq, domainHeader, headerWord,
      bit3, bit4, bit2, domainFirst, payload⟩ :=
        memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
          target.store target.memory target.mdomain word loc (locals ++ envs)
          ⟨rootsRel, Or.inl rfl⟩
    simp only [show 32 < 64 by decide, ↓reduceIte] at payload
    obtain ⟨payloadHigh, domainSecond, payloadLow, _, _⟩ := payload
    have pointerRead : WordSemStateFiniteExact.getVar (adjustVar arg) target =
        some (.word (getAddr conf index (.word 0))) := by simpa [locEq] using locRead
    have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target
      (getAddr conf index (.word 0)) addr ⟨shiftBound, Or.inl rfl, pointerRead, realAddrEq⟩
    let high : BitVec 32 := (word >>> (32 : Nat)).setWidth 32
    let low : BitVec 32 := word.setWidth 32
    have wordEq : word.toNat = high.toNat * 2 ^ 32 + low.toNat := by
      simp only [high, low, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have := word.isLt
      have h1 : word.toNat / 2 ^ 32 < 2 ^ 32 := by omega
      rw [Nat.mod_eq_of_lt h1]
      omega
    have compiled : (compileAssign (width := 32) conf n l dest (.wordOp .wordToInt) [arg] none).1 =
        wordListSeq [
          .assign 15 (realAddr conf (adjustVar arg)),
          .assign 13 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
          .assign 11 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
          .ite .notEqual 13 (.imm 0) (writeWord64On32 conf hd dest 13 11)
            (wordListSeq [
              .assign 1 (shiftN .lsr (.var 11) 29),
              .ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 11) 2))
                (writeWord32On32 conf hd1 dest 11)])] := by
      simp [compileAssign, arg1, assignWordToInt, header, header1]
    let mid := ((target.setVar 15 (.word addr)).setVar 13 (.word high)).setVar 11 (.word low)
    have loads : WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 15 (realAddr conf (adjustVar arg)),
        .assign 13 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
        .assign 11 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)]))]) target = (none, mid) := by
      have domain1 : target.mdomain (addr + wordSemBytesInWord) = true := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainFirst
      have domain2 : target.mdomain (addr + 2 * wordSemBytesInWord) = true := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainSecond
      have load1 : target.memory (addr + wordSemBytesInWord) = .word high := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh
      have load2 : target.memory (addr + 2 * wordSemBytesInWord) = .word low := by
        simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow
      simp only [BitVec.ofNat_eq_ofNat] at domain2 load2
      simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
        wordOpHOL, wordOp, theWords, realEval, domain1, domain2, load1, load2,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, mid]
    let inner : WordLangProgHOL (BitVec 32) := wordListSeq [
      .assign 1 (shiftN .lsr (.var 11) 29),
      .ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 11) 2))
        (writeWord32On32 conf hd1 dest 11)]
    have joined := evalListAppend [
        .assign 15 (realAddr conf (adjustVar arg)),
        .assign 13 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
        .assign 11 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)]))]
      (.ite .notEqual 13 (.imm 0) (writeWord64On32 conf hd dest 13 11) inner) target mid loads
    simp only [List.cons_append, List.nil_append] at joined
    have get13 : WordSemStateFiniteExact.getVar 13 mid = some (.word high) := by
      simp [mid, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
    have get11 : WordSemStateFiniteExact.getVar 11 mid = some (.word low) := by
      simp [mid, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same]
    have midHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
        mid.store mid.memory mid.mdomain (joinEnvLocals source.locals mid.locals ++ envs) := by
      simpa [mid, WordSemStateFiniteExact.setVar,
        joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
          related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have midPresent : ∀ k, (sptLookup k source.locals).isSome →
        (sptLookup (adjustVar k) mid.locals).isSome := by
      intro k present
      have odd11 : adjustVar k ≠ 11 := by simp [adjustVar]; omega
      have odd13 : adjustVar k ≠ 13 := by simp [adjustVar]; omega
      have odd15 : adjustVar k ≠ 15 := by simp [adjustVar]; omega
      simpa [mid, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ odd11,
        sptLookup_sptInsert_ne _ _ _ _ odd13, sptLookup_sptInsert_ne _ _ _ _ odd15] using
          oldPresent k present
    by_cases highZero : high = 0
    · have lowEq : word.toNat = low.toNat := by
        rw [wordEq, highZero]; simp
      let pre := mid.setVar 1 (.word (low >>> 29))
      have innerRun : WordSemStateFiniteExact.evaluate (wordListSeq [.assign 1 (shiftN .lsr (.var 11) 29)]) mid =
          (none, pre) := by
        simp [wordListSeq, WordSemStateFiniteExact.evaluate, shiftN, WordSemStateFiniteExact.wordExp,
          get11, wordShiftHOL, pre]
      have innerJoined := evalListAppend [.assign 1 (shiftN .lsr (.var 11) 29)]
        (.ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 11) 2))
          (writeWord32On32 conf hd1 dest 11)) mid pre innerRun
      simp only [List.cons_append, List.nil_append] at innerJoined
      have get1 : WordSemStateFiniteExact.getVar 1 pre = some (.word (low >>> 29)) := by
        simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      have get11' : WordSemStateFiniteExact.getVar 11 pre = some (.word low) := by
        simp [pre, mid, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
      have outer : WordSemStateFiniteExact.evaluate
          (compileAssign (width := 32) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
          WordSemStateFiniteExact.evaluate inner mid := by
        rw [compiled, joined]
        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get13]
        split
        · rename_i h
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq,
            Bool.not_eq_true', beq_eq_false_iff_ne] at h
          exact absurd highZero h
        · rfl
        · simp [wordSemWordCmp] at *
      have preRel : ∀ (s : DataSem.State C F), stateRel conf l1 l2 s pre none locs =
          stateRel conf l1 l2 s target none locs := by
        intro s
        exact (stateRel_insertOdd conf l1 l2 s mid none locs 1 _ rfl).trans
          ((stateRel_insertOdd conf l1 l2 s _ none locs 11 _ rfl).trans
            ((stateRel_insertOdd conf l1 l2 s _ none locs 13 _ rfl).trans
              (stateRel_insertOdd conf l1 l2 s target none locs 15 _ rfl)))
      by_cases small : low >>> 29 = 0
      · have smallI : smallInt 32 (word.toNat : Int) := by
          rw [lowEq]; exact (smallInt_word_iff 32 (by decide) low).mpr small
        let final := pre.setVar (adjustVar dest) (.word (smallnum (word.toNat : Int)))
        have run1 : WordSemStateFiniteExact.evaluate
            (compileAssign (width := 32) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
            (none, final) := by
          rw [outer, innerJoined]
          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1,
            wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, WordSemStateFiniteExact.wordExp, shiftN,
            get11', wordShiftHOL, final, lowEq, smallnum_word]
          split
          · rfl
          · rename_i h
            simp only [Option.some.injEq, beq_eq_false_iff_ne] at h
            exact absurd small h
          · simp at *
        have nextPre : stateRel conf l1 l2 nextSource pre none locs := (preRel nextSource).mpr nextRel
        have hmem := nextPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have numberRoot := impMemoryRel_number conf pre.be (holThe nextSource.tstamps) nextSource.refs
          nextSource.space pre.store pre.memory pre.mdomain _ (word.toNat : Int) ⟨Or.inl rfl, smallI, hmem⟩
        have updated := stateRel_insertRoot conf l1 l2 nextSource pre locs dest _ _ nextPre
          (by simpa using numberRoot)
        exact ⟨none, final, run1, by simp, fun _ => ⟨by simpa [nextSource, spaced] using updated, rfl⟩⟩
      · have large : ¬ smallInt 32 (low.toNat : Int) := fun h =>
          small ((smallInt_word_iff 32 (by decide) low).mp h)
        have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
            pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
          simpa [pre, WordSemStateFiniteExact.setVar, joinEnvLocals_insertOdd,
            inter_insertOdd_adjustSet, joinEnvLocals] using midHeap
        have prePresent : ∀ k, (sptLookup k source.locals).isSome →
            (sptLookup (adjustVar k) pre.locals).isSome := by
          intro k present
          have odd1 : adjustVar k ≠ 1 := by simp [adjustVar]
          simpa [pre, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne _ _ _ _ odd1] using
            midPresent k present
        obtain ⟨nf, memory, locals1, writeEval, writeHeap, localsPreserved, destPresent, zeroEq⟩ :=
          evaluateWriteWord32Bignum conf target.be (holThe source.tstamps) source.space source.refs pre
            source.locals envs 11 dest low hd1 preHeap get11' shiftBound (by decide) (by omega) rfl header1
            large prePresent
        have smallerHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
            (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
            (joinEnvLocals (sptInsert dest (.number (word.toNat : Int)) source.locals) locals1 ++ envs) := by
          apply memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs
            (source.space - 2) (source.space - 3) _ _ _ _
          refine ⟨?_, by omega⟩
          rw [lowEq]
          simpa [pre, mid, WordSemStateFiniteExact.setVar] using writeHeap
        have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
          unspaced target locs (.number (word.toNat : Int)) nf memory locals1 pre.fpRegs unspacedRel
          (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
          destPresent
          (by simpa [pre, mid, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using zeroEq)
          (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
        have run1 : WordSemStateFiniteExact.evaluate
            (compileAssign (width := 32) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
            (none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}) := by
          rw [outer, innerJoined]
          simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1]
          split
          · rename_i h
            simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq,
              beq_iff_eq] at h
            exact absurd h small
          · exact writeEval
          · simp [wordSemWordCmp] at *
        refine ⟨none, _, run1, by simp, fun _ => ⟨?_, rfl⟩⟩
        simpa [unspaced, pre, mid, DataSem.doStack, DataSem.doLimSafe, WordSemStateFiniteExact.setVar]
          using finalRel
    · obtain ⟨nf, memory, locals1, writeEval, writeHeap, localsPreserved, destPresent, zeroEq⟩ :=
        evaluateWriteWord64On32Num conf target.be (holThe source.tstamps) source.space source.refs mid
          source.locals envs 11 13 dest low high hd midHeap get11 get13 shiftBound highZero
          (by decide) (by decide) (by omega) rfl header midPresent
      have finalHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
          (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
          (joinEnvLocals (sptInsert dest (.number (word.toNat : Int)) source.locals) locals1 ++ envs) := by
        rw [wordEq]
        simpa [mid, WordSemStateFiniteExact.setVar] using writeHeap
      have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
        unspaced target locs (.number (word.toNat : Int)) nf memory locals1 mid.fpRegs unspacedRel
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
        destPresent
        (by simpa [mid, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using zeroEq)
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe, envs] using finalHeap)
      have run1 : WordSemStateFiniteExact.evaluate
          (compileAssign (width := 32) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
          (none, {mid with store := mid.store.update (.nextFree, nf), memory := memory, locals := locals1}) := by
        rw [compiled, joined]
        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get13]
        split
        · exact writeEval
        · rename_i h
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq,
            Bool.not_eq_false', beq_iff_eq] at h
          exact absurd h highZero
        · simp [wordSemWordCmp] at *
      refine ⟨none, _, run1, by simp, fun _ => ⟨?_, rfl⟩⟩
      simpa [unspaced, mid, DataSem.doStack, DataSem.doLimSafe, WordSemStateFiniteExact.setVar] using finalRel
  · subst width
    have compiled : (compileAssign (width := 64) conf n l dest (.wordOp .wordToInt) [arg] none).1 =
        wordListSeq [loadWord64 conf 3 (adjustVar arg), .assign 1 (shiftN .lsr (.var 3) 61),
          .ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 3) 2))
            (writeWord64 conf hd1 dest 3)] := by
      simp [compileAssign, arg1, assignWordToInt, header1]
    have loadRun := evaluate_loadWord64 conf target.be (holThe source.tstamps) source.refs source.space
      target word loc (locals ++ envs) (adjustVar arg) 3 ⟨rootsRel, shiftBound, rfl, locRead⟩
    let pre := (target.setVar 3 (.word word)).setVar 1 (.word (word >>> 61))
    have prefixRun : WordSemStateFiniteExact.evaluate
        (wordListSeq [loadWord64 conf 3 (adjustVar arg), .assign 1 (shiftN .lsr (.var 3) 61)]) target =
        (none, pre) := by
      have get3 : WordSemStateFiniteExact.getVar 3 (target.setVar 3 (.word word)) = some (.word word) := by
        simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
      simp only [wordListSeq, WordSemStateFiniteExact.evaluate, loadRun, BitVec.setWidth_eq,
        fixClock_setVar_self]
      simp [shiftN, WordSemStateFiniteExact.wordExp, get3, wordShiftHOL, pre]
    have joined := evalListAppend [loadWord64 conf 3 (adjustVar arg), .assign 1 (shiftN .lsr (.var 3) 61)]
      (.ite .equal 1 (.imm 0) (.assign (adjustVar dest) (shiftN .lsl (.var 3) 2))
        (writeWord64 conf hd1 dest 3)) target pre prefixRun
    simp only [List.cons_append, List.nil_append] at joined
    have get1 : WordSemStateFiniteExact.getVar 1 pre = some (.word (word >>> 61)) := by
      simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
    have get3 : WordSemStateFiniteExact.getVar 3 pre = some (.word word) := by
      simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
    have preRel : ∀ (s : DataSem.State C F), stateRel conf l1 l2 s pre none locs =
        stateRel conf l1 l2 s target none locs := by
      intro s
      exact (stateRel_insertOdd conf l1 l2 s (target.setVar 3 (.word word)) none locs 1 _ rfl).trans
        (stateRel_insertOdd conf l1 l2 s target none locs 3 _ rfl)
    by_cases small : word >>> 61 = 0
    · have smallI : smallInt 64 (word.toNat : Int) := (smallInt_word_iff 64 (by decide) word).mpr small
      let final := pre.setVar (adjustVar dest) (.word (smallnum (word.toNat : Int)))
      have run1 : WordSemStateFiniteExact.evaluate
          (compileAssign (width := 64) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
          (none, final) := by
        rw [compiled, joined]
        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1,
          wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, WordSemStateFiniteExact.wordExp, shiftN,
          get3, wordShiftHOL, final, smallnum_word]
        split
        · rfl
        · rename_i h
          simp only [Option.some.injEq, beq_eq_false_iff_ne] at h
          exact absurd small h
        · simp at *
      have nextPre : stateRel conf l1 l2 nextSource pre none locs := (preRel nextSource).mpr nextRel
      have hmem := nextPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have numberRoot := impMemoryRel_number conf pre.be (holThe nextSource.tstamps) nextSource.refs
        nextSource.space pre.store pre.memory pre.mdomain _ (word.toNat : Int) ⟨Or.inr rfl, smallI, hmem⟩
      have updated := stateRel_insertRoot conf l1 l2 nextSource pre locs dest _ _ nextPre
        (by simpa using numberRoot)
      exact ⟨none, final, run1, by simp, fun _ => ⟨by simpa [nextSource, spaced] using updated, rfl⟩⟩
    · have large : ¬ smallInt 64 (word.toNat : Int) := fun h =>
        small ((smallInt_word_iff 64 (by decide) word).mp h)
      have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
          pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
        simpa [pre, WordSemStateFiniteExact.setVar,
          joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
            related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have prePresent : ∀ k, (sptLookup k source.locals).isSome →
          (sptLookup (adjustVar k) pre.locals).isSome := by
        intro k present
        have odd3 : adjustVar k ≠ 3 := by simp [adjustVar]
        have odd1 : adjustVar k ≠ 1 := by simp [adjustVar]
        simpa [pre, WordSemStateFiniteExact.setVar,
          sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using oldPresent k present
      obtain ⟨nf, memory, locals1, writeEval, writeHeap, localsPreserved, destPresent, zeroEq⟩ :=
        evaluateWriteWord64Bignum conf target.be (holThe source.tstamps) source.space source.refs pre
          source.locals envs 3 dest word hd1 preHeap get3 shiftBound (by decide) (by omega) rfl header1
          large prePresent
      have smallerHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
          (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
          (joinEnvLocals (sptInsert dest (.number (word.toNat : Int)) source.locals) locals1 ++ envs) := by
        apply memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs
          (source.space - 2) (source.space - 3) _ _ _ _
        refine ⟨?_, by omega⟩
        simpa [pre, WordSemStateFiniteExact.setVar] using writeHeap
      have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
        unspaced target locs (.number (word.toNat : Int)) nf memory locals1 pre.fpRegs unspacedRel
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
        destPresent
        (by simpa [pre, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using zeroEq)
        (by simpa [unspaced, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
      have run1 : WordSemStateFiniteExact.evaluate
          (compileAssign (width := 64) conf n l dest (.wordOp .wordToInt) [arg] none).1 target =
          (none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}) := by
        rw [compiled, joined]
        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, get1]
        split
        · rename_i h
          simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq,
            beq_iff_eq] at h
          exact absurd h small
        · exact writeEval
        · simp [wordSemWordCmp] at *
      refine ⟨none, _, run1, by simp, fun _ => ⟨?_, rfl⟩⟩
      simpa [unspaced, pre, DataSem.doStack, DataSem.doLimSafe, WordSemStateFiniteExact.setVar] using finalRel

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
