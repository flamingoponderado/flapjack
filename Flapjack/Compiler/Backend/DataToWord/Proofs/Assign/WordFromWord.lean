module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpUop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.WordArith

@[expose] public section

/-! Conversions between boxed Word64 values and bytes in the data-to-word assignment
simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace WordFromWordAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordFromWordAssignmentWitness

/-- Invert the source narrowing conversion of a Word64 to a byte; local proof
infrastructure for `assign_WordFromWord`. -/
private theorem wordFromWordTrueSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.wordFromWord true)) values source = .val (result, resultState)) :
    ∃ word, values = [.word64 word] ∧
      result = .number (Int.ofNat (BitVec.ofNat 8 word.toNat).toNat) ∧
      resultState = DataSem.doStack (.wordOp (.wordFromWord true)) values
        (DataSem.doLimSafe source (.wordOp (.wordFromWord true)) values) := by
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
  | cons value rest =>
    cases rest with
    | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | nil =>
      cases value <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]

/-- Invert the source widening conversion of a byte to a Word64; local proof
infrastructure for `assign_WordFromWord`. -/
private theorem wordFromWordFalseSource {C F : Type} (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.wordFromWord false)) values source = .val (result, resultState)) :
    ∃ n byte next, values = [.number n] ∧ ClosSem.intToByte n = some byte ∧
      DataSem.consumeSpace 3 source = some next ∧
      result = .word64 (byte.setWidth 64) ∧
      resultState = DataSem.doStack (.wordOp (.wordFromWord false)) values
        (DataSem.doLimSafe next (.wordOp (.wordFromWord false)) values) := by
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
        rename_i n
        cases hb : ClosSem.intToByte n <;> simp_all

/-- The HOL bitwise-and operator is Lean's `&&&` on bit vectors. -/
private theorem andOp_eq {w : Nat} (a b : BitVec w) : AndOp.and a b = a &&& b := rfl

/-- Masking the low byte of a loaded payload word and tagging it gives the small
number of the source byte; local arithmetic for `assign_WordFromWord`. -/
private theorem maskTag {width : Nat} [NeZero width] (word : BitVec 64) (good : goodDimindex width) :
    ((word.setWidth width &&& 255) <<< (2 : Nat)) =
      (smallnum (Int.ofNat (BitVec.ofNat 8 word.toNat).toNat) : BitVec width) := by
  have nonneg : ¬ ((Int.ofNat (BitVec.ofNat 8 word.toNat).toNat) < 0) := by
    simp only [not_lt]
    exact Int.natCast_nonneg _
  unfold smallnum
  rw [if_neg nonneg]
  apply BitVec.eq_of_toNat_eq
  have mask : ∀ m : Nat, m &&& 255 = m % 256 := fun m => by
    simpa using Nat.and_two_pow_sub_one_eq_mod m 8
  rcases good with rfl | rfl <;>
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, Nat.shiftLeft_eq, mask] <;> omega

/-- A safe widening conversion has an encodable Word64 header; local proof
infrastructure for `assign_WordFromWord`. -/
private theorem wordFromWordHeaderOfSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (safe : DataSem.limSafe source.limits (.wordOp (.wordFromWord false)) values) :
    ∃ hd, encodeHeader (width := width) conf 3 (if width < 64 then 2 else 1) = some hd := by
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have limitEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
  have safeLen : 1 < conf.lenSize := by
    simp [DataSem.limSafe, limitEq] at safe
    exact safe
  have countBound : 2 < 2 ^ conf.lenSize := by
    have h : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rcases good with h | h <;> subst width
  · refine ⟨makeHeader conf (BitVec.ofNat 32 3) 2, ?_⟩
    simp [encodeHeader, countBound, show 3 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · refine ⟨makeHeader conf (BitVec.ofNat 64 3) 1, ?_⟩
    simp [encodeHeader, show 1 < 2 ^ conf.lenSize by omega, show 3 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]

/-- A decoded byte is a small integer; local arithmetic for `assign_WordFromWord`. -/
private theorem byteSmall {width : Nat} [NeZero width] (good : goodDimindex width) (n : Int)
    (byte : BitVec 8) (h : ClosSem.intToByte n = some byte) : smallInt width n := by
  unfold ClosSem.intToByte at h
  split at h
  · rename_i range
    rcases good with rfl | rfl <;> simp [smallInt] <;> omega
  · cases h

/-- Untagging the small number of a decoded byte gives the byte zero-extended to the
machine word; local arithmetic for `assign_WordFromWord`. -/
private theorem byteShift {width : Nat} [NeZero width] (good : goodDimindex width) (n : Int)
    (byte : BitVec 8) (h : ClosSem.intToByte n = some byte) :
    (smallnum n : BitVec width) >>> (2 : Nat) = (byte.setWidth 64).setWidth width := by
  unfold ClosSem.intToByte at h
  split at h
  · rename_i range
    cases h
    have nonneg : ¬ n < 0 := by omega
    unfold smallnum
    rw [if_neg nonneg]
    apply BitVec.eq_of_toNat_eq
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le range.1
    have mLt : m < 256 := by omega
    rcases good with rfl | rfl <;>
      simp [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow] <;>
      omega
  · cases h

/-- A zero-extended byte has a zero high 32-bit half; local arithmetic for
`assign_WordFromWord`. -/
private theorem byteHigh (byte : BitVec 8) :
    ((byte.setWidth 64) >>> (32 : Nat)).setWidth 32 = 0 := by
  apply BitVec.eq_of_toNat_eq
  have lt := byte.isLt
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  omega

/-- Converting between boxed Word64 values and bytes satisfies the original
assignment simulation. The evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordFromWord"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordFromWord_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ b, op = .wordOp (.wordFromWord b))
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
  obtain ⟨narrow, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    have good := related.2.2.2.2.2.2.1
    cases narrow with
    | true =>
      obtain ⟨word, valuesEq, resultEq, stateEq⟩ := wordFromWordTrueSource values source resultState result run
      subst values result resultState
      have argLen := DataSpace.getVars_length args source.locals [.word64 word] argsEq
      cases args with
      | nil => simp at argLen
      | cons arg rest =>
        cases rest with
        | cons x xs => simp at argLen
        | nil =>
          obtain ⟨words, getWords, lengthEq⟩ :=
            stateRel_getVars conf l1 l2 source target locs [arg] [.word64 word] related argsEq
          cases words with
          | nil => simp at lengthEq
          | cons loc rest =>
            cases rest with
            | cons x xs => simp at lengthEq
            | nil =>
              let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                flatStack source.stack target.stack
              let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
              have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                target.store target.memory target.mdomain target envs [arg] [.word64 word] [loc] (by
                  refine ⟨?_, argsEq, getWords⟩
                  simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
              obtain ⟨index, addr, originalHeader, locEq, realAddrEq, domainHeader, headerWord,
                bit3, bit4, bit2, domainFirst, payload⟩ :=
                  memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain word loc (locals ++ envs)
                    ⟨by simpa [locals, envs, List.append_assoc] using roots, good⟩
              have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
                cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
                  simp_all [WordSemStateFiniteExact.getVars]
              have pointerRead : WordSemStateFiniteExact.getVar (adjustVar arg) target =
                  some (.word (getAddr conf index (.word 0))) := by simpa [locEq] using locRead
              have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target
                (getAddr conf index (.word 0)) addr
                ⟨related.2.2.2.2.2.2.2.1, good, pointerRead, realAddrEq⟩
              let byteInt : Int := Int.ofNat (BitVec.ofNat 8 word.toNat).toNat
              let offset : BitVec width :=
                if width = 32 then 2 * wordSemBytesInWord else wordSemBytesInWord
              have loadDomain : target.mdomain (addr + offset) = true ∧
                  target.memory (addr + offset) = .word (word.setWidth width) := by
                rcases good with h | h <;> subst width
                · simp only [show 32 < 64 by decide, ↓reduceIte] at payload
                  obtain ⟨_, domainSecond, payloadLow, _⟩ := payload
                  simpa [offset, StackRemove.bytesInWord, wordSemBytesInWord] using
                    And.intro domainSecond payloadLow
                · simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at payload
                  obtain ⟨payloadWord, _⟩ := payload
                  simpa [offset, StackRemove.bytesInWord, wordSemBytesInWord] using
                    And.intro domainFirst payloadWord
              let t1 := WordSemStateFiniteExact.setVar 1 (.word ((word.setWidth width) &&& 255))
                (WordSemStateFiniteExact.setVar 1 (.word (word.setWidth width))
                  (WordSemStateFiniteExact.setVar 1 (.word addr) target))
              let final := WordSemStateFiniteExact.setVar (adjustVar dest)
                (.word (smallnum byteInt : BitVec width)) t1
              have eval : WordSemStateFiniteExact.evaluate
                  (compileAssign conf n l dest (.wordOp (.wordFromWord true)) [arg] none).1 target =
                    (none, final) := by
                obtain ⟨loadDom, loadMem⟩ := loadDomain
                have tagged := maskTag word good
                rcases good with h | h <;> subst width <;>
                  simp [offset, wordSemBytesInWord] at loadDom loadMem <;>
                simp [compileAssign, wordSemBytesInWord, arg1, assignWordFromWord, wordListSeq, WordSemStateFiniteExact.evaluate,
                  WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad,
                  WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                  WordSemStateFiniteExact.fixClock, theWords, wordOpHOL, wordOp, realEval,
                  loadDom, loadMem, sptLookup_sptInsert_same, shiftVar, shiftN, wordShiftHOL,
                  final, t1, byteInt, andOp_eq] <;>
                simp at tagged <;> rw [tagged]
              let next := DataSem.doStack (.wordOp (.wordFromWord true)) [.word64 word]
                (DataSem.doLimSafe source (.wordOp (.wordFromWord true)) [.word64 word])
              have nextRel : stateRel conf l1 l2 next target none locs :=
                stateRel_doStack conf l1 l2 _ target locs _ _
                  (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
              have rel1 : stateRel conf l1 l2 next t1 none locs := by
                have ins1 : ∀ (t : WordSemStateFiniteExact width C F) (x : WordLocW width),
                    stateRel conf l1 l2 next (WordSemStateFiniteExact.setVar 1 x t) none locs =
                      stateRel conf l1 l2 next t none locs :=
                  fun t x => stateRel_insert_1 conf l1 l2 next t none locs x
                simp only [t1]
                rw [ins1, ins1, ins1]
                exact nextRel
              have small : smallInt width byteInt := smallInt_w2n width _ good
              let nextLocals := joinEnv next.locals (sptToAList (sptInter t1.locals (adjustSet next.locals)))
              let nextEnvs := [(theGlobal next.global, holFapply t1.store .globals)] ++
                flatStack next.stack t1.stack
              have hmem := rel1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              have numberRoot : memoryRel conf t1.be (holThe next.tstamps) next.refs next.space
                  t1.store t1.memory t1.mdomain
                  ((.number byteInt, .word (smallnum byteInt)) :: nextLocals ++ nextEnvs) := by
                apply impMemoryRel_number conf t1.be (holThe next.tstamps) next.refs next.space
                  t1.store t1.memory t1.mdomain (nextLocals ++ nextEnvs) _
                exact ⟨good, small, by simpa [nextLocals, nextEnvs] using hmem⟩
              have updated := stateRel_insertRoot conf l1 l2 next t1 locs dest
                (.number byteInt) (.word (smallnum byteInt)) rel1
                (by simpa [nextLocals, nextEnvs] using numberRoot)
              refine ⟨none, final, eval, by simp, ?_⟩
              intro _
              exact ⟨by simpa [final, next, byteInt] using updated, rfl⟩
    | false =>
      obtain ⟨sn, byte, next, valuesEq, byteEq, spaceEq, resultEq, stateEq⟩ :=
        wordFromWordFalseSource values source resultState result run
      subst values result resultState
      have argLen := DataSpace.getVars_length args source.locals [.number sn] argsEq
      have nextEq : next = { source with space := source.space - 3 } := by
        unfold DataSem.consumeSpace at spaceEq
        split at spaceEq <;> simp_all
      subst next
      have spaceEnough : 3 ≤ source.space := by
        unfold DataSem.consumeSpace at spaceEq
        split at spaceEq <;> simp_all
      have nextRel : stateRel conf l1 l2
          (DataSem.doStack (.wordOp (.wordFromWord false)) [.number sn]
            (DataSem.doLimSafe source (.wordOp (.wordFromWord false)) [.number sn])) target none locs :=
        stateRel_doStack conf l1 l2 _ target locs _ _
          (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
      cases args with
      | nil => simp at argLen
      | cons arg rest =>
        cases rest with
        | cons x xs => simp at argLen
        | nil =>
          cases header : encodeHeader (width := width) conf 3 (if width < 64 then 2 else 1) with
          | none =>
            obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
            have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.wordFromWord false)) [.number sn] := by
              intro safe
              obtain ⟨hd, encoded⟩ := wordFromWordHeaderOfSafe conf source target l1 l2 locs [.number sn]
                related safe
              rw [header] at encoded
              contradiction
            refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
            · simpa [compileAssign, arg1, assignWordFromWord, header] using outEval
            · intro _
              refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
              · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
                simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
              · intro _
                simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
            · simp
          | some hd =>
            obtain ⟨words, getWords, lengthEq⟩ :=
              stateRel_getVars conf l1 l2 source target locs [arg] [.number sn] related argsEq
            cases words with
            | nil => simp at lengthEq
            | cons loc rest =>
              cases rest with
              | cons x xs => simp at lengthEq
              | nil =>
                let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                  flatStack source.stack target.stack
                let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
                have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                  target.store target.memory target.mdomain target envs [arg] [.number sn] [loc] (by
                    refine ⟨?_, argsEq, getWords⟩
                    simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                have small : smallInt width sn := byteSmall good sn byte byteEq
                have locEq := memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs
                  source.space target.store target.memory target.mdomain sn loc (locals ++ envs)
                  ⟨good, small, by simpa [locals, envs, List.append_assoc] using roots⟩
                have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
                  cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
                    simp_all [WordSemStateFiniteExact.getVars]
                subst locEq
                have locRead' : sptLookup (adjustVar arg) target.locals = some (.word (smallnum sn)) := by
                  simpa [WordSemStateFiniteExact.getVar] using locRead
                have shifted := byteShift good sn byte byteEq
                let resultWord : BitVec 64 := byte.setWidth 64
                rcases good with width32 | width64
                · subst width
                  let pre := WordSemStateFiniteExact.setVar 3 (.word 0)
                    (WordSemStateFiniteExact.setVar 5 (.word (resultWord.setWidth 32)) target)
                  have prefixEval : WordSemStateFiniteExact.evaluate (wordListSeq [
                      .assign 5 (shiftN .lsr (.var (adjustVar arg)) 2), .assign 3 (.const 0)]) target =
                        (none, pre) := by
                    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.fixClock, shiftN, wordShiftHOL,
                      locRead', pre, resultWord, shifted, WordSemStateFiniteExact.setVar]
                  have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                      pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar,
                      joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                        related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have preLow : pre.getVar 5 = some (.word (resultWord.setWidth 32)) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                  have preHigh : pre.getVar 3 = some (.word ((resultWord >>> 32).setWidth 32)) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same, resultWord, byteHigh byte]
                  have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                      (sptLookup (adjustVar k) pre.locals).isSome := by
                    intro k present
                    have odd3 : adjustVar k ≠ 3 := by simp [adjustVar]
                    have odd5 : adjustVar k ≠ 5 := by simp [adjustVar]; omega
                    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                    simpa [pre, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd5]
                      using presentOld k present
                  have writeRun := evaluateWriteWord64On32 (β := PUnit) conf target.be (holThe source.tstamps)
                    source.space source.refs pre source.locals envs 5 3 dest resultWord hd
                    preHeap preLow preHigh related.2.2.2.2.2.2.2.1 (by decide) (by decide) (by omega) rfl
                    (by simpa using header) prePresent
                  obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                    destPresent, zeroEq⟩ := writeRun
                  have finalHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                      (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                      (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar] using writeHeap
                  let nextSource := DataSem.doStack (.wordOp (.wordFromWord false)) [.number sn]
                    (DataSem.doLimSafe source (.wordOp (.wordFromWord false)) [.number sn])
                  have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                    nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                    destPresent
                    (by simpa [pre, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using zeroEq)
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using finalHeap)
                  have header32 : encodeHeader (width := 32) conf 3 2 = some hd := by simpa using header
                  have seqRun := evalListAppend [
                    .assign 5 (shiftN .lsr (.var (adjustVar arg)) 2), .assign 3 (.const 0)]
                    (writeWord64On32 conf hd dest 5 3) target pre prefixEval
                  rw [writeEval] at seqRun
                  refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1},
                    ?_, ?_, ?_⟩
                  · simpa [compileAssign, arg1, assignWordFromWord, header32] using seqRun
                  · simp
                  · intro _
                    refine ⟨?_, rfl⟩
                    simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                      WordSemStateFiniteExact.setVar] using finalRel
                · subst width
                  let pre := WordSemStateFiniteExact.setVar 3 (.word resultWord) target
                  have prefixEval : WordSemStateFiniteExact.evaluate (wordListSeq [
                      .assign 3 (shiftN .lsr (.var (adjustVar arg)) 2)]) target = (none, pre) := by
                    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                      WordSemStateFiniteExact.getVar, shiftN, wordShiftHOL,
                      locRead', pre, resultWord, shifted, WordSemStateFiniteExact.setVar]
                  have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                      pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                    simpa [pre, WordSemStateFiniteExact.setVar,
                      joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                        related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  have preRead : pre.getVar 3 = some (.word resultWord) := by
                    simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_same]
                  have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                      (sptLookup (adjustVar k) pre.locals).isSome := by
                    intro k present
                    have odd : adjustVar k ≠ 3 := by simp [adjustVar]
                    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                    simpa [pre, WordSemStateFiniteExact.setVar,
                      sptLookup_sptInsert_ne _ _ _ _ odd] using presentOld k present
                  have writeRun := evaluateWriteWord64 (β := PUnit) conf target.be (holThe source.tstamps)
                    source.space source.refs pre source.locals envs 3 dest resultWord hd
                    preHeap preRead related.2.2.2.2.2.2.2.1 (by decide) (by omega) rfl
                    (by simpa using header) prePresent
                  obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                    destPresent, zeroEq⟩ := writeRun
                  have smallerHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                      (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                      (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                    apply memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs
                      (source.space - 2) (source.space - 3) _ _ _ _
                    refine ⟨?_, by omega⟩
                    simpa [pre, WordSemStateFiniteExact.setVar] using writeHeap
                  let nextSource := DataSem.doStack (.wordOp (.wordFromWord false)) [.number sn]
                    (DataSem.doLimSafe source (.wordOp (.wordFromWord false)) [.number sn])
                  have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                    nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                    destPresent
                    (by simpa [pre, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using zeroEq)
                    (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
                  have header64 : encodeHeader (width := 64) conf 3 1 = some hd := by simpa using header
                  have seqRun := evalListAppend [
                    .assign 3 (shiftN .lsr (.var (adjustVar arg)) 2)]
                    (writeWord64 conf hd dest 3) target pre prefixEval
                  rw [writeEval] at seqRun
                  refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1},
                    ?_, ?_, ?_⟩
                  · simpa [compileAssign, arg1, assignWordFromWord, header64] using seqRun
                  · simp
                  · intro _
                    refine ⟨?_, rfl⟩
                    simpa [nextSource, resultWord, pre, DataSem.doStack, DataSem.doLimSafe,
                      WordSemStateFiniteExact.setVar] using finalRel
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
