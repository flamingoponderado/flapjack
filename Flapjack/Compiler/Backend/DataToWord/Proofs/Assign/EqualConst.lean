module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemEqList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberConst
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StringConst
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddress

@[expose] public section

/-! Complete constant-equality assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps Flapjack.SemanticPrimitivesHOL
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace EqualConstAssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EqualConstAssignmentWitness

/-- Sequence a successful target assignment. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem seqAssign {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Expose sequential evaluation using the evaluator clock theorem. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem seqEval {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- Run the generated memory-word comparison and record its scratch registers. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem compareWordsRun {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (addrExpr : WordLangExpHOL (BitVec width))
    (address : BitVec width) (words : List (BitVec width)) (dest : Nat) (b : Bool)
    (addr : (s.setVar 1 (.word 2)).wordExp addrExpr = some (.word address))
    (comparison : wordMemEq address words s.mdomain s.memory = some b) :
    ∃ x : WordLocW width,
      let scratch := (if b then fun t => t.setVar 1 (.word 18) else id)
        ((if words ≠ [] then fun t => t.setVar 5 x else id)
          ((s.setVar 1 (.word 2)).setVar 3 (.word address)))
      WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.const 2), .assign 3 addrExpr, memEqList 0 words,
        .assign (adjustVar dest) (.var 1)]) s =
        (none, scratch.setVar (adjustVar dest) (.word (if b then 18 else 2))) := by
  let s1 := s.setVar 1 (.word 2)
  let s3 := s1.setVar 3 (.word address)
  have cmp : wordMemEq address words s3.mdomain s3.memory = some b := comparison
  have reg3 : s3.getVar 3 = some (.word address) := by
    simp [s3, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  obtain ⟨x, run⟩ := memEqList_correct s3 words b address ⟨cmp, reg3⟩
  refine ⟨x, ?_⟩
  simp only [wordListSeq]
  rw [seqAssign s 1 (.const 2) (.word 2) _ (by simp [WordSemStateFiniteExact.wordExp])]
  rw [seqAssign s1 3 addrExpr (.word address) _ addr]
  rw [seqEval, run]
  simp only
  cases b <;> cases words <;>
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, s3, s1,
      sptLookup_sptInsert_ne, sptLookup_sptInsert_same]

/-- Preserve the state relation through the comparison scratch registers. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem compareWordsRel {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F) (s : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (address : BitVec width) (words : List (BitVec width))
    (x : WordLocW width) (b : Bool) (related : stateRel conf l1 l2 source s none locs) :
    stateRel conf l1 l2 source
      ((if b then fun t => t.setVar 1 (.word 18) else id)
        ((if words ≠ [] then fun t => t.setVar 5 x else id)
          ((s.setVar 1 (.word 2)).setVar 3 (.word address)))) none locs := by
  have oddSet (t : WordSemStateFiniteExact width C F) (key : Nat) (value : WordLocW width)
      (odd : key % 2 = 1) (rel : stateRel conf l1 l2 source t none locs) :
      stateRel conf l1 l2 source (t.setVar key value) none locs := by
    simpa [WordSemStateFiniteExact.setVar] using
      (stateRel_insertOdd conf l1 l2 source t none locs key value odd).mpr rel
  let t3 := (s.setVar 1 (.word 2)).setVar 3 (.word address)
  have r3 : stateRel conf l1 l2 source t3 none locs :=
    oddSet _ 3 _ (by decide) (oddSet _ 1 _ (by decide) related)
  let t := (if words ≠ [] then fun t => t.setVar 5 x else id) t3
  have rt : stateRel conf l1 l2 source t none locs := by
    cases words with
    | nil => exact r3
    | cons h tail => exact oddSet _ 5 _ (by decide) r3
  change stateRel conf l1 l2 source ((if b then fun t => t.setVar 1 (.word 18) else id) t) none locs
  cases b with
  | false => exact rt
  | true => exact oddSet _ 1 _ (by decide) rt

/-- Insert a Boolean result into related source and target states. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem insertBool {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (dest : Nat) (answer : Bool) (related : stateRel conf l1 l2 source target none locs) :
    stateRel conf l1 l2 (DataSem.setVar dest (DataSem.boolValue answer) source)
      (target.setVar (adjustVar dest) (.word (if answer then 18 else 2))) none locs := by
  apply stateRel_insertRoot conf l1 l2 source target locs dest _ _ related
  apply memoryRel_bool conf target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain _ _ _
  refine ⟨related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, related.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro h; simp [h]
  · intro h; simp [h]

/-- Combine generated comparison execution and the resulting state relation. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem compareWordsFinish {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F) (s : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (addrExpr : WordLangExpHOL (BitVec width))
    (address : BitVec width) (words : List (BitVec width)) (dest : Nat) (b : Bool)
    (related : stateRel conf l1 l2 source s none locs)
    (addr : (s.setVar 1 (.word 2)).wordExp addrExpr = some (.word address))
    (comparison : wordMemEq address words s.mdomain s.memory = some b) :
    ∃ out, WordSemStateFiniteExact.evaluate (wordListSeq [
        .assign 1 (.const 2), .assign 3 addrExpr, memEqList 0 words,
        .assign (adjustVar dest) (.var 1)]) s = (none, out) ∧
      stateRel conf l1 l2 (DataSem.setVar dest (DataSem.boolValue b) source) out none locs := by
  obtain ⟨x, run⟩ := compareWordsRun s addrExpr address words dest b addr comparison
  let t := (if b then fun t => t.setVar 1 (.word 18) else id)
    ((if words ≠ [] then fun t => t.setVar 5 x else id)
      ((s.setVar 1 (.word 2)).setVar 3 (.word address)))
  have rel := compareWordsRel conf l1 l2 source s locs address words x b related
  exact ⟨t.setVar (adjustVar dest) (.word (if b then 18 else 2)), run,
    insertBool conf l1 l2 source t locs dest b rel⟩

/-- Relate a clear low bit to the generated one-bit mask. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem lowBitZero {width : Nat} (w : BitVec width) (low : w.getLsbD 0 = false) :
    w &&& 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (1 : BitVec width) = BitVec.ofNat width 1 from rfl]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  cases i with
  | zero => simp [low]
  | succ i => simp [Nat.testBit_succ]

/-- Recover the single source argument from successful constant equality. Private infrastructure for the HOL assignment proof, with no separate HOL declaration. -/
private theorem equalConstOne {C F : Type} (part : ClosLang.ConstPart) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.blockOp (.equalConst part)) values source = .val (result, resultState)) :
    ∃ value, values = [value] := by
  cases part <;> cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi] at run
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run

/-- Constant equality satisfies the complete HOL assignment simulation.
The target evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_EqualConst"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignEqualConst_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ part, op = .blockOp (.equalConst part))
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
  obtain ⟨part, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨value, rfl⟩ := equalConstOne part values source resultState result run
    have argLen := DataSpace.getVars_length args source.locals [value] argsEq
    have argShape : ∃ arg, args = [arg] := by
      cases args with
      | nil => simp at argLen
      | cons arg rest =>
        cases rest with
        | nil => exact ⟨arg, rfl⟩
        | cons a rest => simp at argLen
    obtain ⟨arg, rfl⟩ := argShape
    have sourceRead : DataSem.getVar arg source.locals = some value := by
      cases hv : DataSem.getVar arg source.locals with
      | none => simp [DataSem.getVars, hv] at argsEq
      | some got => simpa [DataSem.getVars, hv] using argsEq
    obtain ⟨wordValue, wordRead⟩ := stateRel_getVar conf l1 l2 source target none locs arg value related sourceRead
    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
      target.store target.memory target.mdomain target
      ([(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
      [arg] [value] [wordValue] (by
        refine ⟨?_, argsEq, ?_⟩
        · simpa using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        · simp [WordSemStateFiniteExact.getVars, wordRead])
    cases part with
    | con tag fields =>
      simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | int i =>
      cases value with
      | number j =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨word, wordEq, _⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain j wordValue
          (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
          ⟨related.2.2.2.2.2.2.1, by simpa using roots⟩
        subst wordValue
        have constTest := memoryRel_numberConstTest conf target.be (holThe source.tstamps)
          source.refs source.space target.store target.memory target.mdomain j i word
          (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
            [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
          ⟨by simpa using roots, related.2.2.2.2.2.2.1⟩
        let next := DataSem.doStack (.blockOp (.equalConst (.int i))) [.number j]
          (DataSem.doLimSafe source (.blockOp (.equalConst (.int i))) [.number j])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        by_cases small : smallInt width i
        · have numberEq : ((smallnum i : BitVec width) = word ↔ j = i) := by
            simpa [small] using constTest
          have iff : word = (smallnum i : BitVec width) ↔ i = j := by
            exact eq_comm.trans (numberEq.trans eq_comm)
          have boolEq : (if word = (smallnum i : BitVec width) then (18 : BitVec width) else 2) =
              (if decide (i = j) then 18 else 2) := by
            by_cases eq : word = (smallnum i : BitVec width)
            · have sourceEq := iff.mp eq
              simp [eq, sourceEq]
            · have sourceNe : i ≠ j := fun h => eq (iff.mpr h)
              simp [eq, sourceNe]
          have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.int i) conf n l dest none arg).1 target =
              (none, target.setVar (adjustVar dest) (.word (if word = smallnum i then 18 else 2))) := by
            simp only [assignEqualConst, Build.partWords, small, if_true]
            change WordSemStateFiniteExact.evaluate (setBool (adjustVar dest) .equal (adjustVar arg) (.imm (smallnum i))) target = _
            simp only [setBool]
            rw [WordSemStateFiniteExact.evaluate, wordRead]
            by_cases eq : word = (smallnum i : BitVec width)
            · simp [WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
                Compiler.Encoders.Asm.wordCmpHOL, WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.wordExp, eq]
            · have neq : (word == (smallnum i : BitVec width)) = false := beq_eq_false_iff_ne.mpr eq
              simp [WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
                Compiler.Encoders.Asm.wordCmpHOL, WordSemStateFiniteExact.evaluate,
                WordSemStateFiniteExact.wordExp, eq, neq]
          rw [boolEq] at eval
          have rel := insertBool conf l1 l2 next target locs dest (decide (i = j)) nextRel
          refine ⟨none, target.setVar (adjustVar dest) (.word (if decide (i = j) then 18 else 2)), ?_, ?_, ?_⟩
          · simpa [compileAssign, arg1] using eval
          · simp
          · intro _; exact ⟨rel, rfl⟩
        · cases bin : bignumWords (width := width) conf i with
          | none =>
            have neq : j ≠ i := by simpa [small, bin] using constTest
            have sourceEq : decide (i = j) = false := by simp [Ne.symm neq]
            have buildNone : Build.partWords (width := width) conf .ln (.int i) 0 = none := by
              simp only [bignumWords, Misc.Multiword.i2mw] at bin
              simp only [Build.partWords, small, if_false, Misc.Multiword.i2mw]
              cases enc : encodeHeader (width := width) conf (if i < 0 then 7 else 3)
                  (Misc.Multiword.n2mw (width := width) i.natAbs).length <;> simp_all
            have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.int i) conf n l dest none arg).1 target =
                (none, target.setVar (adjustVar dest) (.word 2)) := by
              rw [assignEqualConst, buildNone]
              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
            have rel := insertBool conf l1 l2 next target locs dest false nextRel
            refine ⟨none, target.setVar (adjustVar dest) (.word 2), ?_, ?_, ?_⟩
            · simpa [compileAssign, arg1] using eval
            · simp
            · intro _
              simp only [sourceEq]
              exact ⟨rel, trivial⟩
          | some words =>
            cases enc : encodeHeader (width := width) conf (if i < 0 then 7 else 3)
                (Misc.Multiword.n2mw (width := width) i.natAbs).length with
            | none => simp [bignumWords, Misc.Multiword.i2mw, enc] at bin
            | some header =>
              have wordsEq : words = header :: Misc.Multiword.n2mw (width := width) i.natAbs := by
                simpa [bignumWords, Misc.Multiword.i2mw, enc] using bin.symm
              subst words
              have buildSome : Build.partWords (width := width) conf .ln (.int i) 0 =
                  some ((true, Build.makePtr conf 0 (0 : BitVec width)
                    (Misc.Multiword.n2mw (width := width) i.natAbs).length),
                    (header :: Misc.Multiword.n2mw (width := width) i.natAbs).map (fun w => (false, .word w))) := by
                simp [Build.partWords, small, Misc.Multiword.i2mw, enc]
              by_cases low : word.getLsbD 0 = false
              · have neq : j ≠ i := by simpa [small, bin, low] using constTest
                have sourceEq : decide (i = j) = false := by simp [Ne.symm neq]
                have mask := lowBitZero word low
                have test : wordSemWordCmp .test (.word word) (.word (1 : BitVec width)) = some true := by
                  simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
                  change (word &&& (1 : BitVec width) == 0) = true
                  exact beq_iff_eq.mpr mask
                have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.int i) conf n l dest none arg).1 target =
                    (none, target.setVar (adjustVar dest) (.word 2)) := by
                  rw [assignEqualConst, buildSome]
                  rw [WordSemStateFiniteExact.evaluate, wordRead]
                  simp only [WordSemStateFiniteExact.getVarImm, test]
                  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
                have rel := insertBool conf l1 l2 next target locs dest false nextRel
                refine ⟨none, target.setVar (adjustVar dest) (.word 2), ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1] using eval
                · simp
                · intro _
                  simp only [sourceEq]
                  exact ⟨rel, trivial⟩
              · have trueBit : word.getLsbD 0 = true := by cases bit : word.getLsbD 0 <;> simp_all
                obtain ⟨address, addrEq, cmp⟩ := by simpa [small, bin, low] using constTest
                have maskNe : word &&& (1 : BitVec width) ≠ 0 := by
                  intro eq
                  have bits := congrArg (fun v : BitVec width => v.getLsbD 0) eq
                  have pos : 0 < width := NeZero.pos width
                  simp [pos] at bits
                  rw [BitVec.getLsbD_eq_getElem pos] at trueBit
                  simp_all
                have test : wordSemWordCmp .test (.word word) (.word (1 : BitVec width)) = some false := by
                  simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
                  change (word &&& (1 : BitVec width) == 0) = false
                  exact beq_eq_false_iff_ne.mpr maskNe
                have addrExp : (target.setVar 1 (.word 2)).wordExp (realAddr conf (adjustVar arg)) = some (.word address) := by
                  apply wordExpRealAddr conf target word address arg
                    ⟨addrEq, related.2.2.2.2.2.2.2.1, related.2.2.2.2.2.2.1, wordRead⟩
                have cmpEq : wordMemEq address (header :: Misc.Multiword.n2mw (width := width) i.natAbs)
                    target.mdomain target.memory = some (decide (i = j)) := by
                  have boolEq : decide (j = i) = decide (i = j) := decide_eq_decide.mpr eq_comm
                  rwa [boolEq] at cmp
                obtain ⟨out, evalWords, outRel⟩ := compareWordsFinish conf l1 l2 next target locs
                  (realAddr conf (adjustVar arg)) address (header :: Misc.Multiword.n2mw i.natAbs)
                  dest (decide (i = j)) nextRel addrExp cmpEq
                have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.int i) conf n l dest none arg).1 target = (none, out) := by
                  rw [assignEqualConst, buildSome]
                  rw [WordSemStateFiniteExact.evaluate, wordRead]
                  simp only [WordSemStateFiniteExact.getVarImm, test]
                  simpa [Build.getWord, Function.comp_def] using evalWords
                refine ⟨none, out, ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1] using eval
                · simp
                · intro _; exact ⟨outRel, rfl⟩
      | word64 _ | block _ _ _ | codePtr _ | refPtr _ _ =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
    | str s =>
      cases value with
      | refPtr flag ptr =>
        have refsEq : (DataSem.doStack (.blockOp (.equalConst (.str s))) [.refPtr flag ptr]
            (DataSem.doLimSafe source (.blockOp (.equalConst (.str s))) [.refPtr flag ptr])).refs = source.refs := rfl
        cases lookup : sptLookup ptr source.refs with
        | none => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, refsEq, lookup] at run
        | some obj =>
          cases obj with
          | byteArray byteFlag bytes =>
            cases byteFlag with
            | false => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, refsEq, lookup] at run
            | true =>
              simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
                DataSem.doAppAux, DataSem.applyNonFfi, refsEq, lookup] at run
              obtain ⟨rfl, rfl⟩ := run
              let next := DataSem.doStack (.blockOp (.equalConst (.str s))) [.refPtr flag ptr]
                (DataSem.doLimSafe source (.blockOp (.equalConst (.str s))) [.refPtr flag ptr])
              have nextRel : stateRel conf l1 l2 next target none locs :=
                stateRel_doStack conf l1 l2 _ target locs _ _
                  (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
              have constTest := memoryRel_stringConstTest conf target.be (holThe source.tstamps)
                source.refs source.space target.store target.memory target.mdomain flag ptr wordValue
                (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
                  [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
                bytes s ⟨by simpa using roots, lookup, related.2.2.2.2.2.2.1⟩
              have stringIff : (bytes = s.explode) ↔ s = Flapjack.Basis.Pure.MlString.MlString.implode bytes := by
                cases s; simp [Flapjack.Basis.Pure.MlString.MlString.explode, eq_comm]
              have boolEq : decide (bytes = s.explode) =
                  decide (s = Flapjack.Basis.Pure.MlString.MlString.implode bytes) := decide_eq_decide.mpr stringIff
              cases build : Build.partWords (width := width) conf .ln (.str s) 0 with
              | none =>
                have neq := constTest.1 build
                have sourceEq : decide (bytes = s.explode) = false := by rw [boolEq]; simp [neq]
                have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.str s) conf n l dest none arg).1 target =
                    (none, target.setVar (adjustVar dest) (.word 2)) := by
                  rw [assignEqualConst, build]
                  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
                have rel := insertBool conf l1 l2 next target locs dest false nextRel
                refine ⟨none, target.setVar (adjustVar dest) (.word 2), ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1] using eval
                · simp
                · intro _; simp only [sourceEq]; exact ⟨rel, trivial⟩
              | some compiled =>
                rcases compiled with ⟨⟨present, v⟩, res⟩
                have presentTrue : present = true := by
                  by_cases bounds : Build.byteLen width s.explode.length < 2 ^ (width - 4) ∧
                      Build.byteLen width s.explode.length < 2 ^ conf.lenSize
                  · simp [Build.partWords, bounds] at build
                    exact build.1.1
                  · simp [Build.partWords, bounds] at build
                subst present
                obtain ⟨word, address, locEq, addrEq, cmp⟩ := constTest.2 (true, v) res build
                subst wordValue
                have addrExp : (target.setVar 1 (.word 2)).wordExp (realAddr conf (adjustVar arg)) = some (.word address) := by
                  apply wordExpRealAddr conf target word address arg
                    ⟨addrEq, related.2.2.2.2.2.2.2.1, related.2.2.2.2.2.2.1, wordRead⟩
                have cmpEq : wordMemEq address (res.map (fun x => Build.getWord x.2)) target.mdomain target.memory =
                    some (decide (bytes = s.explode)) := by rw [boolEq]; exact cmp
                obtain ⟨out, evalWords, outRel⟩ := compareWordsFinish conf l1 l2 next target locs
                  (realAddr conf (adjustVar arg)) address (res.map (fun x => Build.getWord x.2))
                  dest (decide (bytes = s.explode)) nextRel addrExp cmpEq
                have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.str s) conf n l dest none arg).1 target = (none, out) := by
                  rw [assignEqualConst, build]
                  exact evalWords
                refine ⟨none, out, ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1] using eval
                · simp
                · intro _; exact ⟨outRel, rfl⟩
          | valueArray _ | mutBlock _ _ _ _ _ | thunk _ _ =>
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, refsEq, lookup] at run
      | number _ | word64 _ | block _ _ _ | codePtr _ =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
    | w64 constant =>
      cases value with
      | word64 value =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
        obtain ⟨rfl, rfl⟩ := run
        let next := DataSem.doStack (.blockOp (.equalConst (.w64 constant))) [.word64 value]
          (DataSem.doLimSafe source (.blockOp (.equalConst (.w64 constant))) [.word64 value])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        obtain ⟨word, address, words, header, locEq, addrEq, cmp, encoded, wordsEq⟩ :=
          memoryRel_word64ConstTest conf target.be (holThe source.tstamps) source.refs source.space
            target.store target.memory target.mdomain value constant wordValue
            (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
              [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
            ⟨by simpa using roots, related.2.2.2.2.2.2.1⟩
        subst wordValue
        have cmpEq : wordMemEq (address + wordSemBytesInWord) words target.mdomain target.memory =
            some (decide (constant = value)) := by
          have boolEq : decide (value = constant) = decide (constant = value) := decide_eq_decide.mpr eq_comm
          rw [boolEq] at cmp
          simpa [wordSemBytesInWord, StackRemove.bytesInWord] using cmp
        have baseExp : (target.setVar 1 (.word 2)).wordExp (realAddr conf (adjustVar arg)) = some (.word address) := by
          apply wordExpRealAddr conf target word address arg
            ⟨addrEq, related.2.2.2.2.2.2.2.1, related.2.2.2.2.2.2.1, wordRead⟩
        have addrExp : (target.setVar 1 (.word 2)).wordExp
            (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord]) =
            some (.word (address + wordSemBytesInWord)) := by
          simp only [WordSemStateFiniteExact.wordExp, List.attach_map_val, List.map_cons, List.map_nil,
            baseExp, theWords, wordOpHOL, wordOp, List.foldr_cons, List.foldr_nil, add_zero, Option.map_some]
        obtain ⟨out, evalWords, outRel⟩ := compareWordsFinish conf l1 l2 next target locs
          (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord])
          (address + wordSemBytesInWord) words dest (decide (constant = value)) nextRel addrExp cmpEq
        have buildSome : ∃ ptr, Build.partWords (width := width) conf .ln (.w64 constant) 0 =
            some ((true, ptr), (header :: words).map (fun w => (false, .word w))) := by
          rcases related.2.2.2.2.2.2.1 with dim32 | dim64
          · subst width
            have high : holWordExtract 63 32 constant 32 = BitVec.ofNat 32 (constant.toNat / 2 ^ 32) := by
              apply BitVec.eq_of_toNat_eq
              simp [holWordExtract, Nat.shiftRight_eq_div_pow]
            have low : holWordExtract 31 0 constant 32 = BitVec.ofNat 32 (constant.toNat % 2 ^ 32) := by
              apply BitVec.eq_of_toNat_eq
              simp [holWordExtract]
            simp only [show (32 : Nat) < 64 by decide, if_true, high, low] at wordsEq
            subst words
            have enc : encodeHeader (width := 32) conf 3 2 = some header := by simpa using encoded
            refine ⟨Build.makePtr conf 0 (0 : BitVec 32) 2, ?_⟩
            simp [Build.partWords, enc]
          · subst width
            have full : holWordExtract 63 0 constant 64 = BitVec.ofNat 64 constant.toNat := by
              apply BitVec.eq_of_toNat_eq
              simp [holWordExtract, Nat.mod_eq_of_lt constant.isLt]
            simp only [show ¬ (64 : Nat) < 64 by decide, if_false, full] at wordsEq
            subst words
            have enc : encodeHeader (width := 64) conf 3 1 = some header := by simpa using encoded
            refine ⟨Build.makePtr conf 0 (0 : BitVec 64) 1, ?_⟩
            simp [Build.partWords, enc]
        obtain ⟨ptr, buildSome⟩ := buildSome
        have eval : WordSemStateFiniteExact.evaluate (assignEqualConst (.w64 constant) conf n l dest none arg).1 target = (none, out) := by
          rw [assignEqualConst, buildSome]
          simpa [Build.getWord, Function.comp_def] using evalWords
        refine ⟨none, out, ?_, ?_, ?_⟩
        · simpa [compileAssign, arg1] using eval
        · simp
        · intro _; exact ⟨outRel, rfl⟩
      | number _ | block _ _ _ | codePtr _ | refPtr _ _ =>
        simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
