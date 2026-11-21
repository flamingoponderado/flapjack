module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BoolTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordOp8
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

@[expose] public section

/-! Byte comparison assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace WordTestWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordTestWitness

/-- Word tests satisfy the original assignment simulation. The evaluator
inherits the real-model assumption documented in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordTest"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordTest_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ ws test, op = .wordOp (.wordTest ws test))
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
  obtain ⟨ws, test, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  cases ws with
  | w64 =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons a rest =>
      cases rest with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | cons b tail =>
        cases tail <;> simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
  | w8 =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons a rest =>
      cases rest with
      | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | cons b tail =>
        cases tail with
        | cons c tail => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
        | nil =>
          cases a <;> cases b <;>
            simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]
          rename_i a b
          by_cases bounds : 0 ≤ a ∧ a < 256 ∧ 0 ≤ b ∧ b < 256
          · simp only [bounds] at run
            simp only [true_and, if_true] at run
            have argLen := DataSpace.getVars_length args source.locals [.number a, .number b] argsEq
            have argsShape : ∃ x y, args = [x, y] := by
              cases args with
              | nil => simp at argLen
              | cons x rest =>
                cases rest with
                | nil => simp at argLen
                | cons y rest =>
                  cases rest with
                  | nil => exact ⟨x, y, rfl⟩
                  | cons z rest => simp at argLen
            obtain ⟨arg1, arg2, rfl⟩ := argsShape
            obtain ⟨words, getWords, lengthEq⟩ := stateRel_getVars conf l1 l2 source target locs
              [arg1, arg2] [.number a, .number b] related argsEq
            have wordsShape : ∃ x y, words = [x, y] := by
              cases words with
              | nil => simp at lengthEq
              | cons x rest =>
                cases rest with
                | nil => simp at lengthEq
                | cons y rest =>
                  cases rest with
                  | nil => exact ⟨x, y, rfl⟩
                  | cons z rest => simp at lengthEq
            obtain ⟨word1, word2, rfl⟩ := wordsShape
            let next := DataSem.doStack (.wordOp (.wordTest .w8 test)) [.number a, .number b]
              (DataSem.doLimSafe source (.wordOp (.wordTest .w8 test)) [.number a, .number b])
            have nextRel : stateRel conf l1 l2 next target none locs :=
              stateRel_doStack conf l1 l2 _ target locs _ _
                (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
            let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
            let envs := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
            have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain next.locals target envs [arg1, arg2]
              [.number a, .number b] [word1, word2] (by
                refine ⟨?_, ?_, getWords⟩
                · simpa [locals, envs] using hmem
                · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq)
            have good := nextRel.2.2.2.2.2.2.1
            have smallA : smallInt width a := by
              rcases good with h | h <;> subst width <;> simp [smallInt] <;> omega
            have smallB : smallInt width b := by
              rcases good with h | h <;> subst width <;> simp [smallInt] <;> omega
            have root1 : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                target.store target.memory target.mdomain
                ((.number a, word1) :: (.number b, word2) :: locals ++ envs) := by
              simpa [locals, envs, List.append_assoc] using roots
            have root2 := memoryRel_tl conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain (.number a, word1)
              ((.number b, word2) :: locals ++ envs) root1
            have eq1 := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain a word1 _ ⟨good, smallA, root1⟩
            have eq2 := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
              target.store target.memory target.mdomain b word2 _ ⟨good, smallB, root2⟩
            subst word1
            subst word2
            have bothReads : target.getVar (adjustVar arg1) = some (.word (smallnum a)) ∧
                target.getVar (adjustVar arg2) = some (.word (smallnum b)) := by
              cases h1 : target.getVar (adjustVar arg1) <;> cases h2 : target.getVar (adjustVar arg2) <;>
                simp_all [WordSemStateFiniteExact.getVars]
            have aWord : (smallnum a : BitVec width).toNat = 4 * a.toNat := by
              rcases good with h | h <;> subst width <;>
                simp [smallnum, Int.not_lt.mpr bounds.1, BitVec.toNat_ofNat] <;> omega
            have bWord : (smallnum b : BitVec width).toNat = 4 * b.toNat := by
              rcases good with h | h <;> subst width <;>
                simp [smallnum, Int.not_lt.mpr bounds.2.2.1, BitVec.toNat_ofNat] <;> omega
            have wordEq : (smallnum a : BitVec width) = smallnum b ↔ a = b := by
              constructor
              · exact smallnum_injective good a b smallA smallB
              · intro eq; rw [eq]
            have wordLt : (smallnum a : BitVec width) < smallnum b ↔ a < b := by
              rw [BitVec.lt_def, aWord, bWord]
              omega
            have wordGt : (smallnum b : BitVec width) < smallnum a ↔ b < a := by
              rw [BitVec.lt_def, aWord, bWord]
              omega
            let answer := match test with
              | .equal => decide (a = b)
              | .compare .lt => decide (a < b)
              | .compare .leq => decide (a ≤ b)
              | _ => false
            let out : BitVec width := if answer then 18 else 2
            have boolRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                target.store target.memory target.mdomain
                ((DataSem.boolValue answer, .word out) :: locals ++ envs) := by
              apply memoryRel_bool conf target.be (holThe next.tstamps) next.refs next.space
                target.store target.memory target.mdomain (locals ++ envs) _ _
              refine ⟨?_, good, ?_, ?_⟩
              · simpa [locals, envs] using hmem
              · intro h; simp [out, h]
              · intro h; simp [out, h]
            have updated := stateRel_insertRoot conf l1 l2 next target locs dest
              (DataSem.boolValue answer) (.word out) nextRel (by simpa [locals, envs] using boolRoot)
            cases test with
            | equal =>
              simp at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨none, target.setVar (adjustVar dest) (.word out), ?_, by simp, ?_⟩
              · change WordSemStateFiniteExact.evaluate
                  (setBool (adjustVar dest) .equal (adjustVar arg1) (.reg (adjustVar arg2))) target = _
                simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                  bothReads.1, bothReads.2, out, answer]
                by_cases h : a = b
                · subst b; simp
                · have ne : (smallnum a : BitVec width) ≠ smallnum b := fun eq => h (wordEq.mp eq)
                  simp [h, beq_eq_false_iff_ne.mpr ne]
              · simpa [next, answer] using updated
            | altCompare cmp => simp at run
            | compare cmp =>
              cases cmp with
              | lt =>
                simp at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨none, target.setVar (adjustVar dest) (.word out), ?_, by simp, ?_⟩
                · change WordSemStateFiniteExact.evaluate
                    (setBool (adjustVar dest) .lower (adjustVar arg1) (.reg (adjustVar arg2))) target = _
                  simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                    bothReads.1, bothReads.2, wordLt, out, answer]
                  by_cases h : a < b <;> simp [h]
                · simpa [next, answer] using updated
              | leq =>
                simp at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨none, target.setVar (adjustVar dest) (.word out), ?_, by simp, ?_⟩
                · change WordSemStateFiniteExact.evaluate
                    (setBool (adjustVar dest) .notLower (adjustVar arg2) (.reg (adjustVar arg1))) target = _
                  simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                    bothReads.1, bothReads.2, wordGt, out, answer]
                  by_cases h : b < a
                  · have hn : ¬ a ≤ b := by omega
                    simp [h, hn]
                  · have hl : a ≤ b := by omega
                    simp [h, hl]
                · simpa [next, answer] using updated
              | gt => simp at run
              | geq => simp at run
          · simp [bounds] at run
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
