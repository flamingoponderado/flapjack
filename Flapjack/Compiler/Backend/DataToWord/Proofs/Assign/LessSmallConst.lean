module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Less
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordTest

@[expose] public section

/-! Small-constant comparison assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace LessSmallConstWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LessSmallConstWitness

/-- The compiler equation used in the small-constant assignment proof. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_LessConstSmall"
  (words_as_type_indexed_bitvec)]
theorem assignLessConstSmallEquation {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (sec l dest i : Nat) (args : List Nat) (names : Option NumSet) :
    (compileAssign conf sec l dest (.intOp (.lessConstSmall i)) args names :
      WordLangProgHOL (BitVec width) × Nat) =
      match args with
      | [v] => (.ite .less (adjustVar v) (.imm (BitVec.ofNat width (4 * i)))
          (.assign (adjustVar dest) (.const 18)) (.assign (adjustVar dest) (.const 2)), l)
      | _ => (.skip, l) := by
  cases args with
  | nil => rfl
  | cons x xs => cases xs <;> rfl

/-- A small-constant comparison satisfies the original assignment simulation.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_LessSmallConst"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignLessSmallConst_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ i, op = .intOp (.lessConstSmall i))
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
  obtain ⟨i, rfl⟩ := opIs
  have namesNone : names = none := by
    cases names <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames ⊢
  subst names
  have cutSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
  subst cut
  cases values with
  | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
      DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp] at run
  | cons a tail =>
    cases tail with
    | cons b tail => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp] at run
    | nil =>
      cases a <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doIntApp]
      rename_i a
      by_cases bounds : 0 ≤ a ∧ a ≤ 1000000 ∧ i < 1000000
      · simp [bounds] at run
        obtain ⟨rfl, rfl⟩ := run
        have argLen := DataSpace.getVars_length args source.locals [.number a] argsEq
        have argsShape : ∃ x, args = [x] := by
          cases args with
          | nil => simp at argLen
          | cons x rest =>
            cases rest with
            | nil => exact ⟨x, rfl⟩
            | cons y rest => simp at argLen
        obtain ⟨arg, rfl⟩ := argsShape
        have dataRead : DataSem.getVar arg source.locals = some (.number a) := by
          cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
        obtain ⟨word, wordRead⟩ := stateRel_getVar conf l1 l2 source target none locs arg _ related dataRead
        let next := DataSem.doStack (.intOp (.lessConstSmall i)) [.number a]
          (DataSem.doLimSafe source (.intOp (.lessConstSmall i)) [.number a])
        have nextRel : stateRel conf l1 l2 next target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
        let envs := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
        have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
          target.store target.memory target.mdomain next.locals target envs [arg] [.number a] [word] (by
            refine ⟨?_, ?_, ?_⟩
            · simpa [locals, envs] using hmem
            · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
            · simp [WordSemStateFiniteExact.getVars, wordRead])
        have good := nextRel.2.2.2.2.2.2.1
        have smallA : smallInt width a := by
          rcases good with h | h <;> subst width <;> simp [smallInt] <;> omega
        have smallI : smallInt width (Int.ofNat i) := by
          rcases good with h | h <;> subst width <;> simp [smallInt] <;> omega
        have eq := memoryRel_numberImp conf target.be (holThe next.tstamps) next.refs next.space
          target.store target.memory target.mdomain a word _
          ⟨good, smallA, by simpa [locals, envs] using roots⟩
        subst word
        let answer := decide (a < Int.ofNat i)
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
        have immEq : (BitVec.ofNat width (4 * i)) = smallnum (Int.ofNat i) := by
          simp [smallnum, Int.not_lt.mpr (Int.natCast_nonneg i)]
          congr 1
        have compare : (a < Int.ofNat i) ↔
            Compiler.Encoders.Asm.holAsmSignedLess (smallnum a : BitVec width)
              (BitVec.ofNat width (4 * i)) = true := by
          rw [immEq, signedLessEq _ _ good]
          exact numLessThm a (Int.ofNat i) ⟨good, smallA, smallI⟩
        refine ⟨none, target.setVar (adjustVar dest) (.word out), ?_, by simp, ?_⟩
        · rw [assignLessConstSmallEquation]
          change WordSemStateFiniteExact.evaluate
            (setBool (adjustVar dest) .less (adjustVar arg) (.imm (BitVec.ofNat width (4 * i)))) target = _
          simp [setBool, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getVarImm, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
            wordRead, out, answer]
          by_cases h : a < Int.ofNat i
          · have cmp := compare.mp h
            simp [cmp]
            split <;> simp_all
          · have cmp : Compiler.Encoders.Asm.holAsmSignedLess (smallnum a : BitVec width)
                  (BitVec.ofNat width (4 * i)) = false := by
              cases eq : Compiler.Encoders.Asm.holAsmSignedLess (smallnum a : BitVec width)
                    (BitVec.ofNat width (4 * i)) with
              | false => rfl
              | true => exact (h (compare.mpr eq)).elim
            simp [cmp]
            split <;> simp_all
        · simpa [next, answer] using updated
      · simp [bounds] at run
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
