module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Roots
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Const
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Bool
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State

@[expose] public section

/-! Boolean negation in the data-to-word assignment simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps

namespace assignBoolNotMap
/-- Canonical target-state roundtrip for the assignment simulation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end assignBoolNotMap

/-- The empty-block branch of `memory_rel_Block_IMP` gives the concrete
Boolean word used in the HOL Boolean assignment proofs. This is a local
factoring of the empty-block case, with no separate HOL declaration. -/
theorem boolBlock_word {width : Nat} [NeZero width] (conf : Config)
    (be : Bool) (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (location : WordLocW width) (vars : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.block stamp tag [], location) :: vars))
    (good : goodDimindex width) :
    location = .word (BitVec.ofNat width tag * 16 + 2) := by
  obtain ⟨w, eq, data⟩ := memoryRel_blockImp conf be next refs space store memory domain
    stamp tag [] location vars ⟨rel, good⟩
  rw [data.1] at eq
  exact eq

/-- Boolean negation satisfies the original data-to-word assignment goal. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_BoolNot"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignBoolNot_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value)
    (result : Flapjack.Compiler.Backend.DataSem.Value)
    (boolOp : op = .blockOp .boolNot)
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
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        DataSem.doAppAux, DataSem.applyNonFfi] at run
    | cons value values =>
      cases values with
      | cons head tail => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi] at run
      | nil =>
        cases value with
        | number i => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool] at run
        | word64 w => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool] at run
        | codePtr p => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool] at run
        | refPtr b p => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
            DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool] at run
        | block stamp tag xs =>
          by_cases valid : xs = [] ∧ tag < 2
          · obtain ⟨rfl, bound⟩ := valid
            have le : tag ≤ 1 := by omega
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool, le] at run
            obtain ⟨rfl, rfl⟩ := run
            have argLen : args.length = 1 := by
              have h := DataSpace.getVars_length args source.locals [.block stamp tag []] argsEq
              simpa using h.symm
            cases args with
            | nil => simp at argLen
            | cons arg args =>
              cases args with
              | cons extra tail => simp at argLen
              | nil =>
                have sourceFound : DataSem.getVar arg source.locals = some (.block stamp tag []) := by
                  cases h : DataSem.getVar arg source.locals <;> simp_all [DataSem.getVars]
                obtain ⟨word, targetFound⟩ :=
                  stateRel_getVar conf l1 l2 source target none locs arg (.block stamp tag []) related sourceFound
                let next := DataSem.doStack (.blockOp .boolNot) [.block stamp tag []]
                  (DataSem.doLimSafe source (.blockOp .boolNot) [.block stamp tag []])
                have nextRel : stateRel conf l1 l2 next target none locs :=
                  stateRel_doStack conf l1 l2 _ target locs _ _
                    (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
                let locals := joinEnv next.locals (sptToAList (sptInter target.locals (adjustSet next.locals)))
                let rest := [(theGlobal next.global, holFapply target.store .globals)] ++ flatStack next.stack target.stack
                have hmem := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                have roots := memoryRel_lookupVars conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain next.locals target rest [arg]
                  [.block stamp tag []] [word] (by
                    refine ⟨?_, ?_, ?_⟩
                    · simpa [locals, rest] using hmem
                    · simpa [next, DataSem.doStack, DataSem.doLimSafe] using argsEq
                    · simp [WordSemStateFiniteExact.getVars, targetFound])
                have good := nextRel.2.2.2.2.2.2.1
                have wordEq := boolBlock_word conf target.be (holThe next.tstamps) next.refs next.space
                  target.store target.memory target.mdomain stamp tag word (locals ++ rest)
                  (by simpa [locals] using roots) good
                subst word
                let out : BitVec width := (BitVec.ofNat width tag * 16 + 2) ^^^ 16
                have outputTrue : (Bool.not (decide (tag = 1)) = true) → out = 18 := by
                  intro truth
                  have z : tag = 0 := by simp at truth; omega
                  subst tag
                  rcases good with h | h <;> subst width <;> decide
                have outputFalse : (Bool.not (decide (tag = 1)) = false) → out = 2 := by
                  intro truth
                  have o : tag = 1 := by simpa using truth
                  subst tag
                  rcases good with h | h <;> subst width <;> decide
                have boolRoot : memoryRel conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain
                    ((DataSem.boolValue (!(decide (tag = 1))), .word out) :: locals ++ rest) := by
                  apply memoryRel_bool conf target.be (holThe next.tstamps) next.refs next.space
                    target.store target.memory target.mdomain (locals ++ rest) _ _
                  refine ⟨?_, good, ?_, ?_⟩
                  · simpa [locals, rest] using hmem
                  · intro h; simp [outputTrue h]
                  · intro h; simp [outputFalse h]
                have updated := stateRel_insertRoot conf l1 l2 next target locs dest
                  (DataSem.boolValue (!(decide (tag = 1)))) (.word out) nextRel (by
                    simpa [locals, rest] using boolRoot)
                have compiled : compileAssign (width := width) conf n l dest (.blockOp .boolNot) [arg] none =
                    assignBoolNot l dest arg := by rfl
                refine ⟨none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word out) target, ?_, ?_, ?_⟩
                · simp [compiled, assignBoolNot, WordSemStateFiniteExact.evaluate,
                    WordSemStateFiniteExact.wordExp, targetFound, out, theWords, wordOpHOL, wordOp]
                · simp
                · simpa [next] using updated
          · have invalid : ¬ (xs = [] ∧ tag ≤ 1) := by
              intro h
              exact valid ⟨h.1, by omega⟩
            simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
              DataSem.doAppAux, DataSem.applyNonFfi, DataSem.destBool, invalid] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
