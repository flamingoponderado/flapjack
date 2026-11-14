module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PureMemory

@[expose] public section

/-! Successful pure primitive application for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Auxiliary string-comparison case for the full pure-success theorem; it has no separate HOL declaration. -/
private theorem stringCmp_aux_same {C F : Type} (fast : Bool) (cmp : Opb) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp (.stringCmp fast cmp)) args state = .val (value, next)) : next = state := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        case refPtr.refPtr f a g b =>
          cases ha : sptLookup a state.refs with
          | none => simp [ha] at run
          | some left =>
            cases left <;> simp [ha] at run
            case byteArray m left =>
              cases hb : sptLookup b state.refs with
              | none => simp [hb] at run
              | some right =>
                cases right <;> simp [hb] at run
                all_goals exact run.2.symm

/-- Auxiliary dispatcher frame for the full pure-success theorem; it has no separate HOL declaration. -/
private theorem pure_aux_same {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (pure : isPure op = true) (run : doAppAux op args state = .val (value, next)) : next = state := by
  cases op with
  | ffi name => simp [isPure] at pure
  | install => simp [isPure] at pure
  | thunkOp op => simp [isPure] at pure
  | label n =>
    cases args with
    | nil =>
      by_cases found : (sptLookup n state.code).isSome <;> simp [doAppAux, applyNonFfi, found] at run
      exact run.2.symm
    | cons x xs => simp [doAppAux, applyNonFfi] at run
  | intOp op =>
    cases found : doIntApp op args <;> simp [doAppAux, applyNonFfi, found] at run
    exact run.2.symm
  | wordOp op =>
    cases found : doWordApp op args <;> simp [doAppAux, applyNonFfi, found] at run
    exact run.2.symm
  | globOp op => exact pure_global_aux_same op args state next value pure run
  | blockOp op =>
    cases op <;> simp [isPure] at pure
    case elemAt n => exact elemAt_aux_same n args state next value run
    case tagLenEq a b => exact simple_block_aux_same _ args state next value rfl run
    case lenEq a => exact simple_block_aux_same _ args state next value rfl run
    case tagEq a => exact simple_block_aux_same _ args state next value rfl run
    case lengthBlock => exact simple_block_aux_same _ args state next value rfl run
    case boolTest a => exact bool_block_aux_same _ args state next value rfl run
    case boolNot => exact bool_block_aux_same _ args state next value rfl run
    case boundsCheckBlock => exact boundsCheckBlock_aux_same args state next value run
    case constant a => cases args <;> simp [doAppAux, applyNonFfi] at run
    case equalConst a => exact equalConst_aux_same a args state next value run
  | memOp op =>
    cases op <;> simp [isPure] at pure
    case el => exact memEl_aux_same args state next value run
    case length => exact memoryLength_aux_same _ args state next value rfl run
    case lengthByte => exact memoryLength_aux_same _ args state next value rfl run
    case derefByte => exact derefByte_aux_same args state next value run
    case concatByteVec => exact False.elim (unavailable_mem_aux _ args state next value rfl run)
    case toListByte => exact False.elim (unavailable_mem_aux _ args state next value rfl run)
    case lengthByteVec => exact False.elim (unavailable_mem_aux _ args state next value rfl run)
    case derefByteVec => exact False.elim (unavailable_mem_aux _ args state next value rfl run)
    case stringCmp fast cmp => exact stringCmp_aux_same fast cmp args state next value run
    case boundsCheckArray => exact memoryBounds_aux_same _ args state next value rfl run
    case boundsCheckByte loose => exact memoryBounds_aux_same _ args state next value rfl run

/-- Internal space-accounting fact for successful pure operations; it has no separate HOL declaration. -/
private theorem pure_space {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (pure : isPure op = true)
    (notGreater : op ≠ .intOp .greater) (notGreaterEq : op ≠ .intOp .greaterEq) :
    doSpace op args state = some state := by
  cases op with
  | ffi name => simp [isPure] at pure
  | install => simp [isPure] at pure
  | thunkOp op => simp [isPure] at pure
  | label n => simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  | intOp op => cases op <;> simp_all [isPure, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  | wordOp op => exact pure_word_doSpace op args state pure
  | blockOp op => exact pure_block_doSpace op args state pure
  | globOp op => exact pure_global_doSpace op args state pure
  | memOp op => exact pure_mem_doSpace op args state pure

/-- A successful pure application changes only the safety and stack-maximum
fields. The evaluator inherits the real-model assumption in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_liveProofScript.sml" "is_pure_do_app_Rval_IMP"]
theorem isPure_doApp_success {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (value : DataSem.Value) (next : State C F)
    (premises : isPure op = true ∧ doApp op args state = .val (value, next)) :
    ∃ safe smax, next = {state with safeForSpace := safe, stackMax := smax} := by
  obtain ⟨pure, run⟩ := premises
  have notGreater : op ≠ .intOp .greater := by
    intro equal
    subst op
    simp [doApp] at run
  have notGreaterEq : op ≠ .intOp .greaterEq := by
    intro equal
    subst op
    simp [doApp] at run
  have space := pure_space op args state pure notGreater notGreaterEq
  cases op with
  | ffi name => simp [isPure] at pure
  | install => simp [isPure] at pure
  | thunkOp op => simp [isPure] at pure
  | intOp op =>
    cases op with
    | greater => simp [doApp] at run
    | greaterEq => simp [doApp] at run
    | _ =>
      simp only [doApp, space] at run
      have eq := pure_aux_same _ args _ next value pure run
      subst next
      exact ⟨_, _, rfl⟩
  | _ =>
    simp only [doApp, space] at run
    have eq := pure_aux_same _ args _ next value pure run
    subst next
    exact ⟨_, _, rfl⟩

/-- A dead pure assignment is simulated using the complete HOL success
frame above and the original pure-operation error result. -/
theorem simulationFor_removed_pure {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : NumSet) (pure : isPure op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest op names none) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target live := by simpa [compile, dead, pure] using related
  by_cases invalid : (DataLang.opRequiresNames op == true) = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars names source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some args =>
      cases app : doApp op args source with
      | err error =>
        have errorEq := pure_doApp_error op args source error pure app
        subst error
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | val pair =>
        obtain ⟨value, applied⟩ := pair
        have appliedRel : stateRel applied source live := by
          obtain ⟨safe, smax, equal⟩ := isPure_doApp_success op args source value applied ⟨pure, app⟩
          subst applied
          simp [stateRel]
        have finalRel := stateRel_setVar_dead applied target live dest value
          (stateRel_trans applied source target live appliedRel initial) dead
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · simp [compile, dead, pure, DataSem.evaluate]
        · cases op <;> try simp [isPure] at pure <;> cases applied <;>
            simpa [installSfs, postLive] using finalRel

end Flapjack.Compiler.Backend.DataLive
