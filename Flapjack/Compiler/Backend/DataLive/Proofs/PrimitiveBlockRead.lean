import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveThunk

/-! Read-only block primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Simple block inspections return equal results on related states. -/
theorem stateRel_doAppAux_simpleBlock {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (simple : isSimpleBlock op = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp op) args source) (doAppAux (.blockOp op) args target) := by
  cases op <;> simp [isSimpleBlock] at simple
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi, appRel]
        all_goals exact related

/-- Boolean block inspections return equal results on related states. -/
theorem stateRel_doAppAux_boolBlock {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (boolean : isBoolBlock op = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp op) args source) (doAppAux (.blockOp op) args target) := by
  cases op <;> simp [isBoolBlock] at boolean
  case boolNot =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases found : destBool first <;> simp [doAppAux, applyNonFfi, appRel, found]
        exact related
  case boolTest test =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases foundFirst : destBool first <;> simp [doAppAux, applyNonFfi, appRel, foundFirst]
          cases foundSecond : destBool second <;> simp
          exact related

/-- Block-bounds checks return equal results on related states. -/
theorem stateRel_doAppAux_boundsBlock {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp .boundsCheckBlock) args source)
      (doAppAux (.blockOp .boundsCheckBlock) args target) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        exact related

/-- Element reads return matching values for direct blocks and for arrays
looked up through the related reference stores. -/
theorem stateRel_doAppAux_elemAt {C F : Type} (source target : State C F) (live : NumSet)
    (index : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.elemAt index)) args source)
      (doAppAux (.blockOp (.elemAt index)) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases first <;> simp [doAppAux, applyNonFfi, appRel]
      case block timestamp tag values =>
        cases found : values[index]? <;> simp
        exact related
      case refPtr flag ptr =>
        cases found : sptLookup ptr source.refs with
        | none => simp [found, ← refs]
        | some entry =>
          cases entry <;> simp [found, ← refs]
          case valueArray values =>
            cases slot : values[index]? <;> simp
            exact related

/-- Constant comparisons return matching results for immediate and
reference-backed values. -/
theorem stateRel_doAppAux_equalConst {C F : Type} (source target : State C F) (live : NumSet)
    (part : ClosLang.ConstPart) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.equalConst part)) args source)
      (doAppAux (.blockOp (.equalConst part)) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases part <;> cases first <;> simp [doAppAux, applyNonFfi, appRel]
      case str.refPtr text flag ptr =>
        cases found : sptLookup ptr source.refs with
        | none => simp [found, ← refs]
        | some entry =>
          cases entry <;> simp [found, ← refs]
          case byteArray mutable bytes =>
            cases mutable <;> simp
            exact related
      all_goals exact related

/-- The auxiliary dispatcher preserves related states for every block
operation classified as pure. This is untagged pending evaluator review. -/
theorem stateRel_doAppAux_pureBlock {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (pure : isPure (.blockOp op) = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp op) args source) (doAppAux (.blockOp op) args target) := by
  cases op <;> simp [isPure] at pure
  case elemAt index => exact stateRel_doAppAux_elemAt source target live index args related
  case tagLenEq tag length => exact stateRel_doAppAux_simpleBlock source target live _ args rfl related
  case lenEq length => exact stateRel_doAppAux_simpleBlock source target live _ args rfl related
  case tagEq tag => exact stateRel_doAppAux_simpleBlock source target live _ args rfl related
  case lengthBlock => exact stateRel_doAppAux_simpleBlock source target live _ args rfl related
  case boolTest test => exact stateRel_doAppAux_boolBlock source target live _ args rfl related
  case boolNot => exact stateRel_doAppAux_boolBlock source target live _ args rfl related
  case boundsCheckBlock => exact stateRel_doAppAux_boundsBlock source target live args related
  case constant constant => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  case equalConst part => exact stateRel_doAppAux_equalConst source target live part args related

/-- Pure block operations preserve the liveness relation through resource
accounting and the full primitive dispatcher. -/
theorem stateRel_doApp_pureBlock {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (pure : isPure (.blockOp op) = true)
    (related : stateRel source target live) :
    appRel live (doApp (.blockOp op) args source) (doApp (.blockOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.blockOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact stateRel_doAppAux_pureBlock _ _ live op args pure
      (stateRel_doStackLim sourceNext targetNext live (.blockOp op) args nextRel)

/-- Pure block assignments satisfy the liveness simulation with or without
a live-name annotation. -/
theorem simulationFor_assign_pureBlock_all {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) (pure : isPure (.blockOp op) = true) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp op) args names) live := by
  cases names with
  | none =>
    cases retained : ((sptLookup dest live).isNone && isPure (.blockOp op)) with
    | false =>
      apply simulationFor_retained_of_appRel dest (.blockOp op) args live retained
      intro source target values related
      exact stateRel_doApp_pureBlock source target _ op values pure related
    | true =>
      have dead : sptLookup dest live = none := by simpa [pure] using retained
      exact simulationFor_removed_block dest op args live pure dead
  | some names =>
    apply simulationFor_annotated_of_appRel dest (.blockOp op) args names live
    intro source target values related
    exact stateRel_doApp_pureBlock source target _ op values pure related

/-- Related reference stores give the same structural equality result. -/
theorem stateRel_doAppAux_equal {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp .equal) args source) (doAppAux (.blockOp .equal) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases result : doEq source.refs first second <;> simp [doAppAux, applyNonFfi, appRel, ← refs, result]
        exact related

/-- Structural equality assignments satisfy the liveness simulation with
or without a live-name annotation. -/
theorem simulationFor_assign_equal_all {C F : Type} (dest : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp .equal) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp .equal) values source) (doApp (.blockOp .equal) values target) := by
    intro source target values related
    simp only [doApp]
    rcases stateRel_doSpace source target _ (.blockOp .equal) values related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
    · simp [failed.1, failed.2, appRel]
    · simp only [sourceRun, targetRun]
      exact stateRel_doAppAux_equal _ _ _ values (stateRel_doStackLim sourceNext targetNext _ (.blockOp .equal) values nextRel)
  cases names with
  | none =>
    apply simulationFor_retained_of_appRel dest (.blockOp .equal) args live (by simp [isPure])
    exact primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp .equal) args names live primitiveRel

end Flapjack.Compiler.Backend.DataLive
