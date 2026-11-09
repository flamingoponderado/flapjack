import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveBlockRead

/-! Allocating block primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Related states construct the same block and advance timestamps equally.
This is untagged pending evaluator and carrier review. -/
theorem stateRel_doAppAux_cons {C F : Type} (source target : State C F) (live : NumSet)
    (tag : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.cons tag)) args source)
      (doAppAux (.blockOp (.cons tag)) args target) := by
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simpa [doAppAux, applyNonFfi, appRel] using related
  | cons first rest =>
    cases found : source.tstamps <;>
      simpa [doAppAux, applyNonFfi, appRel, withFreshTimestamp, checkLim, found, ← stamps, stateRel] using related

/-- Lifting an auxiliary block relation through space and stack accounting. -/
theorem stateRel_doApp_block_of_aux {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (related : stateRel source target live)
    (aux : ∀ left right : State C F, stateRel left right live →
      appRel live (doAppAux (.blockOp op) args left) (doAppAux (.blockOp op) args right)) :
    appRel live (doApp (.blockOp op) args source) (doApp (.blockOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.blockOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact aux _ _ (stateRel_doStackLim sourceNext targetNext live (.blockOp op) args nextRel)

/-- Block construction assignments satisfy the liveness simulation with
or without a live-name annotation. -/
theorem simulationFor_assign_cons_all {C F : Type} (dest tag : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.cons tag)) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp (.cons tag)) values source) (doApp (.blockOp (.cons tag)) values target) := by
    intro source target values related
    apply stateRel_doApp_block_of_aux source target _ (.cons tag) values related
    intro left right relation
    exact stateRel_doAppAux_cons left right _ tag values relation
  cases names with
  | none => exact simulationFor_retained_of_appRel dest (.blockOp (.cons tag)) args live (by simp [isPure]) primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp (.cons tag)) args names live primitiveRel

/-- Related states construct the same block from a list and advance
timestamps equally. -/
theorem stateRel_doAppAux_fromList {C F : Type} (source target : State C F) (live : NumSet)
    (tag : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.fromList tag)) args source)
      (doAppAux (.blockOp (.fromList tag)) args target) := by
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi, appRel]
        case number length =>
          cases found : valueToList second with
          | none => simp
          | some values =>
            by_cases same : length = (values.length : Int)
            · cases values with
              | nil => simpa [found, same, appRel] using related
              | cons head tail =>
                cases timestamp : source.tstamps <;>
                  simpa [found, same, appRel, withFreshTimestamp, checkLim, timestamp, ← stamps, stateRel] using related
            · simp [same]

/-- List-to-block construction satisfies liveness simulation for both
annotation forms. -/
theorem simulationFor_assign_fromList_all {C F : Type} (dest tag : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.fromList tag)) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp (.fromList tag)) values source) (doApp (.blockOp (.fromList tag)) values target) := by
    intro source target values related
    apply stateRel_doApp_block_of_aux source target _ (.fromList tag) values related
    intro left right relation
    exact stateRel_doAppAux_fromList left right _ tag values relation
  cases names with
  | none => exact simulationFor_retained_of_appRel dest (.blockOp (.fromList tag)) args live (by simp [isPure]) primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp (.fromList tag)) args names live primitiveRel

/-- Related states append the same lists and advance timestamps equally. -/
theorem stateRel_doAppAux_listAppend {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp .listAppend) args source)
      (doAppAux (.blockOp .listAppend) args target) := by
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases xs : valueToList first with
        | none => simp [doAppAux, applyNonFfi, xs, appRel]
        | some values =>
          cases ys : valueToList second with
          | none => simp [doAppAux, applyNonFfi, xs, ys, appRel]
          | some others =>
            cases timestamp : source.tstamps <;>
              simpa [doAppAux, applyNonFfi, xs, ys, appRel, withFreshTimestamp, checkLim, timestamp, ← stamps, stateRel] using related

/-- List append assignments satisfy the liveness simulation for both
annotation forms. -/
theorem simulationFor_assign_listAppend_all {C F : Type} (dest : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp .listAppend) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp .listAppend) values source) (doApp (.blockOp .listAppend) values target) := by
    intro source target values related
    apply stateRel_doApp_block_of_aux source target _ .listAppend values related
    intro left right relation
    exact stateRel_doAppAux_listAppend left right _ values relation
  cases names with
  | none => exact simulationFor_retained_of_appRel dest (.blockOp .listAppend) args live (by simp [isPure]) primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp .listAppend) args names live primitiveRel

/-- Related states build the same constant, reference store and timestamp. -/
theorem stateRel_doAppAux_build {C F : Type} (source target : State C F) (live : NumSet)
    (parts : List ClosLang.ConstPart) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.build parts)) args source)
      (doAppAux (.blockOp (.build parts)) args target) := by
  have refs := related.2.2.2.2.1
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | cons first rest => simp [doAppAux, applyNonFfi, appRel]
  | nil =>
    cases built : doBuildConst parts source.refs source.tstamps with
    | mk value remaining =>
      obtain ⟨newRefs, newStamps⟩ := remaining
      simp [doAppAux, applyNonFfi, appRel, ← refs, ← stamps, built]
      rcases related with ⟨code, clock, space, ffi, _, global, handler, stack, compiler, oracle, _, limits, frames, locals⟩
      exact ⟨code, clock, space, ffi, rfl, global, handler, stack, compiler, oracle, rfl, limits, frames, locals⟩

/-- Constant construction assignments satisfy the liveness simulation for
both annotation forms. -/
theorem simulationFor_assign_build_all {C F : Type} (dest : Nat) (parts : List ClosLang.ConstPart)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.build parts)) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp (.build parts)) values source) (doApp (.blockOp (.build parts)) values target) := by
    intro source target values related
    apply stateRel_doApp_block_of_aux source target _ (.build parts) values related
    intro left right relation
    exact stateRel_doAppAux_build left right _ parts values relation
  cases names with
  | none => exact simulationFor_retained_of_appRel dest (.blockOp (.build parts)) args live (by simp [isPure]) primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp (.build parts)) args names live primitiveRel

/-- Related states extend a block with the same values and timestamps. -/
theorem stateRel_doAppAux_consExtend {C F : Type} (source target : State C F) (live : NumSet)
    (tag : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp (.consExtend tag)) args source)
      (doAppAux (.blockOp (.consExtend tag)) args target) := by
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons third rest =>
        cases rest with
        | nil => simp [doAppAux, applyNonFfi, appRel]
        | cons fourth rest =>
          cases first <;> simp [doAppAux, applyNonFfi, appRel]
          case block timestamp oldTag previous =>
            cases second <;> try simp
            case number lower =>
              cases third <;> try simp
              case number length =>
                cases fourth <;> try simp
                case number total =>
                  by_cases bad : lower < 0 ∨ length < 0 ∨ (previous.length : Int) < lower + length ∨
                      total = 0 ∨ ¬total = (rest.length : Int) + length
                  · simp [bad]
                  · cases stamp : source.tstamps <;>
                      simpa [bad, appRel, withFreshTimestamp, checkLim, stamp, ← stamps, stateRel] using related

/-- Block-extension assignments satisfy the liveness simulation for both
annotation forms. -/
theorem simulationFor_assign_consExtend_all {C F : Type} (dest tag : Nat) (args : List Nat)
    (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.consExtend tag)) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.blockOp (.consExtend tag)) values source) (doApp (.blockOp (.consExtend tag)) values target) := by
    intro source target values related
    apply stateRel_doApp_block_of_aux source target _ (.consExtend tag) values related
    intro left right relation
    exact stateRel_doAppAux_consExtend left right _ tag values relation
  cases names with
  | none => exact simulationFor_retained_of_appRel dest (.blockOp (.consExtend tag)) args live (by simp [isPure]) primitiveRel
  | some names => exact simulationFor_annotated_of_appRel dest (.blockOp (.consExtend tag)) args names live primitiveRel

/-- Every block assignment satisfies the liveness simulation. This case is
untagged pending source evaluator and state-carrier review. -/
theorem simulationFor_assign_block_all {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp op) args names) live := by
  by_cases pure : isPure (.blockOp op) = true
  · exact simulationFor_assign_pureBlock_all dest op args names live pure
  · cases op <;> simp [isPure] at pure
    case cons tag => exact simulationFor_assign_cons_all dest tag args names live
    case consExtend tag => exact simulationFor_assign_consExtend_all dest tag args names live
    case fromList tag => exact simulationFor_assign_fromList_all dest tag args names live
    case listAppend => exact simulationFor_assign_listAppend_all dest args names live
    case equal => exact simulationFor_assign_equal_all dest args names live
    case build parts => exact simulationFor_assign_build_all dest parts args names live

end Flapjack.Compiler.Backend.DataLive
