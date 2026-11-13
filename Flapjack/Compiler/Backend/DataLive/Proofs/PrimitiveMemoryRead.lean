module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveMemoryAlloc

@[expose] public section

/-! Read-only memory primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Related states agree on memory-length operations. -/
theorem stateRel_doAppAux_memoryLength {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.MemOp) (args : List DataSem.Value) (lengthOp : isMemoryLength op = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.memOp op) args source) (doAppAux (.memOp op) args target) := by
  have refs := related.2.2.2.2.1
  cases op <;> simp [isMemoryLength] at lengthOp
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi, appRel]
        case refPtr flag ptr =>
          cases found : sptLookup ptr source.refs with
          | none => simp [found, ← refs]
          | some entry =>
            cases entry <;> simp [found, ← refs]
            all_goals exact related

/-- Related states agree on array and byte-array bounds checks. -/
theorem stateRel_doAppAux_memoryBounds {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.MemOp) (args : List DataSem.Value) (boundsOp : isMemoryBounds op = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.memOp op) args source) (doAppAux (.memOp op) args target) := by
  have refs := related.2.2.2.2.1
  cases op <;> simp [isMemoryBounds] at boundsOp
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr source.refs with
            | none => simp [found, ← refs]
            | some entry =>
              cases entry <;> simp [found, ← refs]
              all_goals exact related

/-- Related states agree on indexed value reads. -/
theorem stateRel_doAppAux_memEl {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .el) args source) (doAppAux (.memOp .el) args target) := by
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
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        case block.number timestamp tag values index =>
          by_cases negative : index < 0
          · simp [negative]
          · cases slot : values[index.toNat]? <;> simp [negative]
            exact related
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr source.refs with
          | none => simp [found, ← refs]
          | some entry =>
            cases entry <;> simp [found, ← refs]
            case valueArray values =>
              by_cases negative : index < 0
              · simp [negative]
              · cases slot : values[index.toNat]? <;> simp [negative]
                exact related

/-- Related states agree on indexed byte reads. -/
theorem stateRel_doAppAux_derefByte {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .derefByte) args source) (doAppAux (.memOp .derefByte) args target) := by
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
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr source.refs with
          | none => simp [found, ← refs]
          | some entry =>
            cases entry <;> simp [found, ← refs]
            case byteArray mutability bytes =>
              by_cases negative : index < 0
              · simp [negative]
              · cases slot : bytes[index.toNat]? <;> simp [negative]
                exact related

/-- Related states agree on byte-string comparisons. -/
theorem stateRel_doAppAux_stringCmp {C F : Type} (source target : State C F) (live : NumSet)
    (fast : Bool) (cmp : Opb) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp (.stringCmp fast cmp)) args source)
      (doAppAux (.memOp (.stringCmp fast cmp)) args target) := by
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
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        case refPtr.refPtr bitA ptrA bitB ptrB =>
          cases foundA : sptLookup ptrA source.refs with
          | none => simp [foundA, ← refs]
          | some entryA =>
            cases entryA <;> simp [foundA, ← refs]
            case byteArray flagA bytesA =>
              cases foundB : sptLookup ptrB source.refs with
              | none => simp
              | some entryB =>
                cases entryB <;> simp
                case byteArray flagB bytesB => exact related

/-- All pure memory auxiliary operations preserve related outcomes. -/
theorem stateRel_doAppAux_pureMemory {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.MemOp) (args : List DataSem.Value) (pure : isPure (.memOp op) = true)
    (related : stateRel source target live) :
    appRel live (doAppAux (.memOp op) args source) (doAppAux (.memOp op) args target) := by
  cases op <;> simp [isPure] at pure
  case el => exact stateRel_doAppAux_memEl source target live args related
  case length => exact stateRel_doAppAux_memoryLength source target live _ args rfl related
  case lengthByte => exact stateRel_doAppAux_memoryLength source target live _ args rfl related
  case derefByte => exact stateRel_doAppAux_derefByte source target live args related
  case concatByteVec => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  case toListByte => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  case lengthByteVec => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  case derefByteVec => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  case stringCmp fast cmp => exact stateRel_doAppAux_stringCmp source target live fast cmp args related
  case boundsCheckArray => exact stateRel_doAppAux_memoryBounds source target live _ args rfl related
  case boundsCheckByte loose => exact stateRel_doAppAux_memoryBounds source target live _ args rfl related

end Flapjack.Compiler.Backend.DataLive
