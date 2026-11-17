module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PureGlobal

@[expose] public section

/-! Pure memory operations and dead assignment elimination. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Pure memory operations do not consume or reset reserved heap space. -/
theorem pure_mem_doSpace {C F : Type} (op : ClosLang.MemOp) (args : List DataSem.Value)
    (state : State C F) (pure : isPure (.memOp op) = true) : doSpace (.memOp op) args state = some state := by
  cases op <;> simp [isPure] at pure <;> simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Memory primitives whose auxiliary dispatcher has no successful clause. -/
def isUnavailableMemory : ClosLang.MemOp → Bool
  | .concatByteVec | .toListByte | .lengthByteVec | .derefByteVec => true
  | _ => false

/-- The unavailable byte-vector primitives cannot return successfully. -/
theorem unavailable_mem_aux {C F : Type} (op : ClosLang.MemOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (unavailable : isUnavailableMemory op = true)
    (run : doAppAux (.memOp op) args state = .val (value, next)) : False := by
  cases op <;> simp [isUnavailableMemory] at unavailable <;>
    cases args <;> simp [doAppAux, applyNonFfi] at run

/-- If an operation requires a live-name annotation, its unannotated
assignment is always a type error. -/
theorem simulationFor_removed_requiresNames {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : NumSet) (requires : DataLang.opRequiresNames op = true) :
    simulationFor (C := C) (F := F) (.assign dest op names none) live := by
  intro source target result sourceNext run related notType exception
  simp [DataSem.evaluate, requires] at run
  obtain ⟨rfl, rfl⟩ := run
  exact False.elim (notType rfl)

/-- The two pure array-length primitives. -/
def isMemoryLength : ClosLang.MemOp → Bool
  | .length | .lengthByte => true
  | _ => false

/-- A successful array-length read preserves the auxiliary state. -/
theorem memoryLength_aux_same {C F : Type} (op : ClosLang.MemOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (lengthOp : isMemoryLength op = true)
    (run : doAppAux (.memOp op) args state = .val (value, next)) : next = state := by
  cases op <;> simp [isMemoryLength] at lengthOp
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        case refPtr flag ptr =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            all_goals exact run.2.symm

/-- The pure memory bounds-check primitives. -/
def isMemoryBounds : ClosLang.MemOp → Bool
  | .boundsCheckArray | .boundsCheckByte _ => true
  | _ => false

/-- A successful memory bounds check preserves the auxiliary state. -/
theorem memoryBounds_aux_same {C F : Type} (op : ClosLang.MemOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (boundsOp : isMemoryBounds op = true)
    (run : doAppAux (.memOp op) args state = .val (value, next)) : next = state := by
  cases op <;> simp [isMemoryBounds] at boundsOp
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              all_goals exact run.2.symm

/-- Indexed value reads preserve the auxiliary state on success. -/
theorem memEl_aux_same {C F : Type} (args : List DataSem.Value) (state next : State C F)
    (value : DataSem.Value) (run : doAppAux (.memOp .el) args state = .val (value, next)) : next = state := by
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
        case block.number timestamp tag values index =>
          by_cases negative : index < 0
          · simp [negative] at run
          · cases slot : values[index.toNat]? with
            | none => simp [negative, slot] at run
            | some item => simp [negative, slot] at run; exact run.2.symm
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case valueArray values =>
              by_cases negative : index < 0
              · simp [negative] at run
              · cases slot : values[index.toNat]? with
                | none => simp [negative, slot] at run
                | some item => simp [negative, slot] at run; exact run.2.symm

/-- Indexed byte reads preserve the auxiliary state on success. -/
theorem derefByte_aux_same {C F : Type} (args : List DataSem.Value) (state next : State C F)
    (value : DataSem.Value) (run : doAppAux (.memOp .derefByte) args state = .val (value, next)) : next = state := by
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
        case refPtr.number flag ptr index =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case byteArray mutability bytes =>
              by_cases negative : index < 0
              · simp [negative] at run
              · cases slot : bytes[index.toNat]? with
                | none => simp [negative, slot] at run
                | some byte => simp [negative, slot] at run; exact run.2.symm

end Flapjack.Compiler.Backend.DataLive
