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

/-- The unavailable byte-vector primitives are classified as pure. -/
theorem unavailable_mem_isPure (op : ClosLang.MemOp) (unavailable : isUnavailableMemory op = true) :
    isPure (.memOp op) = true := by
  cases op <;> simp_all [isUnavailableMemory, isPure]

/-- Dead assignments using unavailable byte-vector operations satisfy the
liveness simulation because successful application is impossible. -/
theorem simulationFor_removed_unavailableMemory {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (names : List Nat) (live : NumSet) (unavailable : isUnavailableMemory op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) names none) live := by
  have pure := unavailable_mem_isPure op unavailable
  apply simulationFor_removed_of_frame dest (.memOp op) names live pure dead
  intro args state next value run
  have space := pure_mem_doSpace op args state pure
  simp only [doApp, space] at run
  exact False.elim (unavailable_mem_aux op args _ next value unavailable run)

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

/-- Array-length reads are pure. -/
theorem memoryLength_isPure (op : ClosLang.MemOp) (lengthOp : isMemoryLength op = true) :
    isPure (.memOp op) = true := by
  cases op <;> simp_all [isMemoryLength, isPure]

/-- Dead array-length reads satisfy the liveness simulation. -/
theorem simulationFor_removed_memoryLength {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (names : List Nat) (live : NumSet) (lengthOp : isMemoryLength op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) names none) live := by
  have pure := memoryLength_isPure op lengthOp
  apply simulationFor_removed_of_frame dest (.memOp op) names live pure dead
  intro args state next value run
  have space := pure_mem_doSpace op args state pure
  simp only [doApp, space] at run
  have equal := memoryLength_aux_same op args _ next value lengthOp run
  subst next
  simp [stateRel, doStack, doLimSafe]

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

/-- Memory bounds checks are pure. -/
theorem memoryBounds_isPure (op : ClosLang.MemOp) (boundsOp : isMemoryBounds op = true) :
    isPure (.memOp op) = true := by
  cases op <;> simp_all [isMemoryBounds, isPure]

/-- Dead memory bounds checks satisfy the liveness simulation. -/
theorem simulationFor_removed_memoryBounds {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (names : List Nat) (live : NumSet) (boundsOp : isMemoryBounds op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) names none) live := by
  have pure := memoryBounds_isPure op boundsOp
  apply simulationFor_removed_of_frame dest (.memOp op) names live pure dead
  intro args state next value run
  have space := pure_mem_doSpace op args state pure
  simp only [doApp, space] at run
  have equal := memoryBounds_aux_same op args _ next value boundsOp run
  subst next
  simp [stateRel, doStack, doLimSafe]

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

/-- Dead indexed value reads satisfy the liveness simulation. -/
theorem simulationFor_removed_memEl {C F : Type} (dest : Nat) (names : List Nat) (live : NumSet)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp .el) names none) live := by
  apply simulationFor_removed_of_frame dest (.memOp .el) names live rfl dead
  intro args state next value run
  have space := pure_mem_doSpace .el args state rfl
  simp only [doApp, space] at run
  have equal := memEl_aux_same args _ next value run
  subst next
  simp [stateRel, doStack, doLimSafe]

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

/-- Dead indexed byte reads satisfy the liveness simulation. -/
theorem simulationFor_removed_derefByte {C F : Type} (dest : Nat) (names : List Nat) (live : NumSet)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp .derefByte) names none) live := by
  apply simulationFor_removed_of_frame dest (.memOp .derefByte) names live rfl dead
  intro args state next value run
  have space := pure_mem_doSpace .derefByte args state rfl
  simp only [doApp, space] at run
  have equal := derefByte_aux_same args _ next value run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- All dead pure memory assignments satisfy the liveness simulation. This
case is untagged pending the source evaluator and carrier review. -/
theorem simulationFor_removed_memory {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (names : List Nat) (live : NumSet) (pure : isPure (.memOp op) = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) names none) live := by
  cases op <;> simp [isPure] at pure
  case el => exact simulationFor_removed_memEl dest names live dead
  case length => exact simulationFor_removed_memoryLength dest _ names live rfl dead
  case lengthByte => exact simulationFor_removed_memoryLength dest _ names live rfl dead
  case derefByte => exact simulationFor_removed_derefByte dest names live dead
  case concatByteVec => exact simulationFor_removed_unavailableMemory dest _ names live rfl dead
  case toListByte => exact simulationFor_removed_unavailableMemory dest _ names live rfl dead
  case lengthByteVec => exact simulationFor_removed_unavailableMemory dest _ names live rfl dead
  case derefByteVec => exact simulationFor_removed_unavailableMemory dest _ names live rfl dead
  case stringCmp fast cmp => exact simulationFor_removed_requiresNames dest _ names live rfl
  case boundsCheckArray => exact simulationFor_removed_memoryBounds dest _ names live rfl dead
  case boundsCheckByte loose => exact simulationFor_removed_memoryBounds dest _ names live rfl dead

/-- Every dead pure unannotated assignment satisfies the liveness
simulation. The retained and annotated assignment cases remain open; this
result is untagged pending source evaluator and carrier review. -/
theorem simulationFor_removed_pure {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : NumSet) (pure : isPure op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest op names none) live := by
  cases op with
  | label label => exact simulationFor_removed_label dest label names live dead
  | ffi name => simp [isPure] at pure
  | intOp op => exact simulationFor_removed_int dest op names live pure dead
  | wordOp op => exact simulationFor_removed_word dest op names live pure dead
  | blockOp op => exact simulationFor_removed_block dest op names live pure dead
  | globOp op => exact simulationFor_removed_global dest op names live pure dead
  | memOp op => exact simulationFor_removed_memory dest op names live pure dead
  | install => simp [isPure] at pure
  | thunkOp op => simp [isPure] at pure

end Flapjack.Compiler.Backend.DataLive
