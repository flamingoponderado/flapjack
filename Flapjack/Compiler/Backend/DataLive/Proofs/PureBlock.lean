import Flapjack.Compiler.Backend.DataLive.Proofs.PureError

/-! Pure block primitives and dead assignment elimination. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Pure block operations do not consume or reset reserved heap space. -/
theorem pure_block_doSpace {C F : Type} (op : ClosLang.BlockOp) (args : List DataSem.Value)
    (state : State C F) (pure : isPure (.blockOp op) = true) : doSpace (.blockOp op) args state = some state := by
  cases op <;> simp [isPure] at pure <;> simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Block operations whose sole argument is inspected without a heap lookup. -/
def isSimpleBlock : ClosLang.BlockOp → Bool
  | .tagEq _ | .lenEq _ | .tagLenEq _ _ | .lengthBlock => true
  | _ => false

/-- Successful simple block operations preserve the state passed to the
auxiliary dispatcher. This is a case of the pure-operation success proof. -/
theorem simple_block_aux_same {C F : Type} (op : ClosLang.BlockOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (simple : isSimpleBlock op = true) (run : doAppAux (.blockOp op) args state = .val (value, next)) :
    next = state := by
  cases op <;> simp [isSimpleBlock] at simple
  all_goals cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        all_goals exact run.2.symm

/-- The simple block operations are among the pass's pure operations. -/
theorem simple_block_isPure (op : ClosLang.BlockOp) (simple : isSimpleBlock op = true) :
    isPure (.blockOp op) = true := by
  cases op <;> simp_all [isSimpleBlock, isPure]

/-- Successful simple block operations change only resource bookkeeping
in the full dispatcher. -/
theorem simple_block_doApp_stateRel {C F : Type} (op : ClosLang.BlockOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (live : NumSet)
    (simple : isSimpleBlock op = true) (run : doApp (.blockOp op) args state = .val (value, next)) :
    stateRel next state live := by
  have space := pure_block_doSpace op args state (simple_block_isPure op simple)
  simp only [doApp, space] at run
  have equal := simple_block_aux_same op args _ next value simple run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- Dead simple block inspections can be removed by the liveness pass. -/
theorem simulationFor_removed_simpleBlock {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (names : List Nat) (live : NumSet) (simple : isSimpleBlock op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp op) names none) live := by
  apply simulationFor_removed_of_frame dest (.blockOp op) names live (simple_block_isPure op simple) dead
  intro args state next value run
  exact simple_block_doApp_stateRel op args state next value live simple run

/-- Block operations that inspect boolean values without updating state. -/
def isBoolBlock : ClosLang.BlockOp → Bool
  | .boolTest _ | .boolNot => true
  | _ => false

/-- Successful boolean block operations preserve the auxiliary state. -/
theorem bool_block_aux_same {C F : Type} (op : ClosLang.BlockOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (boolean : isBoolBlock op = true) (run : doAppAux (.blockOp op) args state = .val (value, next)) :
    next = state := by
  cases op <;> simp [isBoolBlock] at boolean
  case boolNot =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases found : destBool first <;> simp [doAppAux, applyNonFfi, found] at run
        exact run.2.symm
  case boolTest test =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases foundFirst : destBool first <;> simp [doAppAux, applyNonFfi, foundFirst] at run
          cases foundSecond : destBool second <;> simp [foundSecond] at run
          exact run.2.symm

/-- Boolean block operations are pure for the liveness pass. -/
theorem bool_block_isPure (op : ClosLang.BlockOp) (boolean : isBoolBlock op = true) :
    isPure (.blockOp op) = true := by
  cases op <;> simp_all [isBoolBlock, isPure]

/-- Dead boolean block operations can be removed by the liveness pass. -/
theorem simulationFor_removed_boolBlock {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (names : List Nat) (live : NumSet) (boolean : isBoolBlock op = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp op) names none) live := by
  have pure := bool_block_isPure op boolean
  apply simulationFor_removed_of_frame dest (.blockOp op) names live pure dead
  intro args state next value run
  have space := pure_block_doSpace op args state pure
  simp only [doApp, space] at run
  have equal := bool_block_aux_same op args _ next value boolean run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- A block-bounds check preserves the auxiliary state on success. -/
theorem boundsCheckBlock_aux_same {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp .boundsCheckBlock) args state = .val (value, next)) : next = state := by
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
        exact run.2.symm

/-- Dead block-bounds checks can be removed by the liveness pass. -/
theorem simulationFor_removed_boundsCheckBlock {C F : Type} (dest : Nat)
    (names : List Nat) (live : NumSet) (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp .boundsCheckBlock) names none) live := by
  apply simulationFor_removed_of_frame dest (.blockOp .boundsCheckBlock) names live rfl dead
  intro args state next value run
  have space := pure_block_doSpace .boundsCheckBlock args state rfl
  simp only [doApp, space] at run
  have equal := boundsCheckBlock_aux_same args _ next value run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- A constant comparison preserves the auxiliary state on success. -/
theorem equalConst_aux_same {C F : Type} (part : ClosLang.ConstPart) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp (.equalConst part)) args state = .val (value, next)) : next = state := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases part with
      | con tag fields =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
      | int n =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        exact run.2.symm
      | w64 n =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        exact run.2.symm
      | str text =>
        cases first <;> try simp [doAppAux, applyNonFfi] at run
        case refPtr flag ptr =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case byteArray mutable bytes =>
              cases mutable <;> simp_all

/-- Dead constant comparisons can be removed by the liveness pass. -/
theorem simulationFor_removed_equalConst {C F : Type} (dest : Nat) (part : ClosLang.ConstPart)
    (names : List Nat) (live : NumSet) (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.equalConst part)) names none) live := by
  apply simulationFor_removed_of_frame dest (.blockOp (.equalConst part)) names live rfl dead
  intro args state next value run
  have space := pure_block_doSpace (.equalConst part) args state rfl
  simp only [doApp, space] at run
  have equal := equalConst_aux_same part args _ next value run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- A block element read preserves the auxiliary state on success. -/
theorem elemAt_aux_same {C F : Type} (index : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp (.elemAt index)) args state = .val (value, next)) : next = state := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases first <;> simp [doAppAux, applyNonFfi] at run
      case block stamp tag values =>
        cases found : values[index]? with
        | none => simp [found] at run
        | some item =>
          simp [found] at run
          exact run.2.symm
      case refPtr flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [found] at run
        | some entry =>
          cases entry <;> simp [found] at run
          case valueArray values =>
            cases slot : values[index]? with
            | none => simp [slot] at run
            | some item =>
              simp [slot] at run
              exact run.2.symm

/-- Dead block element reads can be removed by the liveness pass. -/
theorem simulationFor_removed_elemAt {C F : Type} (dest index : Nat)
    (names : List Nat) (live : NumSet) (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.elemAt index)) names none) live := by
  apply simulationFor_removed_of_frame dest (.blockOp (.elemAt index)) names live rfl dead
  intro args state next value run
  have space := pure_block_doSpace (.elemAt index) args state rfl
  simp only [doApp, space] at run
  have equal := elemAt_aux_same index args _ next value run
  subst next
  simp [stateRel, doStack, doLimSafe]

/-- The constant primitive has no successful evaluator clause. -/
theorem simulationFor_removed_constant {C F : Type} (dest : Nat) (constant : ClosLang.Const)
    (names : List Nat) (live : NumSet) (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp (.constant constant)) names none) live := by
  apply simulationFor_removed_of_frame dest (.blockOp (.constant constant)) names live rfl dead
  intro args state next value run
  have space := pure_block_doSpace (.constant constant) args state rfl
  simp only [doApp, space] at run
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- All dead pure block assignments satisfy the liveness simulation. This
is an untagged subcase of the HOL assignment theorem pending source review. -/
theorem simulationFor_removed_block {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (names : List Nat) (live : NumSet) (pure : isPure (.blockOp op) = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.blockOp op) names none) live := by
  cases op <;> simp [isPure] at pure
  case elemAt index => exact simulationFor_removed_elemAt dest index names live dead
  case tagLenEq tag length => exact simulationFor_removed_simpleBlock dest _ names live rfl dead
  case lenEq length => exact simulationFor_removed_simpleBlock dest _ names live rfl dead
  case tagEq tag => exact simulationFor_removed_simpleBlock dest _ names live rfl dead
  case lengthBlock => exact simulationFor_removed_simpleBlock dest _ names live rfl dead
  case boolTest test => exact simulationFor_removed_boolBlock dest _ names live rfl dead
  case boolNot => exact simulationFor_removed_boolBlock dest _ names live rfl dead
  case boundsCheckBlock => exact simulationFor_removed_boundsCheckBlock dest names live dead
  case constant constant => exact simulationFor_removed_constant dest constant names live dead
  case equalConst part => exact simulationFor_removed_equalConst dest part names live dead

end Flapjack.Compiler.Backend.DataLive
