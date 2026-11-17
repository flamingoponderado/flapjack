module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PureError

@[expose] public section

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

end Flapjack.Compiler.Backend.DataLive
