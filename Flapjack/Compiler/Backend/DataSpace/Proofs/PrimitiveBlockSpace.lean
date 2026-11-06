import Flapjack.Compiler.Backend.DataSpace.Proofs.PrimitiveMemorySpace

/-! Independence of block primitive results from reserved space. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Block allocation does not inspect reserved space. -/
theorem doAppAux_cons_with_space {C F : Type} (tag : Nat) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.blockOp (.cons tag)) values { state with space := space } =
      replaceResultSpace space (doAppAux (.blockOp (.cons tag)) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases found : state.tstamps <;>
      simp [doAppAux, applyNonFfi, replaceResultSpace, withFreshTimestamp, checkLim, found]

/-- Building a constant does not inspect reserved space. -/
theorem doAppAux_build_with_space {C F : Type} (parts : List ClosLang.ConstPart)
    (values : List DataSem.Value) (state : State C F) (space : Nat) :
    doAppAux (.blockOp (.build parts)) values { state with space := space } =
      replaceResultSpace space (doAppAux (.blockOp (.build parts)) values state) := by
  cases values with
  | cons first rest => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | nil =>
    cases built : doBuildConst parts state.refs state.tstamps with
    | mk value remaining =>
      obtain ⟨refs, stamps⟩ := remaining
      simp [doAppAux, applyNonFfi, replaceResultSpace, built]

/-- Reading a block element does not inspect reserved space. -/
theorem doAppAux_elemAt_with_space {C F : Type} (index : Nat) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.blockOp (.elemAt index)) values { state with space := space } =
      replaceResultSpace space (doAppAux (.blockOp (.elemAt index)) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | nil =>
      cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
      case block timestamp tag values => cases found : values[index]? <;> simp
      case refPtr flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp
        | some entry =>
          cases entry <;> simp
          case valueArray values => cases slot : values[index]? <;> simp

/-- Constant comparisons do not inspect reserved space. -/
theorem doAppAux_equalConst_with_space {C F : Type} (part : ClosLang.ConstPart)
    (values : List DataSem.Value) (state : State C F) (space : Nat) :
    doAppAux (.blockOp (.equalConst part)) values { state with space := space } =
      replaceResultSpace space (doAppAux (.blockOp (.equalConst part)) values state) := by
  cases values with
  | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | nil =>
      cases part <;> cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
      case str.refPtr text flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp
        | some entry =>
          cases entry <;> simp
          case byteArray mutable bytes => cases mutable <;> simp

/-- Every block operation permitted in an unannotated assignment has an
auxiliary result independent of reserved space. -/
theorem doAppAux_block_noNames_with_space {C F : Type} (op : ClosLang.BlockOp)
    (values : List DataSem.Value) (state : State C F) (space : Nat)
    (valid : DataLang.opRequiresNames (.blockOp op) = false) :
    doAppAux (.blockOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.blockOp op) values state) := by
  cases op <;> simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
  case cons tag => exact doAppAux_cons_with_space tag values state space
  case elemAt index => exact doAppAux_elemAt_with_space index values state space
  case build parts => exact doAppAux_build_with_space parts values state space
  case equalConst part => exact doAppAux_equalConst_with_space part values state space
  case constant constant => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  case boolNot =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil => cases found : destBool first <;> simp [doAppAux, applyNonFfi, replaceResultSpace, found]
  case boolTest test =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
        | nil =>
          cases foundFirst : destBool first <;> simp [doAppAux, applyNonFfi, replaceResultSpace, foundFirst]
          cases foundSecond : destBool second <;> simp
  case boundsCheckBlock =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
        | nil => cases first <;> cases second <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  all_goals
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil => cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]

/-- Every primitive permitted in an unannotated assignment has an auxiliary
result independent of reserved space. This is a Flapjack simulation lemma. -/
theorem doAppAux_noNames_with_space {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (space : Nat)
    (valid : DataLang.opRequiresNames op = false) :
    doAppAux op values { state with space := space } =
      replaceResultSpace space (doAppAux op values state) := by
  cases op with
  | label label => exact doAppAux_label_with_space label values state space
  | ffi name => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
  | intOp op => exact doAppAux_int_with_space op values state space
  | wordOp op => exact doAppAux_word_with_space op values state space
  | blockOp op => exact doAppAux_block_noNames_with_space op values state space valid
  | globOp op => exact doAppAux_global_with_space op values state space
  | memOp op => exact doAppAux_memory_noNames_with_space op values state space valid
  | install => simp [DataLang.opRequiresNames] at valid
  | thunkOp op => exact doAppAux_thunk_with_space op values state space

/-- After paying for an unannotated primitive, extra reserved space remains
available without changing its result or other state fields. -/
theorem doApp_reserved_extra_space {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (extra : Nat)
    (valid : DataLang.opRequiresNames op = false) :
    doApp op values { state with space := opSpaceReq op values.length + extra } =
      replaceResultSpace extra
        (doApp op values { state with space := opSpaceReq op values.length }) := by
  rw [doApp_reserved_unannotated op values state extra valid]
  have base := doApp_reserved_unannotated op values state 0 valid
  simp only [Nat.add_zero] at base
  rw [base]
  have stackEq : doStack op values (doLimSafe { state with space := extra } op values) =
      { doStack op values (doLimSafe { state with space := 0 } op values) with space := extra } := by
    rfl
  rw [stackEq]
  exact doAppAux_noNames_with_space op values
    (doStack op values (doLimSafe { state with space := 0 } op values)) extra valid

end Flapjack.Compiler.Backend.DataSpace
