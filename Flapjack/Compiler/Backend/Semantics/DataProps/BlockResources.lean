import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveResources

/-! Resource properties of source block operations. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Auxiliary block cases establish resource monotonicity by inspecting their actual clauses. -/
theorem doAppAux_tagEq_resource_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.tagEq tag)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons arg rest =>
    cases rest with
    | cons other tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases arg <;> simp [doAppAux, applyNonFfi] at run
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_consExtend_resource_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.consExtend tag)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third rest =>
        cases rest with
        | nil => simp [doAppAux, applyNonFfi] at run
        | cons fourth rest =>
          cases first <;> simp [doAppAux, applyNonFfi] at run
          case block timestamp oldTag previous =>
            cases second <;> try simp at run
            case number lower =>
              cases third <;> try simp at run
              case number length =>
                cases fourth <;> try simp at run
                case number total =>
                  by_cases bad : lower < 0 ∨ length < 0 ∨ (previous.length : Int) < lower + length ∨
                      total = 0 ∨ ¬total = (rest.length : Int) + length
                  · simp [bad] at run
                  · cases stamps : state.tstamps <;> simp [bad, withFreshTimestamp, checkLim, stamps] at run
                    all_goals obtain ⟨rfl, rfl⟩ := run
                    all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_fromList_resource_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.fromList tag)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        case number length =>
          cases found : valueToList second with
          | none => simp [found] at run
          | some values =>
            by_cases same : length = (values.length : Int)
            · cases values with
              | nil =>
                simp [found, same] at run
                obtain ⟨rfl, rfl⟩ := run
                simp [BackendProps.optionLe_refl]
              | cons head tail =>
                cases stamps : state.tstamps <;>
                  simp [found, same, withFreshTimestamp, checkLim, stamps] at run
                all_goals obtain ⟨rfl, rfl⟩ := run
                all_goals simp [BackendProps.optionLe_refl]
            · simp [found, same] at run


theorem doAppAux_cons_resource_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.cons tag)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil =>
    simp [doAppAux, applyNonFfi] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [BackendProps.optionLe_refl]
  | cons first rest =>
    cases stamps : state.tstamps <;> simp [doAppAux, applyNonFfi, withFreshTimestamp, checkLim, stamps] at run
    all_goals obtain ⟨rfl, rfl⟩ := run
    all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_listAppend_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .listAppend) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases xs : valueToList first with
        | none => simp [doAppAux, applyNonFfi, xs] at run
        | some values =>
          cases ys : valueToList second with
          | none => simp [doAppAux, applyNonFfi, xs, ys] at run
          | some others =>
            cases stamps : state.tstamps <;>
              simp [doAppAux, applyNonFfi, xs, ys, withFreshTimestamp, checkLim, stamps] at run
            all_goals obtain ⟨rfl, rfl⟩ := run
            all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_build_resource_frame {C F : Type} (parts : List ClosLang.ConstPart) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.build parts)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | cons first rest => simp [doAppAux, applyNonFfi] at run
  | nil =>
    generalize result : doBuildConst parts state.refs state.tstamps = triple
    obtain ⟨built, refs, stamps⟩ := triple
    simp [doAppAux, applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [BackendProps.optionLe_refl]


theorem doAppAux_constant_resource_frame {C F : Type} (constant : ClosLang.Const) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.constant constant)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args <;> simp [doAppAux, applyNonFfi] at run


theorem doAppAux_elemAt_resource_frame {C F : Type} (index : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.elemAt index)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
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
          obtain ⟨rfl, rfl⟩ := run
          simp [BackendProps.optionLe_refl]
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
              obtain ⟨rfl, rfl⟩ := run
              simp [BackendProps.optionLe_refl]


theorem doAppAux_equalConst_resource_frame {C F : Type} (part : ClosLang.ConstPart) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.equalConst part)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases part <;> cases first <;> simp [doAppAux, applyNonFfi] at run
      case str.refPtr text flag ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [found] at run
        | some entry =>
          cases entry <;> simp [found] at run
          case byteArray writable bytes =>
            cases writable <;> simp at run
            obtain ⟨rfl, rfl⟩ := run
            simp [BackendProps.optionLe_refl]
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_equal_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .equal) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases result : doEq state.refs first second with
        | typeError => simp [doAppAux, applyNonFfi, result] at run
        | val bit =>
          simp [doAppAux, applyNonFfi, result] at run
          obtain ⟨rfl, rfl⟩ := run
          simp [BackendProps.optionLe_refl]


theorem doAppAux_boolNot_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .boolNot) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons arg rest =>
    cases rest with
    | cons other tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases result : destBool arg with
      | none => simp [doAppAux, applyNonFfi, result] at run
      | some bit =>
        simp [doAppAux, applyNonFfi, result] at run
        obtain ⟨rfl, rfl⟩ := run
        simp [BackendProps.optionLe_refl]


theorem doAppAux_boolTest_resource_frame {C F : Type} (test : AstHOL.Test) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.boolTest test)) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases x : destBool first with
        | none => simp [doAppAux, applyNonFfi, x] at run
        | some left =>
          cases y : destBool second with
          | none => simp [doAppAux, applyNonFfi, x, y] at run
          | some right =>
            simp [doAppAux, applyNonFfi, x, y] at run
            obtain ⟨rfl, rfl⟩ := run
            simp [BackendProps.optionLe_refl]


theorem doAppAux_boundsCheckBlock_resource_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .boundsCheckBlock) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
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
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals simp [BackendProps.optionLe_refl]


theorem doAppAux_block_resource_frame {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases op with
  | boundsCheckBlock => exact doAppAux_boundsCheckBlock_resource_frame args state next value run
  | boolNot => exact doAppAux_boolNot_resource_frame args state next value run
  | boolTest test => exact doAppAux_boolTest_resource_frame test args state next value run
  | equal => exact doAppAux_equal_resource_frame args state next value run
  | equalConst part => exact doAppAux_equalConst_resource_frame part args state next value run
  | elemAt index => exact doAppAux_elemAt_resource_frame index args state next value run
  | build parts => exact doAppAux_build_resource_frame parts args state next value run
  | constant constant => exact doAppAux_constant_resource_frame constant args state next value run
  | cons tag => exact doAppAux_cons_resource_frame tag args state next value run
  | listAppend => exact doAppAux_listAppend_resource_frame args state next value run
  | fromList tag => exact doAppAux_fromList_resource_frame tag args state next value run
  | consExtend tag => exact doAppAux_consExtend_resource_frame tag args state next value run
  | tagEq _ | lenEq _ | tagLenEq _ _ | lengthBlock =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons arg rest =>
      cases rest with
      | cons other tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases arg <;> simp [doAppAux, applyNonFfi] at run
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals simp [BackendProps.optionLe_refl]



/-- Block operations satisfy the resource properties through the production dispatcher. -/
theorem doApp_block_resource_frame {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.blockOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.blockOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact accounted_resource_frame _ args state accounted next value space run
      (fun before after v h => doAppAux_block_resource_frame op args before after v h)

end Flapjack.Compiler.Backend.DataSem
