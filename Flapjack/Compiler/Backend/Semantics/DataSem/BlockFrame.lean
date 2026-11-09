import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

/-! Local and control frames for block primitive application. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Lift an auxiliary block frame through the dispatcher's space and stack
bookkeeping. This is Flapjack infrastructure for pass simulations. -/
theorem doApp_block_frame_of_aux {C F : Type} (op : ClosLang.BlockOp)
    (auxFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doAppAux (.blockOp op) args before = .val (value, after) → SameLocalControl before after)
    (args : List Value) (state next : State C F) (value : Value)
    (run : doApp (.blockOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.blockOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := doSpace_frame (.blockOp op) args state accounted space
    have second := auxFrame args _ next value run
    have second' : SameLocalControl accounted next := by
      simpa [SameLocalControl, doStack, doLimSafe] using second
    exact first.trans second'

/-- A successful block tag comparison preserves locals and control fields. -/
theorem doAppAux_tagEq_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.tagEq tag)) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons arg rest =>
    cases rest with
    | cons other tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases arg <;> simp [doAppAux, applyNonFfi] at run
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful block tag comparison preserves locals and control fields
through the full dispatcher. -/
theorem doApp_tagEq_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.blockOp (.tagEq tag)) args state = .val (value, next)) :
    SameLocalControl state next :=
  doApp_block_frame_of_aux (.tagEq tag) (doAppAux_tagEq_frame tag) args state next value run

/-- Extending a block only changes allocation accounting. -/
theorem doAppAux_consExtend_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.consExtend tag)) args state = .val (value, next)) :
    SameLocalControl state next := by
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
                    all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Converting a list into a block only changes allocation accounting. -/
theorem doAppAux_fromList_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.fromList tag)) args state = .val (value, next)) :
    SameLocalControl state next := by
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
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              | cons head tail =>
                cases stamps : state.tstamps <;>
                  simp [found, same, withFreshTimestamp, checkLim, stamps] at run
                all_goals obtain ⟨rfl, rfl⟩ := run
                all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            · simp [found, same] at run

/-- Constructing a block changes timestamp and limit accounting only. -/
theorem doAppAux_cons_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.cons tag)) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases args with
  | nil =>
    simp [doAppAux, applyNonFfi] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons first rest =>
    cases stamps : state.tstamps <;> simp [doAppAux, applyNonFfi, withFreshTimestamp, checkLim, stamps] at run
    all_goals obtain ⟨rfl, rfl⟩ := run
    all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Appending lists changes timestamp and limit accounting only. -/
theorem doAppAux_listAppend_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .listAppend) args state = .val (value, next)) :
    SameLocalControl state next := by
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
            all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Building a constant may update references and timestamps, but preserves
the local and control fields used by the pass simulation. -/
theorem doAppAux_build_frame {C F : Type} (parts : List ClosLang.ConstPart) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.build parts)) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases args with
  | cons first rest => simp [doAppAux, applyNonFfi] at run
  | nil =>
    generalize result : doBuildConst parts state.refs state.tstamps = triple
    obtain ⟨built, refs, stamps⟩ := triple
    simp [doAppAux, applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constant operations have no successful auxiliary clause. -/
theorem doAppAux_constant_frame {C F : Type} (constant : ClosLang.Const) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.constant constant)) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases args <;> simp [doAppAux, applyNonFfi] at run

/-- Reading a block element preserves locals and control, whether the block
is represented directly or stored in a reference. -/
theorem doAppAux_elemAt_frame {C F : Type} (index : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.elemAt index)) args state = .val (value, next)) :
    SameLocalControl state next := by
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
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
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
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful constant comparison preserves locals and control fields. -/
theorem doAppAux_equalConst_frame {C F : Type} (part : ClosLang.ConstPart) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.equalConst part)) args state = .val (value, next)) :
    SameLocalControl state next := by
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
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful block equality operation preserves locals and control. -/
theorem doAppAux_equal_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .equal) args state = .val (value, next)) :
    SameLocalControl state next := by
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
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Boolean block operations preserve locals and control fields. -/
theorem doAppAux_boolNot_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .boolNot) args state = .val (value, next)) :
    SameLocalControl state next := by
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
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A Boolean block test preserves locals and control fields. -/
theorem doAppAux_boolTest_frame {C F : Type} (test : AstHOL.Test) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.boolTest test)) args state = .val (value, next)) :
    SameLocalControl state next := by
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
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A block bounds check preserves locals and control fields. -/
theorem doAppAux_boundsCheckBlock_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp .boundsCheckBlock) args state = .val (value, next)) :
    SameLocalControl state next := by
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
        all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful auxiliary block operation preserves locals and control fields. -/
theorem doAppAux_block_frame {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp op) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases op with
  | boundsCheckBlock => exact doAppAux_boundsCheckBlock_frame args state next value run
  | boolNot => exact doAppAux_boolNot_frame args state next value run
  | boolTest test => exact doAppAux_boolTest_frame test args state next value run
  | equal => exact doAppAux_equal_frame args state next value run
  | equalConst part => exact doAppAux_equalConst_frame part args state next value run
  | elemAt index => exact doAppAux_elemAt_frame index args state next value run
  | build parts => exact doAppAux_build_frame parts args state next value run
  | constant constant => exact doAppAux_constant_frame constant args state next value run
  | cons tag => exact doAppAux_cons_frame tag args state next value run
  | listAppend => exact doAppAux_listAppend_frame args state next value run
  | fromList tag => exact doAppAux_fromList_frame tag args state next value run
  | consExtend tag => exact doAppAux_consExtend_frame tag args state next value run
  | tagEq _ | lenEq _ | tagLenEq _ _ | lengthBlock =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons arg rest =>
      cases rest with
      | cons other tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases arg <;> simp [doAppAux, applyNonFfi] at run
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful block operation preserves locals and control fields through the
full primitive dispatcher. -/
theorem doApp_block_frame {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.blockOp op) args state = .val (value, next)) :
    SameLocalControl state next :=
  doApp_block_frame_of_aux op (doAppAux_block_frame op) args state next value run

end Flapjack.Compiler.Backend.DataSem
