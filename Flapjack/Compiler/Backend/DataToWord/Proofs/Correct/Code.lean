import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateCode
import Flapjack.Compiler.Backend.DataToWord.Proofs.Space
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Fragment

/-! Code-table preservation for data primitives used by the simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Integer primitive application cannot replace the source code table. -/
theorem doAppAux_int_code {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doAppAux (.intOp op) args state = .val (value, next)) : next.code = state.code := by
  cases result : DataSem.doIntApp op args with
  | none => simp [DataSem.doAppAux, DataSem.applyNonFfi, result] at run
  | some result =>
    simp [DataSem.doAppAux, DataSem.applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- Word primitive application cannot replace the source code table. -/
theorem doAppAux_word_code {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doAppAux (.wordOp op) args state = .val (value, next)) : next.code = state.code := by
  cases result : DataSem.doWordApp op args with
  | none => simp [DataSem.doAppAux, DataSem.applyNonFfi, result] at run
  | some result =>
    simp [DataSem.doAppAux, DataSem.applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- Resolving a label does not change the code table. -/
theorem doAppAux_label_code {C F : Type} (label : Nat) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doAppAux (.label label) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | cons a rest => simp [DataSem.doAppAux, DataSem.applyNonFfi] at run
  | nil =>
    cases found : sptLookup label state.code with
    | none => simp [DataSem.doAppAux, DataSem.applyNonFfi, found] at run
    | some entry =>
      simp [DataSem.doAppAux, DataSem.applyNonFfi, found] at run
      obtain ⟨rfl, rfl⟩ := run
      rfl

private theorem intAccounting_code {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value)
    (state accounted next : DataSem.State C F) (value : DataSem.Value)
    (space : DataSem.doSpace (.intOp op) args state = some accounted)
    (aux : DataSem.doAppAux (.intOp op) args
      (DataSem.doStack (.intOp op) args (DataSem.doLimSafe accounted (.intOp op) args)) = .val (value, next)) :
    next.code = state.code := by
  have first := (doSpace_code_const (.intOp op) args state accounted space).1
  have second := doAppAux_int_code op args _ next value aux
  simpa [DataSem.doStack, DataSem.doLimSafe, first] using second

/-- The complete integer dispatcher preserves code through space accounting. -/
theorem doApp_int_code {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doApp (.intOp op) args state = .val (value, next)) : next.code = state.code := by
  cases op <;> simp only [DataSem.doApp] at run
  all_goals try simp at run
  all_goals split at run
  all_goals try simp at run
  all_goals rename_i accounted space
  all_goals exact intAccounting_code _ args state accounted next value space run

/-- The complete word dispatcher preserves code through space accounting. -/
theorem doApp_word_code {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doApp (.wordOp op) args state = .val (value, next)) : next.code = state.code := by
  simp only [DataSem.doApp] at run
  cases space : DataSem.doSpace (.wordOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.wordOp op) args state accounted space).1
    have second := doAppAux_word_code op args _ next value run
    simpa [DataSem.doStack, DataSem.doLimSafe, first] using second

/-- The complete label dispatcher preserves code through space accounting. -/
theorem doApp_label_code {C F : Type} (label : Nat) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doApp (.label label) args state = .val (value, next)) : next.code = state.code := by
  simp only [DataSem.doApp] at run
  cases space : DataSem.doSpace (.label label) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.label label) args state accounted space).1
    have second := doAppAux_label_code label args _ next value run
    simpa [DataSem.doStack, DataSem.doLimSafe, first] using second

/-- Integer assignments preserve code on both successful and failed paths. -/
theorem evaluate_assign_int_code {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (names : List Nat) (live : Option NumSet) (state : DataSem.State C F) :
    (DataSem.evaluate (.assign dest (.intOp op) names live) state).2.code = state.code := by
  apply DataSem.evaluate_assign_code_step
  intro values before after value code run
  exact (doApp_int_code op values before after value run).trans code

/-- Word assignments preserve code on both successful and failed paths. -/
theorem evaluate_assign_word_code {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (names : List Nat) (live : Option NumSet) (state : DataSem.State C F) :
    (DataSem.evaluate (.assign dest (.wordOp op) names live) state).2.code = state.code := by
  apply DataSem.evaluate_assign_code_step
  intro values before after value code run
  exact (doApp_word_code op values before after value run).trans code

/-- Label assignments preserve code on both successful and failed paths. -/
theorem evaluate_assign_label_code {C F : Type} (dest label : Nat)
    (names : List Nat) (live : Option NumSet) (state : DataSem.State C F) :
    (DataSem.evaluate (.assign dest (.label label) names live) state).2.code = state.code := by
  apply DataSem.evaluate_assign_code_step
  intro values before after value code run
  exact (doApp_label_code label values before after value run).trans code

open DataSem

/-- Lift a code-preserving auxiliary block operation through accounting. -/
theorem doApp_block_code_of_aux {C F : Type} (op : ClosLang.BlockOp)
    (auxCode : ∀ (args : List DataSem.Value) (before after : State C F) (value : DataSem.Value),
      doAppAux (.blockOp op) args before = .val (value, after) → after.code = before.code)
    (args : List DataSem.Value) (state next : State C F) (value : DataSem.Value)
    (run : doApp (.blockOp op) args state = .val (value, next)) : next.code = state.code := by
  simp only [doApp] at run
  cases space : doSpace (.blockOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.blockOp op) args state accounted space).1
    have second := auxCode args _ next value run
    simpa [doStack, doLimSafe, first] using second

/-- The comparison block operations do not alter code. -/
theorem doAppAux_blockCompare_code {C F : Type} (op : ClosLang.BlockOp)
    (compare : (∃ tag, op = .tagEq tag) ∨ (∃ len, op = .lenEq len) ∨
      (∃ tag len, op = .tagLenEq tag len) ∨ op = .lengthBlock)
    (args : List DataSem.Value) (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp op) args state = .val (value, next)) : next.code = state.code := by
  rcases compare with ⟨tag, rfl⟩ | ⟨len, rfl⟩ | ⟨tag, len, rfl⟩ | rfl <;>
    cases args with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons arg rest =>
      cases rest with
      | cons other tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases arg <;> simp [doAppAux, applyNonFfi] at run
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals rfl

theorem doAppAux_cons_code {C F : Type} (tag : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp (.cons tag)) args state = .val (value, next)) :
    next.code = state.code := by
  cases args with
  | nil =>
    simp [doAppAux, applyNonFfi] at run
    obtain ⟨rfl, rfl⟩ := run
    exact rfl
  | cons first rest =>
    cases stamps : state.tstamps <;> simp [doAppAux, applyNonFfi, withFreshTimestamp, checkLim, stamps] at run
    all_goals obtain ⟨rfl, rfl⟩ := run
    all_goals exact rfl

theorem doAppAux_blockBounds_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp .boundsCheckBlock) args state = .val (value, next)) : next.code = state.code := by
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
        all_goals rfl

theorem doAppAux_byteBounds_code {C F : Type} (loose : Bool) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp (.boundsCheckByte loose)) args state = .val (value, next)) : next.code = state.code := by
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
              obtain ⟨rfl, rfl⟩ := run
              rfl

theorem evaluate_assign_byteBounds_code {C F : Type} (dest : Nat) (loose : Bool)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp (.boundsCheckByte loose)) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp (.boundsCheckByte loose)) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp (.boundsCheckByte loose)) args before accounted space).1
    have second := doAppAux_byteBounds_code loose args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_arrayBounds_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .boundsCheckArray) args state = .val (value, next)) : next.code = state.code := by
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
            case valueArray values =>
              obtain ⟨rfl, rfl⟩ := run
              rfl

theorem evaluate_assign_arrayBounds_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .boundsCheckArray) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .boundsCheckArray) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .boundsCheckArray) args before accounted space).1
    have second := doAppAux_arrayBounds_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_arrayLength_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .length) args state = .val (value, next)) : next.code = state.code := by
  cases args with
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
          case valueArray values =>
            obtain ⟨rfl, rfl⟩ := run
            rfl

theorem evaluate_assign_arrayLength_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .length) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .length) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .length) args before accounted space).1
    have second := doAppAux_arrayLength_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_byteLength_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .lengthByte) args state = .val (value, next)) : next.code = state.code := by
  cases args with
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
          case byteArray flag bytes =>
            obtain ⟨rfl, rfl⟩ := run
            rfl

theorem evaluate_assign_byteLength_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .lengthByte) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .lengthByte) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .lengthByte) args before accounted space).1
    have second := doAppAux_byteLength_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_dynamicElement_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .el) args state = .val (value, next)) : next.code = state.code := by
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
        case block.number stamp tag values i =>
          by_cases negative : i < 0
          · simp [negative] at run
          · cases slot : values[i.toNat]? with
            | none => simp [negative, slot] at run
            | some item =>
              simp [negative, slot] at run
              obtain ⟨rfl, rfl⟩ := run
              rfl
        case refPtr.number flag ptr i =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case valueArray values =>
              by_cases negative : i < 0
              · simp [negative] at run
              · cases slot : values[i.toNat]? with
                | none => simp [negative, slot] at run
                | some item =>
                  simp [negative, slot] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl

theorem evaluate_assign_dynamicElement_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .el) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .el) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .el) args before accounted space).1
    have second := doAppAux_dynamicElement_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_byteElement_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .derefByte) args state = .val (value, next)) : next.code = state.code := by
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
        case refPtr.number flag ptr i =>
          cases found : sptLookup ptr state.refs with
          | none => simp [found] at run
          | some entry =>
            cases entry <;> simp [found] at run
            case byteArray flag bytes =>
              by_cases negative : i < 0
              · simp [negative] at run
              · cases slot : bytes[i.toNat]? with
                | none => simp [negative, slot] at run
                | some item =>
                  simp [negative, slot] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl

theorem evaluate_assign_byteElement_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .derefByte) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .derefByte) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .derefByte) args before accounted space).1
    have second := doAppAux_byteElement_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second


theorem doAppAux_updateByte_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .updateByte) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> cases third <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number.number flag ptr index byte =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              case byteArray mutability bytes =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ bytes.length
                · simp [invalid] at run
                · cases converted : ClosSem.intToByte byte with
                  | none => simp [invalid, converted] at run
                  | some b =>
                    simp [invalid, converted] at run
                    obtain ⟨rfl, rfl⟩ := run
                    rfl


theorem evaluate_assign_byteStore_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .updateByte) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .updateByte) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .updateByte) args before accounted space).1
    have second := doAppAux_updateByte_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_updateArray_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.memOp .update) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi] at run
      | cons third tail =>
        cases tail with
        | cons fourth tail => simp [doAppAux, applyNonFfi] at run
        | nil =>
          cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
          case refPtr.number flag ptr index =>
            cases found : sptLookup ptr state.refs with
            | none => simp [found] at run
            | some entry =>
              cases entry <;> simp [found] at run
              case valueArray values =>
                by_cases invalid : index < 0 ∨ index.toNat ≥ values.length
                · simp [invalid] at run
                · simp [invalid] at run
                  obtain ⟨rfl, rfl⟩ := run
                  rfl

theorem evaluate_assign_arrayStore_code {C F : Type} (dest : Nat)
    (names : List Nat) (state : State C F) :
    (evaluate (.assign dest (.memOp .update) names none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.memOp .update) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.memOp .update) args before accounted space).1
    have second := doAppAux_updateArray_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

theorem doAppAux_boolNot_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp .boolNot) args state = .val (value, next)) :
    next.code = state.code := by
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
        exact rfl


theorem doAppAux_boolTest_code {C F : Type} (test : AstHOL.Test) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp (.boolTest test)) args state = .val (value, next)) :
    next.code = state.code := by
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
            exact rfl

theorem doAppAux_elemAt_code {C F : Type} (index : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.blockOp (.elemAt index)) args state = .val (value, next)) :
    next.code = state.code := by
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
          exact rfl
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
              exact rfl

/-- A code-preserving block auxiliary gives a code-preserving assignment. -/
theorem evaluate_assign_block_code_of_aux {C F : Type} (dest : Nat) (op : ClosLang.BlockOp)
    (names : List Nat) (live : Option NumSet) (state : State C F)
    (auxCode : ∀ (args : List DataSem.Value) (before after : State C F) (value : DataSem.Value),
      doAppAux (.blockOp op) args before = .val (value, after) → after.code = before.code) :
    (evaluate (.assign dest (.blockOp op) names live) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro values before after value code run
  exact (doApp_block_code_of_aux op auxCode values before after value run).trans code

/-- Loading the globals pointer preserves code. -/
theorem doAppAux_globalsPtr_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.globOp .globalsPtr) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | cons a rest => simp [doAppAux, applyNonFfi] at run
  | nil =>
    cases global : state.global with
    | none => simp [doAppAux, applyNonFfi, global] at run
    | some ptr =>
      simp [doAppAux, applyNonFfi, global] at run
      obtain ⟨rfl, rfl⟩ := run
      rfl

/-- The globals pointer assignment preserves code through its accounting. -/
theorem evaluate_assign_globalsPtr_code {C F : Type} (dest : Nat) (state : State C F) :
    (evaluate (.assign dest (.globOp .globalsPtr) [] none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.globOp .globalsPtr) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.globOp .globalsPtr) args before accounted space).1
    have second := doAppAux_globalsPtr_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

/-- Installing a globals pointer changes the global field but preserves code. -/
theorem doAppAux_setGlobalsPtr_code {C F : Type} (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.globOp .setGlobalsPtr) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons item rest =>
    cases rest with
    | cons head tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases item <;> simp [doAppAux, applyNonFfi] at run
      case refPtr bit ptr =>
        cases bit <;> simp at run
        obtain ⟨rfl, rfl⟩ := run
        rfl

theorem evaluate_assign_setGlobalsPtr_code {C F : Type} (dest name : Nat) (state : State C F) :
    (evaluate (.assign dest (.globOp .setGlobalsPtr) [name] none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.globOp .setGlobalsPtr) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.globOp .setGlobalsPtr) args before accounted space).1
    have second := doAppAux_setGlobalsPtr_code args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

/-- Reading a global leaves the source code table unchanged. -/
theorem doAppAux_globalLoad_code {C F : Type} (index : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.globOp (.global index)) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | cons a rest => simp [doAppAux, applyNonFfi] at run
  | nil =>
    cases global : state.global with
    | none => simp [doAppAux, applyNonFfi, global] at run
    | some ptr =>
      cases found : sptLookup ptr state.refs with
      | none => simp [doAppAux, applyNonFfi, global, found] at run
      | some entry =>
        cases entry <;> simp [doAppAux, applyNonFfi, global, found] at run
        case valueArray values =>
          cases item : values[index]? with
          | none => simp [item] at run
          | some result =>
            simp [item] at run
            obtain ⟨rfl, rfl⟩ := run
            rfl

theorem evaluate_assign_globalLoad_code {C F : Type} (dest index : Nat) (state : State C F) :
    (evaluate (.assign dest (.globOp (.global index)) [] none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after value code run
  simp only [doApp] at run
  cases space : doSpace (.globOp (.global index)) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.globOp (.global index)) args before accounted space).1
    have second := doAppAux_globalLoad_code index args _ after value run
    simpa [doStack, doLimSafe, first, code] using second

/-- A successful global write updates references but preserves code. -/
theorem doAppAux_globalStore_code {C F : Type} (index : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value)
    (run : doAppAux (.globOp (.setGlobal index)) args state = .val (value, next)) : next.code = state.code := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons item rest =>
    cases rest with
    | cons head tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases global : state.global with
      | none => simp [doAppAux, applyNonFfi, global] at run
      | some ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [doAppAux, applyNonFfi, global, found] at run
        | some entry =>
          cases entry <;> simp [doAppAux, applyNonFfi, global, found] at run
          case valueArray values =>
            by_cases bound : index < values.length
            · simp [bound] at run
              obtain ⟨rfl, rfl⟩ := run
              rfl
            · simp [bound] at run

theorem evaluate_assign_globalStore_code {C F : Type} (dest index value : Nat) (state : State C F) :
    (evaluate (.assign dest (.globOp (.setGlobal index)) [value] none) state).2.code = state.code := by
  apply evaluate_assign_code_step
  intro args before after result code run
  simp only [doApp] at run
  cases space : doSpace (.globOp (.setGlobal index)) args before with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := (doSpace_code_const (.globOp (.setGlobal index)) args before accounted space).1
    have second := doAppAux_globalStore_code index args _ after result run
    simpa [doStack, doLimSafe, first, code] using second

/-- Every program in the current non-call simulation fragment preserves its
code table, including all failing executions. This is Lean-side infrastructure,
not a port of the unrestricted HOL compiler-correctness theorem. -/
theorem verifiedFragment_code {C F : Type} (program : DataLang.Prog) (fragment : VerifiedFragment program) :
    ∀ state : State C F, (evaluate program state).2.code = state.code := by
  induction fragment with
  | skip => intro state; simp [evaluate]
  | tick => intro state; exact evaluate_tick_code state
  | move dest src => intro state; exact evaluate_move_code dest src state
  | globalsPtr dest => intro state; exact evaluate_assign_globalsPtr_code dest state
  | byteOp dest left right op =>
    intro state
    exact evaluate_assign_word_code dest (.wordOpw .w8 op) [left, right] none state
  | byteCompare dest left right kind =>
    intro state
    exact evaluate_assign_word_code dest (.wordTest .w8 kind.test) [left, right] none state
  | setGlobalsPtr dest name => intro state; exact evaluate_assign_setGlobalsPtr_code dest name state
  | globalLoad dest index => intro state; exact evaluate_assign_globalLoad_code dest index state
  | globalStore dest index value => intro state; exact evaluate_assign_globalStore_code dest index value state
  | label dest label => intro state; exact evaluate_assign_label_code dest label [] none state
  | emptyCons dest tag bound =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.cons tag) [] none state (doAppAux_cons_code tag)
  | blockTagLen dest src tag wanted =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.tagLenEq tag wanted) [src] none state
      (doAppAux_blockCompare_code (.tagLenEq tag wanted) (Or.inr (Or.inr (Or.inl ⟨tag, wanted, rfl⟩))))
  | blockTag dest src tag =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.tagEq tag) [src] none state
      (doAppAux_blockCompare_code (.tagEq tag) (Or.inl ⟨tag, rfl⟩))
  | blockLen dest src wanted =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.lenEq wanted) [src] none state
      (doAppAux_blockCompare_code (.lenEq wanted) (Or.inr (Or.inl ⟨wanted, rfl⟩)))
  | blockLength dest src =>
    intro state
    exact evaluate_assign_block_code_of_aux dest .lengthBlock [src] none state
      (doAppAux_blockCompare_code .lengthBlock (Or.inr (Or.inr (Or.inr rfl))))
  | blockBounds dest base index =>
    intro state
    exact evaluate_assign_block_code_of_aux dest .boundsCheckBlock [base, index] none state doAppAux_blockBounds_code
  | byteBounds dest base index loose =>
    intro state
    exact evaluate_assign_byteBounds_code dest loose [base, index] state
  | arrayBounds dest base index =>
    intro state
    exact evaluate_assign_arrayBounds_code dest [base, index] state
  | arrayLength dest base =>
    intro state
    exact evaluate_assign_arrayLength_code dest [base] state
  | byteLength dest base =>
    intro state
    exact evaluate_assign_byteLength_code dest [base] state
  | dynamicElement dest base index =>
    intro state
    exact evaluate_assign_dynamicElement_code dest [base, index] state
  | byteElement dest base index =>
    intro state
    exact evaluate_assign_byteElement_code dest [base, index] state
  | byteStore dest base index value =>
    intro state
    exact evaluate_assign_byteStore_code dest [base, index, value] state
  | arrayStore dest base index value =>
    intro state
    exact evaluate_assign_arrayStore_code dest [base, index, value] state
  | element dest src index =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.elemAt index) [src] none state (doAppAux_elemAt_code index)
  | lessConst dest src n => intro state; exact evaluate_assign_int_code dest (.lessConstSmall n) [src] none state
  | boolTest dest left right test =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.boolTest test) [left, right] none state (doAppAux_boolTest_code test)
  | boolNot dest src =>
    intro state
    exact evaluate_assign_block_code_of_aux dest .boolNot [src] none state doAppAux_boolNot_code
  | intConst dest i => intro state; exact evaluate_assign_int_code dest (.const i) [] none state
  | ret names => intro state; exact evaluate_return_code names state
  | raise name => intro state; exact evaluate_raise_code name state
  | @seq first second firstFrag secondFrag firstIH secondIH =>
    intro state
    exact evaluate_seq_code_step first second state (firstIH state) (fun mid _ _ => secondIH mid)
  | @ite name yes no yesFrag noFrag yesIH noIH =>
    intro state
    exact evaluate_if_code_step name yes no state (yesIH state) (noIH state)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
