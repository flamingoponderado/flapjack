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
  | label dest label => intro state; exact evaluate_assign_label_code dest label [] none state
  | emptyCons dest tag bound =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.cons tag) [] none state (doAppAux_cons_code tag)
  | blockTagEmpty dest src tag =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.tagLenEq tag 0) [src] none state
      (doAppAux_blockCompare_code (.tagLenEq tag 0) (Or.inr (Or.inr (Or.inl ⟨tag, 0, rfl⟩))))
  | blockTag dest src tag =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.tagEq tag) [src] none state
      (doAppAux_blockCompare_code (.tagEq tag) (Or.inl ⟨tag, rfl⟩))
  | blockEmpty dest src =>
    intro state
    exact evaluate_assign_block_code_of_aux dest (.lenEq 0) [src] none state
      (doAppAux_blockCompare_code (.lenEq 0) (Or.inr (Or.inl ⟨0, rfl⟩)))
  | blockLength dest src =>
    intro state
    exact evaluate_assign_block_code_of_aux dest .lengthBlock [src] none state
      (doAppAux_blockCompare_code .lengthBlock (Or.inr (Or.inr (Or.inr rfl))))
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
