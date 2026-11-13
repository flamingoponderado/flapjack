module

public import Flapjack.Compiler.Backend.BviToData.Assign
public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
public import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame
public import Mathlib.Tactic.CasesM

@[expose] public section

/-! Assignment local/control frames for the BVI-to-data operation proof. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Block lowering preserves the operation and operands. It either puts the
compiler's roots on the assignment or makes space using those same roots. This
is Flapjack infrastructure for the operation simulation. -/
theorem iAssign_block_shape (op : ClosLang.BlockOp) (dest : Nat) (operands live corr : List Nat) :
    iAssign dest (.blockOp op) operands live corr =
      if DataLang.opRequiresNames (.blockOp op) then
        .assign dest (.blockOp op) operands (some (namesOfList (operands ++ live ++ corr)))
      else if DataSpace.opSpaceReq (.blockOp op) operands.length = 0 then
        .assign dest (.blockOp op) operands none
      else .seq (.makeSpace (DataSpace.opSpaceReq (.blockOp op) operands.length)
        (namesOfList (operands ++ live ++ corr))) (.assign dest (.blockOp op) operands none) := by
  simp [iAssign]

/-- Thunk lowering preserves the operation and operands. It either puts the
compiler's roots on the assignment or makes space using those same roots. This
is Flapjack infrastructure for the operation simulation. -/
theorem iAssign_thunk_shape (op : AstHOL.ThunkOp) (dest : Nat) (operands live corr : List Nat) :
    iAssign dest (.thunkOp op) operands live corr =
      if DataLang.opRequiresNames (.thunkOp op) then
        .assign dest (.thunkOp op) operands (some (namesOfList (operands ++ live ++ corr)))
      else if DataSpace.opSpaceReq (.thunkOp op) operands.length = 0 then
        .assign dest (.thunkOp op) operands none
      else .seq (.makeSpace (DataSpace.opSpaceReq (.thunkOp op) operands.length)
        (namesOfList (operands ++ live ++ corr))) (.assign dest (.thunkOp op) operands none) := by
  simp [iAssign]

/-- Memory lowering preserves the operation and operands. It either puts the
compiler's roots on the assignment or makes space using those same roots. This
is Flapjack infrastructure for the operation simulation. -/
theorem iAssign_mem_shape (op : ClosLang.MemOp) (dest : Nat) (operands live corr : List Nat) :
    iAssign dest (.memOp op) operands live corr =
      if DataLang.opRequiresNames (.memOp op) then
        .assign dest (.memOp op) operands (some (namesOfList (operands ++ live ++ corr)))
      else if DataSpace.opSpaceReq (.memOp op) operands.length = 0 then
        .assign dest (.memOp op) operands none
      else .seq (.makeSpace (DataSpace.opSpaceReq (.memOp op) operands.length)
        (namesOfList (operands ++ live ++ corr))) (.assign dest (.memOp op) operands none) := by
  simp [iAssign]

/-- Local and control frame for an assignment with an unchanged operation
and operands. The shape and primitive frames are Flapjack infrastructure. -/
theorem evaluate_iAssign_lookup_of_shape {C F : Type} (op : ClosLang.Op) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (shape : iAssign dest op operands live corr =
      if DataLang.opRequiresNames op then
        .assign dest op operands (some (namesOfList (operands ++ live ++ corr)))
      else if DataSpace.opSpaceReq op operands.length = 0 then
        .assign dest op operands none
      else .seq (.makeSpace (DataSpace.opSpaceReq op operands.length)
        (namesOfList (operands ++ live ++ corr))) (.assign dest op operands none))
    (primitiveFrame : ∀ (args : List DataSem.Value) (before after : DataSem.State C F) (value : DataSem.Value),
      DataSem.doApp op args before = .val (value, after) → DataSem.SameLocalControl before after)
    (run : DataSem.evaluate (iAssign dest op operands live corr) state = (none, next)) :
    ∃ (value : DataSem.Value) (cutEnabled : Bool), sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if cutEnabled then (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals) ∧ DataSem.SameControl state next := by
  classical
  by_cases names : DataLang.opRequiresNames op
  · simp only [shape, names, if_true] at run
    obtain ⟨prepared, value, cut, locals, control⟩ :=
      DataSem.evaluate_assign_locals op dest operands
        (some (namesOfList (operands ++ live ++ corr))) state next primitiveFrame run
    refine ⟨value, true, ?_, ?_, control⟩
    · simp [locals, sptLookup_sptInsert_same]
    · intro key different
      rw [locals, sptLookup_sptInsert_ne dest key value prepared.locals different]
      simpa using cutStateOpt_names_lookup true (operands ++ live ++ corr) state prepared key cut
  · by_cases space : DataSpace.opSpaceReq op operands.length = 0
    · simp only [shape, names, space, if_true] at run
      obtain ⟨prepared, value, cut, locals, control⟩ :=
        DataSem.evaluate_assign_locals op dest operands none state next primitiveFrame run
      simp [DataSem.cutStateOpt] at cut
      subst prepared
      refine ⟨value, false, ?_, ?_, control⟩
      · simp [locals, sptLookup_sptInsert_same]
      · intro key different
        simpa [locals] using sptLookup_sptInsert_ne dest key value state.locals different
    · simp only [shape, names, if_false, space] at run
      obtain ⟨mid, firstRun, secondRun⟩ :=
        DataSem.evaluate_seq_inv_control
          (.makeSpace (DataSpace.opSpaceReq op operands.length) (namesOfList (operands ++ live ++ corr)))
          (.assign dest op operands none) state next
          (DataSem.evaluate_makeSpace_control _ _) run
      have midLocals := evaluate_makeSpace_names_locals _ (operands ++ live ++ corr) state mid firstRun
      obtain ⟨prepared, value, cut, locals, control⟩ :=
        DataSem.evaluate_assign_locals op dest operands none mid next primitiveFrame secondRun
      simp [DataSem.cutStateOpt] at cut
      subst prepared
      refine ⟨value, true, ?_, ?_, (DataSem.evaluate_makeSpace_control _ _ state mid firstRun).trans control⟩
      · simp [locals, sptLookup_sptInsert_same]
      · intro key different
        rw [locals, sptLookup_sptInsert_ne dest key value mid.locals different, midLocals]
        exact lookup_cut_namesOfList (operands ++ live ++ corr) state.locals key

/-- A compiled block op writes its destination and preserves the
compiler's live roots and control fields. -/
theorem evaluate_iAssign_block_lookup {C F : Type} (op : ClosLang.BlockOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.blockOp op) operands live corr) state = (none, next)) :
    ∃ (value : DataSem.Value) (cutEnabled : Bool), sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if cutEnabled then (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals) ∧ DataSem.SameControl state next :=
  evaluate_iAssign_lookup_of_shape (.blockOp op) dest operands live corr state next
    (iAssign_block_shape op dest operands live corr) (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.blockOp op) args before after value run) run

/-- A compiled thunk operation writes its destination and preserves the
compiler's live roots and control fields. -/
theorem evaluate_iAssign_thunk_lookup {C F : Type} (op : AstHOL.ThunkOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.thunkOp op) operands live corr) state = (none, next)) :
    ∃ (value : DataSem.Value) (cutEnabled : Bool), sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if cutEnabled then (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals) ∧ DataSem.SameControl state next :=
  evaluate_iAssign_lookup_of_shape (.thunkOp op) dest operands live corr state next
    (iAssign_thunk_shape op dest operands live corr) (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.thunkOp op) args before after value run) run

/-- A compiled memory operation writes its destination and preserves the
compiler's live roots and control fields. -/
theorem evaluate_iAssign_mem_lookup {C F : Type} (op : ClosLang.MemOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.memOp op) operands live corr) state = (none, next)) :
    ∃ (value : DataSem.Value) (cutEnabled : Bool), sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if cutEnabled then (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals) ∧ DataSem.SameControl state next :=
  evaluate_iAssign_lookup_of_shape (.memOp op) dest operands live corr state next
    (iAssign_mem_shape op dest operands live corr)
    (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.memOp op) args before after value run) run

/-- Integer lowering emits a single assignment, including its two operand
reversal cases. -/
theorem iAssign_int_shape (op : ClosLang.IntOp) (dest : Nat) (operands live corr : List Nat) :
    ∃ actualOp actualOperands actualLive,
      iAssign dest (.intOp op) operands live corr = .assign dest (.intOp actualOp) actualOperands actualLive := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- The live-name set of every generated integer assignment is the original
compiler root set whenever the operation requires a cut. -/
theorem iAssign_int_shape_roots (op : ClosLang.IntOp) (dest : Nat) (operands live corr : List Nat) :
    ∃ actualOp actualOperands,
      iAssign dest (.intOp op) operands live corr =
        .assign dest (.intOp actualOp) actualOperands
          (if DataLang.opRequiresNames (.intOp op) then some (namesOfList (operands ++ live ++ corr)) else none) := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Successful generated integer assignments expose the actual operation,
operand read, live cut and primitive state; the primitive leaves the cut
environment, stack, handler and clock unchanged. -/
theorem evaluate_iAssign_int_frame {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∃ actualOp actualOperands actualLive args prepared applied value,
      iAssign dest (.intOp op) operands live corr = .assign dest (.intOp actualOp) actualOperands actualLive ∧
      DataSem.getVars actualOperands state.locals = some args ∧
      DataSem.cutStateOpt actualLive state = some prepared ∧
      DataSem.doApp (.intOp actualOp) args prepared = .val (value, applied) ∧
      next = DataSem.setVar dest value (DataSem.installSfs (.intOp actualOp) applied) ∧
      DataSem.SameLocalControl prepared applied := by
  obtain ⟨actualOp, actualOperands, actualLive, shape⟩ := iAssign_int_shape op dest operands live corr
  rw [shape] at run
  obtain ⟨args, prepared, applied, value, read, cut, app, output, frame⟩ :=
    DataSem.evaluate_assign_int_frame actualOp dest actualOperands actualLive state next run
  exact ⟨actualOp, actualOperands, actualLive, args, prepared, applied, value, shape, read, cut, app, output, frame⟩

/-- Successful compiled integer assignments preserve the source target's
control stack, handler, local-size metadata and clock. -/
theorem evaluate_iAssign_int_control {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    next.stack = state.stack ∧ next.handler = state.handler ∧ next.localsSize = state.localsSize ∧
      next.stackFrameSizes = state.stackFrameSizes ∧ next.clock = state.clock := by
  obtain ⟨actualOp, actualOperands, actualLive, args, prepared, applied, value, shape, read, cut, app, output, frame⟩ :=
    evaluate_iAssign_int_frame op dest operands live corr state next run
  have cutControl := DataSem.cutStateOpt_control actualLive state prepared cut
  rcases cutControl with ⟨stack1, handler1, size1, sizes1, clock1⟩
  rcases frame with ⟨_, stack2, handler2, size2, sizes2, clock2⟩
  rw [output]
  simp [DataSem.setVar, DataSem.installSfs, stack2, handler2, size2, sizes2, clock2,
    stack1, handler1, size1, sizes1, clock1]

/-- A successful generated integer assignment retains every original root
other than the destination, whether the operation cuts locals or not. -/
theorem evaluate_iAssign_int_keepRoots {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∀ key ∈ operands ++ live ++ corr, key ≠ dest → sptLookup key next.locals = sptLookup key state.locals := by
  obtain ⟨actualOp, actualOperands, shape⟩ := iAssign_int_shape_roots op dest operands live corr
  rw [shape] at run
  obtain ⟨prepared, value, cut, locals, control⟩ :=
    DataSem.evaluate_assign_locals (.intOp actualOp) dest actualOperands
      (if DataLang.opRequiresNames (.intOp op) then some (namesOfList (operands ++ live ++ corr)) else none)
      state next (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.intOp actualOp) args before after value run) run
  intro key member different
  rw [locals, sptLookup_sptInsert_ne dest key value prepared.locals different]
  exact cutStateOpt_names_keep (DataLang.opRequiresNames (.intOp op)) (operands ++ live ++ corr)
    state prepared key member cut

/-- Successful generated integer assignments have exactly the compiler's
optional root cut followed by a destination update. -/
theorem evaluate_iAssign_int_exactLocals {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∃ prepared value,
      DataSem.cutStateOpt (if DataLang.opRequiresNames (.intOp op)
        then some (namesOfList (operands ++ live ++ corr)) else none) state = some prepared ∧
      next.locals = sptInsert dest value prepared.locals ∧ DataSem.SameControl state next := by
  obtain ⟨actualOp, actualOperands, shape⟩ := iAssign_int_shape_roots op dest operands live corr
  rw [shape] at run
  exact DataSem.evaluate_assign_locals (.intOp actualOp) dest actualOperands
    (if DataLang.opRequiresNames (.intOp op) then some (namesOfList (operands ++ live ++ corr)) else none)
    state next (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.intOp actualOp) args before after value run) run

/-- Lookup after a successful generated integer assignment is the new value
at the destination and the optional compiler root cut everywhere else. -/
theorem evaluate_iAssign_int_lookup {C F : Type} (op : ClosLang.IntOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.intOp op) operands live corr) state = (none, next)) :
    ∃ value, sptLookup dest next.locals = some value ∧
      ∀ key, key ≠ dest → sptLookup key next.locals =
        if DataLang.opRequiresNames (.intOp op) then
          (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals := by
  classical
  obtain ⟨prepared, value, cut, locals, _⟩ := evaluate_iAssign_int_exactLocals op dest operands live corr state next run
  refine ⟨value, ?_, ?_⟩
  · simp [locals, sptLookup_sptInsert_same]
  · intro key different
    rw [locals, sptLookup_sptInsert_ne dest key value prepared.locals different]
    exact cutStateOpt_names_lookup (DataLang.opRequiresNames (.intOp op)) (operands ++ live ++ corr)
      state prepared key cut

/-- A successful integer `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. This includes comparison
rewrites and both forms of live-name handling. -/
theorem evaluate_iAssign_int_outcome {C F : Type} (op : ClosLang.IntOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.intOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.intOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.intOp op) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  have control : DataSem.SameControl target targetNext :=
    evaluate_iAssign_int_control op dest operands live corr target targetNext execution
  have keeps := evaluate_iAssign_int_keepRoots op dest operands live corr target targetNext execution
  obtain ⟨_, _, lookupOther⟩ := evaluate_iAssign_int_lookup op dest operands live corr target targetNext execution
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup
        · split at lookup <;> simp_all
        · exact lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- Word lowering emits an assignment, optionally preceded by make-space;
the byte comparison rewrites remain word assignments. -/
theorem iAssign_word_shape (op : ClosLang.WordOp) (dest : Nat) (operands live corr : List Nat) :
    (∃ actualOp actualOperands actualLive,
      iAssign dest (.wordOp op) operands live corr = .assign dest (.wordOp actualOp) actualOperands actualLive) ∨
    (∃ actualOp actualOperands actualLive amount roots,
      iAssign dest (.wordOp op) operands live corr =
        .seq (.makeSpace amount roots) (.assign dest (.wordOp actualOp) actualOperands actualLive)) := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  all_goals try (cases_type AstHOL.WordSize)
  all_goals try (cases_type AstHOL.Test)
  all_goals try (cases_type Flapjack.Opb)
  all_goals try (cases_type Bool)
  all_goals simp

/-- The optional make-space prelude for a word assignment uses exactly the
compiler's original root names, and its assignment has no further cut. -/
theorem iAssign_word_shape_roots (op : ClosLang.WordOp) (dest : Nat) (operands live corr : List Nat) :
    (∃ actualOp actualOperands,
      iAssign dest (.wordOp op) operands live corr = .assign dest (.wordOp actualOp) actualOperands none) ∨
    (∃ actualOp actualOperands amount,
      iAssign dest (.wordOp op) operands live corr =
        .seq (.makeSpace amount (namesOfList (operands ++ live ++ corr)))
          (.assign dest (.wordOp actualOp) actualOperands none)) := by
  cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  all_goals try (cases_type AstHOL.WordSize)
  all_goals try (cases_type AstHOL.Test)
  all_goals try (cases_type Flapjack.Opb)
  all_goals try (cases_type Bool)
  all_goals simp

/-- Successful generated word assignments preserve the target control
stack, handler, metadata and clock, including through the make-space prelude. -/
theorem evaluate_iAssign_word_control {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.wordOp op) operands live corr) state = (none, next)) :
    DataSem.SameControl state next := by
  rcases iAssign_word_shape op dest operands live corr with direct | spaced
  · obtain ⟨actualOp, actualOperands, actualLive, shape⟩ := direct
    rw [shape] at run
    exact DataSem.evaluate_assign_word_control actualOp dest actualOperands actualLive state next run
  · obtain ⟨actualOp, actualOperands, actualLive, amount, roots, shape⟩ := spaced
    rw [shape] at run
    exact DataSem.evaluate_seq_control (.makeSpace amount roots) (.assign dest (.wordOp actualOp) actualOperands actualLive)
      state next (DataSem.evaluate_makeSpace_control amount roots)
      (DataSem.evaluate_assign_word_control actualOp dest actualOperands actualLive) run

/-- A successful word assignment writes its destination and otherwise either
retains all locals or retains exactly the compiler roots after make-space. -/
theorem evaluate_iAssign_word_lookup {C F : Type} (op : ClosLang.WordOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.wordOp op) operands live corr) state = (none, next)) :
    ∃ (value : DataSem.Value) (cutEnabled : Bool), sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if cutEnabled then (if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none)
        else sptLookup key state.locals) ∧ DataSem.SameControl state next := by
  classical
  have control := evaluate_iAssign_word_control op dest operands live corr state next run
  rcases iAssign_word_shape_roots op dest operands live corr with direct | spaced
  · obtain ⟨actualOp, actualOperands, shape⟩ := direct
    rw [shape] at run
    obtain ⟨prepared, value, cut, locals, _⟩ :=
      DataSem.evaluate_assign_locals (.wordOp actualOp) dest actualOperands none state next
        (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.wordOp actualOp) args before after value run) run
    simp [DataSem.cutStateOpt] at cut
    subst prepared
    refine ⟨value, false, ?_, ?_, control⟩
    · simp [locals, sptLookup_sptInsert_same]
    · intro key different
      simpa [locals] using sptLookup_sptInsert_ne dest key value state.locals different
  · obtain ⟨actualOp, actualOperands, amount, shape⟩ := spaced
    rw [shape] at run
    obtain ⟨mid, firstRun, secondRun⟩ :=
      DataSem.evaluate_seq_inv_control (.makeSpace amount (namesOfList (operands ++ live ++ corr)))
        (.assign dest (.wordOp actualOp) actualOperands none) state next
        (DataSem.evaluate_makeSpace_control amount (namesOfList (operands ++ live ++ corr))) run
    have midLocals := evaluate_makeSpace_names_locals amount (operands ++ live ++ corr) state mid firstRun
    obtain ⟨prepared, value, cut, locals, _⟩ :=
      DataSem.evaluate_assign_locals (.wordOp actualOp) dest actualOperands none mid next
        (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.wordOp actualOp) args before after value run) secondRun
    simp [DataSem.cutStateOpt] at cut
    subst prepared
    refine ⟨value, true, ?_, ?_, control⟩
    · simp [locals, sptLookup_sptInsert_same]
    · intro key different
      rw [locals, sptLookup_sptInsert_ne dest key value mid.locals different, midLocals]
      exact lookup_cut_namesOfList (operands ++ live ++ corr) state.locals key

/-- A successful generated FFI assignment writes its destination and
retains precisely the original compiler root names everywhere else. -/
theorem evaluate_iAssign_ffi_lookup {C F : Type} (name : Basis.Pure.MlString.MlString) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.ffi name) operands live corr) state = (none, next)) :
    ∃ value, sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals =
        if key ∈ operands ++ live ++ corr then sptLookup key state.locals else none) ∧
      DataSem.SameControl state next := by
  classical
  have shape : iAssign dest (.ffi name) operands live corr =
      .assign dest (.ffi name) operands (some (namesOfList (operands ++ live ++ corr))) := by
    simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset]
  rw [shape] at run
  obtain ⟨prepared, value, cut, locals, control⟩ :=
    DataSem.evaluate_assign_locals (.ffi name) dest operands (some (namesOfList (operands ++ live ++ corr)))
      state next (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.ffi name) args before after value run) run
  refine ⟨value, ?_, ?_, control⟩
  · simp [locals, sptLookup_sptInsert_same]
  · intro key different
    rw [locals, sptLookup_sptInsert_ne dest key value prepared.locals different]
    simpa using cutStateOpt_names_lookup true (operands ++ live ++ corr) state prepared key cut

/-- Global assignments have no live cut or make-space prelude. -/
theorem evaluate_iAssign_global_lookup {C F : Type} (op : ClosLang.GlobOp) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.globOp op) operands live corr) state = (none, next)) :
    ∃ value, sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals = sptLookup key state.locals) ∧
      DataSem.SameControl state next := by
  have shape : iAssign dest (.globOp op) operands live corr = .assign dest (.globOp op) operands none := by
    cases op <;> simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  rw [shape] at run
  obtain ⟨prepared, value, cut, locals, control⟩ :=
    DataSem.evaluate_assign_locals (.globOp op) dest operands none state next (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.globOp op) args before after value run) run
  simp [DataSem.cutStateOpt] at cut
  subst prepared
  refine ⟨value, ?_, ?_, control⟩
  · simp [locals, sptLookup_sptInsert_same]
  · intro key different
    simpa [locals] using sptLookup_sptInsert_ne dest key value state.locals different

/-- A successful word `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. This includes comparison
rewrites and the optional make-space cut. -/
theorem evaluate_iAssign_word_outcome {C F : Type} (op : ClosLang.WordOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.wordOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.wordOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.wordOp op) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, cutEnabled, _, lookupOther, control⟩ :=
    evaluate_iAssign_word_lookup op dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different]
    cases cutEnabled with
    | false => rfl
    | true => simp only [if_true, if_pos member]
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup
        · split at lookup <;> simp_all
        · exact lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- A successful block op `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. This includes the compiler live-name and space handling. -/
theorem evaluate_iAssign_block_outcome {C F : Type} (op : ClosLang.BlockOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.blockOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.blockOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.blockOp op) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, cutEnabled, _, lookupOther, control⟩ :=
    evaluate_iAssign_block_lookup op dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different]
    cases cutEnabled with
    | false => rfl
    | true => simp only [if_true, if_pos member]
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup
        · split at lookup <;> simp_all
        · exact lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- A successful thunk operation `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. This includes the compiler live-name and space handling. -/
theorem evaluate_iAssign_thunk_outcome {C F : Type} (op : AstHOL.ThunkOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (notForce : op ≠ .forceThunk)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.thunkOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.thunkOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.thunkOp op) target source operands live corr env args dest result next
      (by simp) (by simpa using notForce) related vars livePresent read run
  obtain ⟨_, cutEnabled, _, lookupOther, control⟩ :=
    evaluate_iAssign_thunk_lookup op dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different]
    cases cutEnabled with
    | false => rfl
    | true => simp only [if_true, if_pos member]
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup
        · split at lookup <;> simp_all
        · exact lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- A successful memory `iAssign` establishes the continuing invariant. -/
theorem evaluate_iAssign_mem_outcome {C F : Type} (op : ClosLang.MemOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.memOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.memOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.memOp op) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, cutEnabled, _, lookupOther, control⟩ :=
    evaluate_iAssign_mem_lookup op dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different]
    cases cutEnabled with
    | false => rfl
    | true => simp only [if_true, if_pos member]
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup
        · split at lookup <;> simp_all
        · exact lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- A successful FFI `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. This retains the compiler live-name cut. -/
theorem evaluate_iAssign_ffi_outcome {C F : Type} (name : Basis.Pure.MlString.MlString)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.ffi name) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.ffi name) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.ffi name) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, _, lookupOther, control⟩ :=
    evaluate_iAssign_ffi_lookup name dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different, if_pos member]
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup <;> simp_all
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- A successful global `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. Global assignments retain the other locals. -/
theorem evaluate_iAssign_global_outcome {C F : Type} (op : ClosLang.GlobOp)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.globOp op) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.globOp op) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.globOp op) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, _, lookupOther, control⟩ :=
    evaluate_iAssign_global_lookup op dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    exact lookupOther key different
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    exact fresh key (by omega)
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        simpa [lookupOther key equal] using lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

/-- Label assignments have no live cut or make-space prelude. -/
theorem evaluate_iAssign_label_lookup {C F : Type} (label : Nat) (dest : Nat)
    (operands live corr : List Nat) (state next : DataSem.State C F)
    (run : DataSem.evaluate (iAssign dest (.label label) operands live corr) state = (none, next)) :
    ∃ value, sptLookup dest next.locals = some value ∧
      (∀ key, key ≠ dest → sptLookup key next.locals = sptLookup key state.locals) ∧
      DataSem.SameControl state next := by
  have shape : iAssign dest (.label label) operands live corr = .assign dest (.label label) operands none := by
    simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  rw [shape] at run
  obtain ⟨prepared, value, cut, locals, control⟩ :=
    DataSem.evaluate_assign_locals (.label label) dest operands none state next (fun args before after value run => by simpa using DataSem.doApp_controlFrame (.label label) args before after value run) run
  simp [DataSem.cutStateOpt] at cut
  subst prepared
  refine ⟨value, ?_, ?_, control⟩
  · simp [locals, sptLookup_sptInsert_same]
  · intro key different
    simpa [locals] using sptLookup_sptInsert_ne dest key value state.locals different

/-- A successful label `iAssign` establishes the complete continuing
compiler invariant when its destination is fresh. Label assignments retain the other locals. -/
theorem evaluate_iAssign_label_outcome {C F : Type} (label : Nat)
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.label label) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.label label) operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  obtain ⟨targetNext, value, execution, projected, finalRel, destRead⟩ :=
    evaluate_iAssign_success (.label label) target source operands live corr env args dest result next
      (by simp) (by simp) related vars livePresent read run
  obtain ⟨_, _, lookupOther, control⟩ :=
    evaluate_iAssign_label_lookup label dest operands live corr target targetNext execution
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    exact lookupOther key different
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel, destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, control.1.symm, control.2.1.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    exact fresh key (by omega)
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        simpa [lookupOther key equal] using lookup
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · exact DataSem.SameControl.jumpExc_ne_none control
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

end Flapjack.Compiler.Backend.BviToData
