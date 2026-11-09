module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Space

@[expose] public section

/-! Comparison rewrites used by BVI-to-data assignment compilation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A successful greater-than integer operation is a less-than operation on
the reversed arguments, with the same result and source state. -/
theorem doApp_intGreater_reverse {C F : Type} (args : List BvlSem.Value)
    (source next : BviSem.BviState C F) (result : BvlSem.Value)
    (run : BviSem.doApp (.intOp .greater) args source = .val (result, next)) :
    BviSem.doApp (.intOp .less) args.reverse source = .val (result, next) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyNumeric, BvlSem.doIntApp] at run
    | cons b rest =>
      cases rest with
      | cons c tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyNumeric, BvlSem.doIntApp] at run
      | nil =>
        cases a <;> cases b <;> simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]

/-- Greater-or-equal similarly becomes less-or-equal on reversed inputs. -/
theorem doApp_intGreaterEq_reverse {C F : Type} (args : List BvlSem.Value)
    (source next : BviSem.BviState C F) (result : BvlSem.Value)
    (run : BviSem.doApp (.intOp .greaterEq) args source = .val (result, next)) :
    BviSem.doApp (.intOp .lessEq) args.reverse source = .val (result, next) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyNumeric, BvlSem.doIntApp] at run
    | cons b rest =>
      cases rest with
      | cons c tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyNumeric, BvlSem.doIntApp] at run
      | nil =>
        cases a <;> cases b <;> simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]

private theorem intCmp_reverse (a b : Int) :
    intCmp .gt a b = intCmp .lt b a ∧ intCmp .geq a b = intCmp .leq b a := by
  cases order : compare a b with
  | lt =>
    have less : a < b := Int.compare_eq_lt.mp order
    have reversed : compare b a = .gt := Int.compare_eq_gt.mpr less
    simp only [intCmp, order, reversed]
    exact ⟨rfl, rfl⟩
  | eq =>
    have equal : a = b := Int.compare_eq_eq.mp order
    subst b
    simp only [intCmp, order]
    exact ⟨rfl, rfl⟩
  | gt =>
    have less : b < a := Int.compare_eq_gt.mp order
    have reversed : compare b a = .lt := Int.compare_eq_lt.mpr less
    simp only [intCmp, order, reversed]
    exact ⟨rfl, rfl⟩

/-- A successful byte greater-than test is the corresponding less-than test
on the reversed operands. -/
theorem doApp_byteGreater_reverse {C F : Type} (args : List BvlSem.Value)
    (source next : BviSem.BviState C F) (result : BvlSem.Value)
    (run : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .gt))) args source = .val (result, next)) :
    BviSem.doApp (.wordOp (.wordTest .w8 (.compare .lt))) args.reverse source = .val (result, next) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
    | cons b rest =>
      cases rest with
      | cons c tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
      | nil =>
        cases a <;> cases b <;> simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral,
          (intCmp_reverse _ _).1, and_comm, and_left_comm, and_assoc]

/-- A byte greater-or-equal test likewise becomes less-or-equal on the
reversed operands. -/
theorem doApp_byteGreaterEq_reverse {C F : Type} (args : List BvlSem.Value)
    (source next : BviSem.BviState C F) (result : BvlSem.Value)
    (run : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .geq))) args source = .val (result, next)) :
    BviSem.doApp (.wordOp (.wordTest .w8 (.compare .leq))) args.reverse source = .val (result, next) := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
        BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
    | cons b rest =>
      cases rest with
      | cons c tail => simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
          BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral] at run
      | nil =>
        cases a <;> cases b <;> simp_all [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux,
          BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doWordApp, BvlSem.doWordAppIntegral,
          (intCmp_reverse _ _).2, and_comm, and_left_comm, and_assoc]

/-- Operand reads, live locals and the projected environment establish all
roots selected by the assignment compiler. -/
theorem roots_present {C F : Type} (target : DataSem.State C F)
    (operands live corr : List Nat) (env : List BvlSem.Value) (args : List DataSem.Value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args) :
    ∀ key ∈ operands ++ live ++ corr, sptLookup key target.locals ≠ none := by
  have operandPresent := getVars_present operands target.locals args read
  have corrRead := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresent := getVars_present corr (sptMap dataToBviValue target.locals) env corrRead
  intro key member
  simp only [List.mem_append] at member
  rcases member with operandOrLive | corrMember
  · rcases operandOrLive with operand | liveMember
    · exact operandPresent key operand
    · exact livePresent key liveMember
  · intro absent
    apply corrPresent key corrMember
    simp [sptLookup_sptMap, absent]

/-- The compiler's integer greater-than assignment executes the reversed
less-than operation, preserving the original root set and BVI result. -/
theorem evaluate_iAssign_intGreater {C F : Type} (target : DataSem.State C F)
    (source next : BviSem.BviState C F) (operands live corr : List Nat)
    (env : List BvlSem.Value) (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.intOp .greater) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.intOp .greater) operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs (.intOp .less) targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs (.intOp .less) targetNext)) := by
  have reversedRun : BviSem.doApp (.intOp .less) (args.reverse.map dataToBviValue) source = .val (result, next) := by
    simpa [List.map_reverse] using doApp_intGreater_reverse (args.map dataToBviValue) source next result run
  obtain ⟨targetNext, value, targetRun, projected, finalRel⟩ :=
    evaluate_assign_reset (.intOp .less) target source (operands ++ live ++ corr) operands.reverse args.reverse dest result next
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [DataLang.opSpaceReset]) related (roots_present target operands live corr env args vars livePresent read)
      (DataProps.getVars_reverse operands target.locals args read) reversedRun
  refine ⟨targetNext, value, ?_, projected, finalRel⟩
  simpa [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset] using targetRun

/-- The compiler's integer greater-or-equal assignment executes the
reversed less-or-equal operation with the same BVI result. -/
theorem evaluate_iAssign_intGreaterEq {C F : Type} (target : DataSem.State C F)
    (source next : BviSem.BviState C F) (operands live corr : List Nat)
    (env : List BvlSem.Value) (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.intOp .greaterEq) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.intOp .greaterEq) operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs (.intOp .lessEq) targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs (.intOp .lessEq) targetNext)) := by
  have reversedRun : BviSem.doApp (.intOp .lessEq) (args.reverse.map dataToBviValue) source = .val (result, next) := by
    simpa [List.map_reverse] using doApp_intGreaterEq_reverse (args.map dataToBviValue) source next result run
  obtain ⟨targetNext, value, targetRun, projected, finalRel⟩ :=
    evaluate_assign_reset (.intOp .lessEq) target source (operands ++ live ++ corr) operands.reverse args.reverse dest result next
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [DataLang.opSpaceReset]) related (roots_present target operands live corr env args vars livePresent read)
      (DataProps.getVars_reverse operands target.locals args read) reversedRun
  refine ⟨targetNext, value, ?_, projected, finalRel⟩
  simpa [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset] using targetRun

/-- The byte greater-than compiler rewrite reads its operands in reverse and
executes the supported byte less-than assignment. -/
theorem evaluate_iAssign_byteGreater {C F : Type} (target : DataSem.State C F)
    (source next : BviSem.BviState C F) (operands live corr : List Nat)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target) (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .gt))) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.wordOp (.wordTest .w8 (.compare .gt))) operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs (.wordOp (.wordTest .w8 (.compare .lt))) targetNext)) ∧
      result = dataToBviValue value ∧
      stateRel next (DataSem.setVar dest value (DataSem.installSfs (.wordOp (.wordTest .w8 (.compare .lt))) targetNext)) := by
  have reversedRun : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .lt)))
      (args.reverse.map dataToBviValue) source = .val (result, next) := by
    simpa [List.map_reverse] using doApp_byteGreater_reverse (args.map dataToBviValue) source next result run
  obtain ⟨targetNext, value, targetRun, projected, finalRel⟩ :=
    evaluate_iAssign_noSpace (.wordOp (.wordTest .w8 (.compare .lt))) target source operands.reverse live corr args.reverse dest result next
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [DataLang.opRequiresNames, DataLang.opSpaceReset]) (by simp [DataSpace.opSpaceReq]) related
      (DataProps.getVars_reverse operands target.locals args read) reversedRun
  refine ⟨targetNext, value, ?_, projected, finalRel⟩
  simpa [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq] using targetRun

/-- The byte greater-or-equal compiler rewrite similarly executes the
reversed byte less-or-equal assignment. -/
theorem evaluate_iAssign_byteGreaterEq {C F : Type} (target : DataSem.State C F)
    (source next : BviSem.BviState C F) (operands live corr : List Nat)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target) (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .geq))) (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest (.wordOp (.wordTest .w8 (.compare .geq))) operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs (.wordOp (.wordTest .w8 (.compare .leq))) targetNext)) ∧
      result = dataToBviValue value ∧
      stateRel next (DataSem.setVar dest value (DataSem.installSfs (.wordOp (.wordTest .w8 (.compare .leq))) targetNext)) := by
  have reversedRun : BviSem.doApp (.wordOp (.wordTest .w8 (.compare .leq)))
      (args.reverse.map dataToBviValue) source = .val (result, next) := by
    simpa [List.map_reverse] using doApp_byteGreaterEq_reverse (args.map dataToBviValue) source next result run
  obtain ⟨targetNext, value, targetRun, projected, finalRel⟩ :=
    evaluate_iAssign_noSpace (.wordOp (.wordTest .w8 (.compare .leq))) target source operands.reverse live corr args.reverse dest result next
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp [DataLang.opRequiresNames, DataLang.opSpaceReset]) (by simp [DataSpace.opSpaceReq]) related
      (DataProps.getVars_reverse operands target.locals args read) reversedRun
  refine ⟨targetNext, value, ?_, projected, finalRel⟩
  simpa [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq] using targetRun

/-- Every successful supported primitive, including the compiler's four
comparison rewrites, has a corresponding `iAssign` evaluation. Installation,
byte copying and thunk forcing retain their separate source cases. -/
theorem evaluate_iAssign_success {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.evaluate (iAssign dest op operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧ sptLookup dest targetNext.locals = some value := by
  by_cases greater : op = .intOp .greater
  · subst op
    obtain ⟨s, value, execution, projected, finalRel⟩ :=
      evaluate_iAssign_intGreater target source next operands live corr env args dest result related vars livePresent read run
    exact ⟨_, value, execution, projected, finalRel, by simp [DataSem.setVar, sptLookup_sptInsert_same]⟩
  by_cases greaterEq : op = .intOp .greaterEq
  · subst op
    obtain ⟨s, value, execution, projected, finalRel⟩ :=
      evaluate_iAssign_intGreaterEq target source next operands live corr env args dest result related vars livePresent read run
    exact ⟨_, value, execution, projected, finalRel, by simp [DataSem.setVar, sptLookup_sptInsert_same]⟩
  by_cases byteGreater : op = .wordOp (.wordTest .w8 (.compare .gt))
  · subst op
    obtain ⟨s, value, execution, projected, finalRel⟩ :=
      evaluate_iAssign_byteGreater target source next operands live corr args dest result related read run
    exact ⟨_, value, execution, projected, finalRel, by simp [DataSem.setVar, sptLookup_sptInsert_same]⟩
  by_cases byteGreaterEq : op = .wordOp (.wordTest .w8 (.compare .geq))
  · subst op
    obtain ⟨s, value, execution, projected, finalRel⟩ :=
      evaluate_iAssign_byteGreaterEq target source next operands live corr args dest result related read run
    exact ⟨_, value, execution, projected, finalRel, by simp [DataSem.setVar, sptLookup_sptInsert_same]⟩
  · obtain ⟨s, value, execution, projected, finalRel⟩ :=
      evaluate_iAssign_supported op target source operands live corr env args dest result next notInstall greater
        greaterEq byteGreater byteGreaterEq notForce related vars livePresent read run
    exact ⟨_, value, execution, projected, finalRel, by simp [DataSem.setVar, sptLookup_sptInsert_same]⟩

end Flapjack.Compiler.Backend.BviToData
