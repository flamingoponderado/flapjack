module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateLocals
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyAuxFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.Variables
public import Flapjack.Compiler.Backend.Semantics.DataSem.Space

@[expose] public section

/-! Correctness of allocation-space reservation, including general sequences. -/

namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataProps Flapjack.SemanticPrimitivesHOL

private theorem composeSimulation {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second) :
    ∀ (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value)) (locals : Spt DataSem.Value),
      result ≠ some (.err (.abort .typeError)) → DataSem.evaluate (.seq first second) source = (result, sourceNext) →
      sptSubspt source.locals locals →
      ∃ out safe peak stackMax,
        DataSem.evaluate (.seq (compile first) (compile second)) { source with locals := locals } =
          (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
            else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
        sptSubspt sourceNext.locals out := by
  intro source sourceNext result locals notType run included
  rw [DataSem.evaluate, fixClock_evaluate] at run
  cases firstRun : DataSem.evaluate first source with
  | mk firstResult sourceMid =>
    rw [firstRun] at run
    cases firstResult with
    | none =>
      obtain ⟨midLocals, safe1, peak1, stack1, targetFirst, midIncluded⟩ :=
        firstIH source sourceMid none locals (by simp) firstRun included
      simp only [if_true] at targetFirst
      obtain ⟨out, safe2, peak2, stack2, targetSecond, finalIncluded⟩ :=
        secondIH sourceMid sourceNext result midLocals notType run midIncluded
      obtain ⟨stack3, safe3, peak3, transported⟩ :=
        evaluate_stackSafePeakSwap stack1 safe1
          (if result = none then { sourceNext with locals := out, safeForSpace := safe2, peakHeapLength := peak2, stackMax := stack2 }
            else { sourceNext with safeForSpace := safe2, peakHeapLength := peak2, stackMax := stack2 })
          { sourceMid with locals := midLocals } result peak1 (compile second) targetSecond
      refine ⟨out, safe3, peak3, stack3, ?_, finalIncluded⟩
      rw [DataSem.evaluate, fixClock_evaluate, targetFirst]
      cases result <;> simpa using transported
    | some outcome =>
      have eqs : result = some outcome ∧ sourceNext = sourceMid := Prod.mk.inj run.symm
      obtain ⟨rfl, rfl⟩ := eqs
      obtain ⟨out, safe, peak, stackMax, targetFirst, finalIncluded⟩ :=
        firstIH source sourceNext (some outcome) locals notType firstRun included
      refine ⟨out, safe, peak, stackMax, ?_, finalIncluded⟩
      rw [DataSem.evaluate, fixClock_evaluate, targetFirst]


private theorem compileSeqSkip (second : DataLang.Prog) :
    compile (.seq .skip second) = compile second := by
  cases h : space second with
  | inl body => simp [compile, space, h, pMakeSpace]
  | inr payload =>
    obtain ⟨amount, names, body⟩ := payload
    simp [compile, space, h, pMakeSpace]

private theorem evalSeqSkipAssoc {C F : Type} (first second : DataLang.Prog) (state : State C F) :
    evaluate (.seq (.seq first .skip) second) state = evaluate (.seq first second) state := by
  conv_lhs => rw [DataSem.evaluate, fixClock_evaluate, evaluate_seq_skip]
  rw [DataSem.evaluate, fixClock_evaluate]

/-- Normalizing a sparse tree produces a well-formed tree. This helper is
Flapjack infrastructure for comparing the results of two environment cuts. -/
private theorem sptWf_normalize {α : Type} (tree : Spt α) : sptWf (sptMkWf tree) = true := by
  induction tree with
  | ln => rfl
  | ls value => rfl
  | bn left right ihLeft ihRight =>
    simp only [sptMkWf]
    cases hleft : sptMkWf left <;> cases hright : sptMkWf right <;>
      simp_all [sptMkBN, sptWf, sptIsEmpty]
  | bs left value right ihLeft ihRight =>
    simp only [sptMkWf]
    cases hleft : sptMkWf left <;> cases hright : sptMkWf right <;>
      simp_all [sptMkBS, sptWf, sptIsEmpty]

/-- Two successful cuts equal a single cut by the intersection. -/
private theorem cutEnv_twice {α : Type} (first second : NumSet) (source middle result : Spt α)
    (firstCut : cutEnv first source = some middle)
    (secondCut : cutEnv second middle = some result) :
    cutEnv (sptInter first second) source = some result := by
  classical
  have middleLookup := DataLive.cutEnv_lookup first source middle firstCut
  have resultLookup := DataLive.cutEnv_lookup second middle result secondCut
  have present : ∀ key, sptMem key (sptInter first second) → sptMem key source := by
    intro key member
    have both := (DataLive.mem_inter first second key).1 member
    unfold cutEnv at firstCut
    split at firstCut
    · rename_i allPresent
      exact allPresent key both.1
    · simp at firstCut
  let target := sptMkWf (sptInter source (sptInter first second))
  have targetCut : cutEnv (sptInter first second) source = some target := by
    simp only [cutEnv, if_pos present]
    rfl
  have resultWf : sptWf result = true := by
    unfold cutEnv at secondCut
    split at secondCut
    · simp only [Option.some.injEq] at secondCut
      subst result
      exact sptWf_normalize _
    · simp at secondCut
  have targetWf : sptWf target = true := sptWf_normalize _
  have eq : result = target := by
    apply (sptEqThm result target ⟨resultWf, targetWf⟩).2
    intro key
    rw [resultLookup key, middleLookup key, DataLive.cutEnv_lookup (sptInter first second) source target targetCut key]
    by_cases a : sptMem key first <;> by_cases b : sptMem key second <;>
      simp [a, b, DataLive.mem_inter]
  simpa [← eq] using targetCut


/-- Cutting before a move keeps the source binding and yields an environment
whose moved result extends the original post-move cut. -/
private theorem cutEnv_before_move {α : Type} (source target : Spt α) (names : NumSet)
    (dest src : Nat) (value : α) (result : Spt α)
    (included : sptSubspt source target) (read : sptLookup src source = some value)
    (cut : cutEnv names (sptInsert dest value source) = some result) :
    ∃ before, cutEnv (sptInsert src () (sptDelete dest names)) target = some before ∧
      sptLookup src before = some value ∧ sptSubspt result (sptInsert dest value before) := by
  classical
  have postPresent : ∀ key, sptMem key names → sptMem key (sptInsert dest value source) := by
    unfold cutEnv at cut
    split at cut
    · assumption
    · simp at cut
  have targetRead : sptLookup src target = some value := (sptSubsptLookup _ _).1 included src value read
  let preNames := sptInsert src () (sptDelete dest names)
  have prePresent : ∀ key, sptMem key preNames → sptMem key target := by
    intro key member
    rcases (sptMem_sptInsert key src () _).1 member with same | rest
    · subst key
      simp [sptMem, sptDomain, targetRead]
    · have other : key ≠ dest := by
        intro same
        subst key
        simp [sptMem, sptDomain, sptLookup_sptDelete] at rest
      have post := postPresent key (by simpa [sptMem, sptDomain, sptLookup_sptDelete, other] using rest)
      have sourceMember : sptMem key source := by
        simpa [sptMem_sptInsert, other] using post
      exact (included key sourceMember).1
  let before := sptMkWf (sptInter target preNames)
  have beforeCut : cutEnv preNames target = some before := by
    simp only [cutEnv, if_pos prePresent]
    rfl
  have beforeRead : sptLookup src before = some value := by
    rw [DataLive.cutEnv_lookup preNames target before beforeCut src]
    have member : sptMem src preNames := (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    simp [member, targetRead]
  refine ⟨before, beforeCut, beforeRead, ?_⟩
  rw [sptSubsptLookup]
  intro key found resultRead
  by_cases same : key = dest
  · subst key
    rw [sptLookup_sptInsert_same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut dest] at resultRead
    by_cases member : sptMem dest names <;> simp [member, sptLookup_sptInsert_same] at resultRead
    exact congrArg some resultRead
  · rw [sptLookup_sptInsert_ne dest key value before same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut key] at resultRead
    by_cases member : sptMem key names
    · have preMember : sptMem key preNames := by
        apply (sptMem_sptInsert key src () _).2
        right
        simpa [sptMem, sptDomain, sptLookup_sptDelete, same] using member
      have sourceRead : sptLookup key source = some found := by
        simpa [member, sptLookup_sptInsert_ne dest key value source same] using resultRead
      have targetFound := (sptSubsptLookup _ _).1 included key found sourceRead
      rw [DataLive.cutEnv_lookup preNames target before beforeCut key]
      simp [preMember, targetFound]
    · simp [member] at resultRead


/-- A successful argument read is preserved by a cut retaining every
argument name. -/
private theorem getVars_after_cut {α : Type} (arguments : List Nat) (env cut : Spt α) (names : NumSet)
    (values : List α) (read : DataSem.getVars arguments env = some values)
    (cutRun : cutEnv names env = some cut) (kept : ∀ key ∈ arguments, sptMem key names) :
    DataSem.getVars arguments cut = some values := by
  induction arguments generalizing values with
  | nil => simpa [DataSem.getVars] using read
  | cons name arguments ih =>
    cases first : DataSem.getVar name env with
    | none => simp [DataSem.getVars, first] at read
    | some value =>
      cases rest : DataSem.getVars arguments env with
      | none => simp [DataSem.getVars, first, rest] at read
      | some tail =>
        have present : sptMem name names := kept name (by simp)
        have cutFirst : DataSem.getVar name cut = some value := by
          change sptLookup name env = some value at first
          simpa [DataSem.getVar, present, first] using DataLive.cutEnv_lookup names env cut cutRun name
        have cutRest := ih tail rest (by intro key member; exact kept key (by simp [member]))
        simp [DataSem.getVars, first, rest] at read
        subst values
        simp [DataSem.getVars, cutFirst, cutRest]

/-- Cutting before an assignment keeps all operand values and produces a
post-write environment extending the original post-assignment cut. -/
private theorem cutEnv_before_assign {α : Type} (source target : Spt α) (names : NumSet)
    (dest : Nat) (arguments : List Nat) (values : List α) (value : α) (result : Spt α)
    (included : sptSubspt source target) (read : DataSem.getVars arguments source = some values)
    (cut : cutEnv names (sptInsert dest value source) = some result) :
    ∃ before, cutEnv (sptListInsert arguments (sptDelete dest names)) target = some before ∧
      DataSem.getVars arguments before = some values ∧ sptSubspt result (sptInsert dest value before) := by
  classical
  have postPresent : ∀ key, sptMem key names → sptMem key (sptInsert dest value source) := by
    unfold cutEnv at cut
    split at cut
    · assumption
    · simp at cut
  have targetRead := getVars_of_subspt arguments source target values included read
  let preNames := sptListInsert arguments (sptDelete dest names)
  have prePresent : ∀ key, sptMem key preNames → sptMem key target := by
    intro key member
    rcases (DataLive.mem_listInsert arguments _ key).1 member with argument | rest
    · exact DataProps.getVars_imp_domain arguments key target values ⟨argument, targetRead⟩
    · have other : key ≠ dest := by
        intro same
        subst key
        simp [sptMem, sptDomain, sptLookup_sptDelete] at rest
      have post := postPresent key (by simpa [sptMem, sptDomain, sptLookup_sptDelete, other] using rest)
      have sourceMember : sptMem key source := by simpa [sptMem_sptInsert, other] using post
      exact (included key sourceMember).1
  let before := sptMkWf (sptInter target preNames)
  have beforeCut : cutEnv preNames target = some before := by
    simp only [cutEnv, if_pos prePresent]
    rfl
  have beforeRead : DataSem.getVars arguments before = some values :=
    getVars_after_cut arguments target before preNames values targetRead beforeCut
      (fun key member => (DataLive.mem_listInsert arguments _ key).2 (Or.inl member))
  refine ⟨before, beforeCut, beforeRead, ?_⟩
  rw [sptSubsptLookup]
  intro key found resultRead
  by_cases same : key = dest
  · subst key
    rw [sptLookup_sptInsert_same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut dest] at resultRead
    by_cases member : sptMem dest names <;> simp [member, sptLookup_sptInsert_same] at resultRead
    exact congrArg some resultRead
  · rw [sptLookup_sptInsert_ne dest key value before same]
    rw [DataLive.cutEnv_lookup names (sptInsert dest value source) result cut key] at resultRead
    by_cases member : sptMem key names
    · have preMember : sptMem key preNames := by
        apply (DataLive.mem_listInsert arguments _ key).2
        right
        simpa [sptMem, sptDomain, sptLookup_sptDelete, same] using member
      have sourceRead : sptLookup key source = some found := by
        simpa [member, sptLookup_sptInsert_ne dest key value source same] using resultRead
      have targetFound := (sptSubsptLookup _ _).1 included key found sourceRead
      rw [DataLive.cutEnv_lookup preNames target before beforeCut key]
      simp [preMember, targetFound]
    · simp [member] at resultRead

/-- An operation allowed without a live-name annotation does not reset
reserved space. This is auxiliary infrastructure for the hoisting proof. -/
private theorem noNames_noReset (op : ClosLang.Op) (valid : DataLang.opRequiresNames op = false) :
    DataLang.opSpaceReset op = false := by
  simp [DataLang.opRequiresNames] at valid
  exact valid.1

/-- Reserving an operation's requirement plus the subsequent reservation
leaves exactly the subsequent amount after a non-resetting space check. -/
private theorem doSpace_reserved {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (noReset : DataLang.opSpaceReset op = false) :
    doSpace op values { state with space := opSpaceReq op values.length + remaining } =
      some { state with space := remaining } := by
  by_cases zero : opSpaceReq op values.length = 0
  · simp [doSpace, noReset, zero]
  · have enough : ¬opSpaceReq op values.length + remaining < opSpaceReq op values.length := by omega
    simp [doSpace, noReset, zero, consumeSpace, enough]

/-- A successful operand read gives the operation requirement computed from
the argument names the same arity as that computed from the values. -/
private theorem read_requirement {α : Type} (names : List Nat) (env : Spt α) (values : List α)
    (op : ClosLang.Op) (read : DataSem.getVars names env = some values) :
    opSpaceReq op names.length = opSpaceReq op values.length := by
  rw [getVars_length names env values read]

/-- For non-resetting non-install operations, the hoisted reservation
feeds exactly the remaining space to the primitive dispatcher. -/
private theorem doApp_reserved {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (noReset : DataLang.opSpaceReset op = false)
    (notInstall : op ≠ .install) :
    doApp op values { state with space := opSpaceReq op values.length + remaining } =
      doAppAux op values (doStack op values (doLimSafe { state with space := remaining } op values)) := by
  have spaceRun := doSpace_reserved op values state remaining noReset
  cases op with
  | install => exact False.elim (notInstall rfl)
  | intOp intop =>
    cases intop <;> simp_all [doApp, DataLang.opSpaceReset]
  | label label => simp [doApp, spaceRun]
  | ffi name => simp [doApp, spaceRun]
  | wordOp wordop => simp [doApp, spaceRun]
  | blockOp blockop => simp [doApp, spaceRun]
  | globOp globop => simp [doApp, spaceRun]
  | memOp memop => simp [doApp, spaceRun]
  | thunkOp thunkop => simp [doApp, spaceRun]

/-- The reserved-space dispatcher equation for an operation valid in an
unannotated assignment. -/
private theorem doApp_reserved_unannotated {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (remaining : Nat) (valid : DataLang.opRequiresNames op = false) :
    doApp op values { state with space := opSpaceReq op values.length + remaining } =
      doAppAux op values (doStack op values (doLimSafe { state with space := remaining } op values)) := by
  have notInstall : op ≠ .install := by
    intro same
    subst op
    simp [DataLang.opRequiresNames] at valid
  exact doApp_reserved op values state remaining (noNames_noReset op valid) notInstall

/-- A successful non-resetting space check changes only the reserved amount. -/
private theorem doSpace_noNames_success {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state next : State C F)
    (valid : DataLang.opRequiresNames op = false) (run : doSpace op values state = some next) :
    next = { state with space := state.space - opSpaceReq op values.length } := by
  have noReset := noNames_noReset op valid
  by_cases zero : opSpaceReq op values.length = 0
  · simpa [doSpace, noReset, zero] using run.symm
  · by_cases enough : state.space < opSpaceReq op values.length
    · simp [doSpace, noReset, zero, consumeSpace, enough] at run
    · simpa [doSpace, noReset, zero, consumeSpace, enough] using run.symm

/-- On an unannotated operation, application first performs its space check
and then dispatches the primitive. -/
private theorem doApp_noNames {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (valid : DataLang.opRequiresNames op = false) :
    doApp op values state =
      match doSpace op values state with
      | none => .err (.abort .typeError)
      | some next => doAppAux op values (doStack op values (doLimSafe next op values)) := by
  cases op with
  | install => simp [DataLang.opRequiresNames] at valid
  | ffi name => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
  | intOp op => cases op <;> simp_all [doApp, DataLang.opRequiresNames, DataLang.opSpaceReset] <;> rfl
  | label label => rfl
  | wordOp op => rfl
  | blockOp op => rfl
  | globOp op => rfl
  | memOp op => rfl
  | thunkOp op => rfl

/-- If an unannotated primitive succeeds, supplying precisely its requirement
and extra reserved space gives the same value and state with that extra space. -/
private theorem doApp_success_with_reservation {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state after : State C F) (value : DataSem.Value)
    (extra : Nat) (valid : DataLang.opRequiresNames op = false)
    (run : doApp op values state = .val (value, after)) :
    doApp op values { state with space := opSpaceReq op values.length + extra } =
      .val (value, { after with space := extra }) := by
  rw [doApp_noNames op values state valid] at run
  cases spaceRun : doSpace op values state with
  | none => simp [spaceRun] at run
  | some next =>
    have shape := doSpace_noNames_success op values state next valid spaceRun
    subst next
    simp only [spaceRun] at run
    rw [doApp_reserved_unannotated op values state extra valid]
    have stackEq : doStack op values (doLimSafe { state with space := extra } op values) =
        { doStack op values (doLimSafe { state with space := state.space - opSpaceReq op values.length } op values) with space := extra } := by
      rfl
    rw [stackEq, doAppAux_withSpace op values _ extra, run]
    rfl

/-- An unannotated primitive cannot produce an FFI or other non-type error. -/
private theorem doApp_noNames_error {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (error : ErrorResult DataSem.Value)
    (valid : DataLang.opRequiresNames op = false) (run : doApp op values state = .err error) :
    error = .abort .typeError := by
  rcases DataProps.doApp_err op values state error run with typeError | ⟨name, outcome, eq, _⟩
  · exact typeError
  · subst op
    simp [DataLang.opRequiresNames] at valid

private theorem mergeReservations {C F : Type} (amount1 amount2 : Nat) (names1 names2 : NumSet)
    (body : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : evaluate (.seq (.makeSpace amount1 names1) (.seq (.makeSpace amount2 names2) body)) state = (result, next)) :
    ∃ safe peak stackMax,
      evaluate (.seq (.makeSpace amount2 (sptInter names1 names2)) body) state =
        (result, { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
  cases cut1 : cutEnv names1 state.locals with
  | none =>
    simp [DataSem.evaluate, fixClock, cut1, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some env1 =>
    cases cut2 : cutEnv names2 env1 with
    | none =>
      simp [DataSem.evaluate, fixClock, cut1, cut2, addSpace, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some env2 =>
      have combined := cutEnv_twice names1 names2 state.locals env1 env2 cut1 cut2
      rw [DataSem.evaluate, fixClock_evaluate] at run
      have eval1 : evaluate (.makeSpace amount1 names1) state =
          (none, addSpace { state with locals := env1 } amount1) := by simp [DataSem.evaluate, cut1]
      rw [eval1] at run
      simp only at run
      rw [DataSem.evaluate, fixClock_evaluate] at run
      have eval2 : evaluate (.makeSpace amount2 names2)
          (addSpace { state with locals := env1 } amount1) =
          (none, addSpace { addSpace { state with locals := env1 } amount1 with locals := env2 } amount2) := by
        have localEq : (addSpace { state with locals := env1 } amount1).locals = env1 := rfl
        simp only [DataSem.evaluate, localEq, cut2]
      rw [eval2] at run
      simp only at run
      rw [DataSem.evaluate, fixClock_evaluate]
      have evalCombined : evaluate (.makeSpace amount2 (sptInter names1 names2)) state =
          (none, addSpace { state with locals := env2 } amount2) := by simp [DataSem.evaluate, combined]
      rw [evalCombined]
      simp only
      let twice := addSpace { addSpace { state with locals := env1 } amount1 with locals := env2 } amount2
      let once := addSpace { state with locals := env2 } amount2
      change evaluate body twice = (result, next) at run
      change ∃ safe peak stackMax, evaluate body once =
        (result, { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax })
      have same : once = { twice with safeForSpace := once.safeForSpace, peakHeapLength := once.peakHeapLength, stackMax := once.stackMax } := by
        rfl
      obtain ⟨mx, safe, peak, transported⟩ :=
        evaluate_stackSafePeakSwap once.stackMax once.safeForSpace next twice result once.peakHeapLength body run
      exact ⟨safe, peak, mx, by simpa [← same] using transported⟩

private theorem moveReservation {C F : Type} (dest src amount : Nat) (names : NumSet)
    (body : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : evaluate (.seq (.move dest src) (.seq (.makeSpace amount names) body)) state = (result, next)) :
    ∃ out safe peak stackMax,
      evaluate (.seq (.makeSpace amount (sptInsert src () (sptDelete dest names))) (.seq (.move dest src) body)) state =
        (result, if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt next.locals out := by
  cases read : getVar src state.locals with
  | none =>
    simp [DataSem.evaluate, fixClock, read, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    cases cut : cutEnv names (sptInsert dest value state.locals) with
    | none =>
      simp [DataSem.evaluate, fixClock, read, cut, setVar, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some env =>
      have found : sptLookup src state.locals = some value := read
      obtain ⟨before, cutBefore, readBefore, enlarged⟩ :=
        cutEnv_before_move state.locals state.locals names dest src value env (localsOk_refl _) found cut
      have moveRun : evaluate (.move dest src) state = (none, setVar dest value state) := by
        simp [DataSem.evaluate, read]
      rw [DataSem.evaluate, fixClock_evaluate, moveRun] at run
      simp only at run
      rw [DataSem.evaluate, fixClock_evaluate] at run
      have spaceRun : evaluate (.makeSpace amount names) (setVar dest value state) =
          (none, addSpace { setVar dest value state with locals := env } amount) := by
        simp only [DataSem.evaluate, setVar, cut]
      rw [spaceRun] at run
      simp only at run
      rw [DataSem.evaluate, fixClock_evaluate]
      have spaceBefore : evaluate (.makeSpace amount (sptInsert src () (sptDelete dest names))) state =
          (none, addSpace { state with locals := before } amount) := by
        simp [DataSem.evaluate, cutBefore]
      rw [spaceBefore]
      simp only
      rw [DataSem.evaluate, fixClock_evaluate]
      have movedBefore : evaluate (.move dest src) (addSpace { state with locals := before } amount) =
          (none, setVar dest value (addSpace { state with locals := before } amount)) := by
        simp [DataSem.evaluate, DataSem.getVar, readBefore, addSpace]
      rw [movedBefore]
      simp only
      let old := addSpace { setVar dest value state with locals := env } amount
      let moved := setVar dest value (addSpace { state with locals := before } amount)
      let larger := sptInsert dest value before
      change evaluate body old = (result, next) at run
      change ∃ out safe peak stackMax, evaluate body moved =
          (result, if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
            else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
        sptSubspt next.locals out
      obtain ⟨out, safe, peak, mx, enlargedRun, included⟩ :=
        evaluate_locals body old result next () larger notType run enlarged
      let base := { old with locals := larger }
      have same : moved = { base with safeForSpace := moved.safeForSpace, peakHeapLength := moved.peakHeapLength, stackMax := moved.stackMax } := by
        rfl
      obtain ⟨mx2, safe2, peak2, transported⟩ := evaluate_stackSafePeakSwap moved.stackMax moved.safeForSpace
        (if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
          else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := mx })
        base result moved.peakHeapLength body enlargedRun
      refine ⟨out, safe2, peak2, mx2, ?_, included⟩
      cases result <;> simpa [← same] using transported

private theorem assignReservation {C F : Type} (dest : Nat) (op : ClosLang.Op) (arguments : List Nat)
    (amount : Nat) (names : NumSet) (body : DataLang.Prog) (state next : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value))
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : evaluate (.seq (.assign dest op arguments none) (.seq (.makeSpace amount names) body)) state = (result, next)) :
    ∃ out safe peak stackMax,
      evaluate (.seq (.makeSpace (opSpaceReq op arguments.length + amount) (sptListInsert arguments (sptDelete dest names)))
        (.seq (.assign dest op arguments none) body)) state =
        (result, if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt next.locals out := by
  by_cases valid : DataLang.opRequiresNames op = false
  · cases read : DataSem.getVars arguments state.locals with
    | none =>
      simp [DataSem.evaluate, valid, read, fixClock, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some values =>
      cases app : doApp op values state with
      | err error =>
        have errorEq := doApp_noNames_error op values state error valid app
        subst error
        simp [DataSem.evaluate, valid, read, cutStateOpt, app, fixClock] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | val pair =>
        obtain ⟨value, applied⟩ := pair
        have control := doApp_control op values state applied value app
        let assigned := setVar dest value (installSfs op applied)
        have assignRun : evaluate (.assign dest op arguments none) state = (none, assigned) := by
          simp [DataSem.evaluate, valid, read, cutStateOpt, app, assigned]
        rw [DataSem.evaluate, fixClock_evaluate, assignRun] at run
        simp only at run
        cases cut : cutEnv names assigned.locals with
        | none =>
          simp [DataSem.evaluate, fixClock, cut, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some resultEnv =>
          have sourceCut : cutEnv names (sptInsert dest value state.locals) = some resultEnv := by
            simpa [assigned, setVar, installSfs, control.1] using cut
          obtain ⟨before, beforeCut, beforeRead, afterIncluded⟩ :=
            cutEnv_before_assign state.locals state.locals names dest arguments values value resultEnv (localsOk_refl _) read sourceCut
          rw [DataSem.evaluate, fixClock_evaluate] at run
          have spaceRun : evaluate (.makeSpace amount names) assigned =
              (none, addSpace { assigned with locals := resultEnv } amount) := by
            simp [DataSem.evaluate, cut]
          rw [spaceRun] at run
          simp only at run
          let requirement := opSpaceReq op values.length
          let reserved := { state with space := requirement + amount }
          let targetMid := addSpace { state with locals := before } (requirement + amount)
          have reservedApp : doApp op values reserved = .val (value, { applied with space := amount }) := by
            exact doApp_success_with_reservation op values state applied value amount valid app
          have related : DataLive.stateRel reserved targetMid .ln := by
            simp [DataLive.stateRel, reserved, targetMid, addSpace, sptMem, sptDomain, sptLookup]
          obtain ⟨targetApplied, targetApp, appRel⟩ :=
            DataLive.stateRel_doApp_success reserved targetMid { applied with space := amount } .ln op values value related reservedApp
          have targetControl := doApp_control op values targetMid targetApplied value targetApp
          have stateEq : targetApplied = { applied with locals := before, space := amount, safeForSpace := targetApplied.safeForSpace, peakHeapLength := targetApplied.peakHeapLength, stackMax := targetApplied.stackMax } := by
            rcases appRel with ⟨code, clock, spaceEq, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
            cases applied
            cases targetApplied
            simp_all [targetMid, addSpace]
          let targetNext := setVar dest value (installSfs op targetApplied)
          have reqEq := read_requirement arguments state.locals values op read
          have reserveRun : evaluate (.makeSpace (opSpaceReq op arguments.length + amount)
              (sptListInsert arguments (sptDelete dest names))) state = (none, targetMid) := by
            simp [DataSem.evaluate, beforeCut, targetMid, requirement, reqEq]
          rw [DataSem.evaluate, fixClock_evaluate, reserveRun]
          simp only
          rw [DataSem.evaluate, fixClock_evaluate]
          have targetRead : DataSem.getVars arguments targetMid.locals = some values := by
            simpa [targetMid, addSpace] using beforeRead
          have targetRun : evaluate (.assign dest op arguments none) targetMid = (none, targetNext) := by
            simp [DataSem.evaluate, valid, targetRead, cutStateOpt, targetApp, targetNext]
          rw [targetRun]
          simp only
          let old := addSpace { assigned with locals := resultEnv } amount
          let larger := sptInsert dest value before
          change evaluate body old = (result, next) at run
          change ∃ out safe peak stackMax, evaluate body targetNext =
              (result, if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
                else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
            sptSubspt next.locals out
          obtain ⟨out, safe, peak, mx, enlargedRun, included⟩ :=
            evaluate_locals body old result next () larger notType run afterIncluded
          let base := { old with locals := larger }
          have same : targetNext = { base with safeForSpace := targetNext.safeForSpace, peakHeapLength := targetNext.peakHeapLength, stackMax := targetNext.stackMax } := by
            dsimp only [targetNext]
            rw [stateEq]
            simp [base, old, larger, assigned, setVar, installSfs, addSpace]
          obtain ⟨mx2, safe2, peak2, transported⟩ := evaluate_stackSafePeakSwap targetNext.stackMax targetNext.safeForSpace
            (if result = none then { next with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
              else { next with safeForSpace := safe, peakHeapLength := peak, stackMax := mx })
            base result targetNext.peakHeapLength body enlargedRun
          refine ⟨out, safe2, peak2, mx2, ?_, included⟩
          cases result <;> simpa [← same] using transported
  · have invalid : DataLang.opRequiresNames op = true := by cases h : DataLang.opRequiresNames op <;> simp_all
    simp [DataSem.evaluate, invalid, fixClock, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)

private theorem seqCase {C F : Type} (first second : DataLang.Prog)
    (firstIH : simulationFor (C := C) (F := F) first)
    (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq first second) := by
  intro source sourceNext result locals notType run included
  have ordinary := composeSimulation first second firstIH secondIH source sourceNext result locals notType run included
  cases first <;> cases found : space second <;>
    try { simpa [compile, space, pMakeSpace, found] using ordinary }
  case skip.inl | skip.inr =>
    have sourceRun : DataSem.evaluate second source = (result, sourceNext) := by
      simpa [DataSem.evaluate, fixClock] using run
    have target := secondIH source sourceNext result locals notType sourceRun included
    simpa [compileSeqSkip] using target
  case assign.inr =>
    rename_i dest op arguments live payload
    obtain ⟨amount, names, body⟩ := payload
    cases live with
    | some live =>
      simpa [compile, space, pMakeSpace, found] using ordinary
    | none =>
      obtain ⟨out, safe, peak, mx, targetRun, final⟩ := ordinary
      have nested : evaluate (.seq (.assign dest op arguments none) (.seq (.makeSpace amount names) body))
          { source with locals := locals } =
            (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
              else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) := by
        simpa [compile, space, pMakeSpace, found] using targetRun
      obtain ⟨out2, safe2, peak2, mx2, moved, final2⟩ := assignReservation dest op arguments amount names body
        { source with locals := locals }
        (if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) result notType nested
      refine ⟨out2, safe2, peak2, mx2, ?_, ?_⟩
      · cases result <;> simpa [compile, space, pMakeSpace, found] using moved
      · cases result with
        | none => exact sptSubsptTrans _ _ _ ⟨final, by simpa using final2⟩
        | some outcome => simpa using final2
  case move.inr =>
    rename_i dest src payload
    obtain ⟨amount, names, body⟩ := payload
    obtain ⟨out, safe, peak, mx, targetRun, final⟩ := ordinary
    have nested : evaluate (.seq (.move dest src) (.seq (.makeSpace amount names) body))
        { source with locals := locals } =
          (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
            else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) := by
      simpa [compile, space, pMakeSpace, found] using targetRun
    obtain ⟨out2, safe2, peak2, mx2, moved, final2⟩ := moveReservation dest src amount names body
      { source with locals := locals }
      (if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
        else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) result notType nested
    refine ⟨out2, safe2, peak2, mx2, ?_, ?_⟩
    · cases result <;> simpa [compile, space, pMakeSpace, found] using moved
    · cases result with
      | none => exact sptSubsptTrans _ _ _ ⟨final, by simpa using final2⟩
      | some outcome => simpa using final2
  case makeSpace.inl =>
    simpa [compile, space, pMakeSpace, found, evalSeqSkipAssoc] using ordinary
  case makeSpace.inr =>
    rename_i amount1 names1 payload
    obtain ⟨amount2, names2, body⟩ := payload
    obtain ⟨out, safe, peak, mx, targetRun, final⟩ := ordinary
    have nested : evaluate (.seq (.makeSpace amount1 names1) (.seq (.makeSpace amount2 names2) body))
        { source with locals := locals } =
          (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
            else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) := by
      simpa [compile, space, pMakeSpace, found, evalSeqSkipAssoc] using targetRun
    obtain ⟨safe2, peak2, mx2, merged⟩ := mergeReservations amount1 amount2 names1 names2 body
      { source with locals := locals }
      (if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := mx }
        else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := mx }) result notType nested
    refine ⟨out, safe2, peak2, mx2, ?_, final⟩
    cases result <;> simpa [compile, space, pMakeSpace, found] using merged

private theorem simulationFor_all {C F : Type} (program : DataLang.Prog) :
    simulationFor (C := C) (F := F) program := by
  have allSizes : ∀ weight : Nat, ∀ program : DataLang.Prog,
      sizeOf program = weight → simulationFor (C := C) (F := F) program := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro program measure
      cases program with
      | skip => exact simulationFor_skip
      | move dest src => exact simulationFor_move dest src
      | assign dest op arguments names => exact simulationFor_assign dest op arguments names
      | tick => exact simulationFor_tick
      | makeSpace amount names => exact simulationFor_makeSpace amount names
      | raise name => exact simulationFor_raise name
      | «return» names => exact simulationFor_return names
      | seq first second =>
        apply seqCase first second
        · apply ih (sizeOf first) ?_ first rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf second) ?_ second rfl
          simp only [DataLang.Prog.seq.sizeOf_spec] at measure
          omega
      | ifThenElse name yes no =>
        apply simulationFor_if name yes no
        · apply ih (sizeOf yes) ?_ yes rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
        · apply ih (sizeOf no) ?_ no rfl
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
          omega
      | force ret label src => exact simulationFor_force ret label src
      | call ret dest arguments handler => exact simulationFor_call ret dest arguments handler
  exact allSizes (sizeOf program) program rfl

/-- Evaluation of the reservation pass preserves non-type-error results,
allowing only local extension on continuation and the original resource updates. -/
@[hol "cakeml/compiler/backend/proofs/data_spaceProofScript.sml" "evaluate_compile"]
theorem evaluate_compile {C F V : Type} (program : DataLang.Prog) (source : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (sourceNext : State C F)
    (_vars : V) (locals : Spt DataSem.Value)
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : evaluate program source = (result, sourceNext))
    (included : localsOk source.locals locals) :
    ∃ out safe peak stackMax,
      evaluate (compile program) { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      localsOk sourceNext.locals out :=
  simulationFor_all program source sourceNext result locals notType run included

/-- Stopped non-type-error evaluation is preserved by reservation compilation. -/
@[hol "cakeml/compiler/backend/proofs/data_spaceProofScript.sml" "compile_correct"]
theorem compile_correct {C F : Type} (program : DataLang.Prog) (source : State C F)
    (stopped : (evaluate program source).1 ≠ none)
    (notType : (evaluate program source).1 ≠ some (.err (.abort .typeError))) :
    ∃ safe peak stackMax,
      evaluate (compile program) source =
        ((evaluate program source).1, { (evaluate program source).2 with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
  cases run : evaluate program source with
  | mk result sourceNext =>
    cases result with
    | none => simp [run] at stopped
    | some outcome =>
      have allowed : some outcome ≠ some (.err (.abort .typeError)) := by simpa [run] using notType
      obtain ⟨out, safe, peak, stackMax, target, _⟩ :=
        evaluate_compile program source (some outcome) sourceNext () source.locals allowed run (localsOk_refl _)
      refine ⟨safe, peak, stackMax, ?_⟩
      simpa [run] using target

end Flapjack.Compiler.Backend.DataSpace
