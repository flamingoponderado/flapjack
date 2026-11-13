module

public import Flapjack.Compiler.Backend.BviToData.Proofs.State
public import Flapjack.Compiler.Backend.BviToData.Proofs.Apply
public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

@[expose] public section

/-! Space and stack bookkeeping for primitive-operation simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Reserving space changes no component observed by the BVI-to-data state
relation. This is pass-specific infrastructure for assignment simulation. -/
theorem stateRel_addSpace {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (amount : Nat) (related : stateRel source target) :
    stateRel source (DataSem.addSpace target amount) := by
  simpa [stateRel, DataSem.addSpace] using related

/-- Updating limit safety does not affect the related BVI state. -/
theorem stateRel_doLimSafe {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (op : ClosLang.Op) (values : List DataSem.Value)
    (related : stateRel source target) : stateRel source (DataSem.doLimSafe target op values) := by
  simpa [stateRel, DataSem.doLimSafe] using related

/-- Stack-usage bookkeeping leaves the components of the state relation
unchanged. -/
theorem stateRel_doStack {C F : Type} (source : BviSem.BviState C F)
    (target : DataSem.State C F) (op : ClosLang.Op) (values : List DataSem.Value)
    (related : stateRel source target) : stateRel source (DataSem.doStack op values target) := by
  simpa [stateRel, DataSem.doStack] using related

/-- Space accounting succeeds whenever the reserved space covers its static
requirement. Operations that reset their space do not require that reserve. -/
theorem doSpace_succeeds {C F : Type} (target : DataSem.State C F) (op : ClosLang.Op)
    (values : List DataSem.Value)
    (enough : DataLang.opSpaceReset op = true ∨ DataSpace.opSpaceReq op values.length ≤ target.space) :
    ∃ next, DataSem.doSpace op values target = some next := by
  unfold DataSem.doSpace
  split
  · exact ⟨_, rfl⟩
  · rename_i notReset
    have reserved := enough.resolve_left notReset
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · simp [DataSem.consumeSpace, Nat.not_lt_of_ge reserved]

/-- Successful space accounting preserves the state relation and the local
and stack fields consumed by assignment and exception simulation. -/
theorem stateRel_doSpace {C F : Type} (source : BviSem.BviState C F)
    (target next : DataSem.State C F) (op : ClosLang.Op) (values : List DataSem.Value)
    (related : stateRel source target) (run : DataSem.doSpace op values target = some next) :
    stateRel source next ∧ next.locals = target.locals ∧ next.stack = target.stack ∧
      next.handler = target.handler ∧ next.localsSize = target.localsSize ∧
      next.stackFrameSizes = target.stackFrameSizes := by
  unfold DataSem.doSpace at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    simpa [stateRel] using related
  · dsimp only at run
    split at run
    · simp only [Option.some.injEq] at run
      subst next
      exact ⟨related, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [DataSem.consumeSpace] at run
      split at run
      · simp at run
      · simp only [Option.some.injEq] at run
        subst next
        simpa [stateRel] using related

/-- Once space accounting succeeds, a non-install operation accepted by the
full dispatcher delegates to the auxiliary operation at its accounted state. -/
theorem doApp_of_aux {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (target accounted next : DataSem.State C F) (value : DataSem.Value)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (space : DataSem.doSpace op values target = some accounted)
    (aux : DataSem.doAppAux op values (DataSem.doStack op values (DataSem.doLimSafe accounted op values)) =
      .val (value, next)) :
    DataSem.doApp op values target = .val (value, next) := by
  cases op with
  | install => exact False.elim (notInstall rfl)
  | intOp op =>
    cases op <;> simp_all [DataSem.doApp]
  | label _ | ffi _ | wordOp _ | blockOp _ | globOp _ | memOp _ | thunkOp _ =>
    simpa [DataSem.doApp, space] using aux

/-- A successful supported BVI primitive has a corresponding result from
the full data dispatcher when its space reservation is sufficient. This is
pass infrastructure; the remaining operation rewrites and FFI abort path are
handled separately by the full compiler proof. -/
theorem doApp_full_projection {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (args : List DataSem.Value) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (related : stateRel source target)
    (enough : DataLang.opSpaceReset op = true ∨ DataSpace.opSpaceReq op args.length ≤ target.space)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doApp op args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  obtain ⟨accounted, space⟩ := doSpace_succeeds target op args enough
  have accountedRel := (stateRel_doSpace source target accounted op args related space).1
  have safeRel := stateRel_doLimSafe source accounted op args accountedRel
  have stackRel := stateRel_doStack source (DataSem.doLimSafe accounted op args) op args safeRel
  obtain ⟨targetNext, value, aux, projected, finalRel⟩ :=
    doApp_projection op _ source args result next notInstall notGreater notGreaterEq notWordGt notWordGeq
      notForce stackRel run
  exact ⟨targetNext, value, doApp_of_aux op args target accounted targetNext value notInstall notGreater
    notGreaterEq space aux, projected, finalRel⟩

/-- A make-space instruction cuts the locals to its live names and reserves
the requested space when those names are present. -/
theorem evaluate_makeSpace_names {C F : Type} (target : DataSem.State C F)
    (names : List Nat) (amount : Nat)
    (present : ∀ key ∈ names, sptLookup key target.locals ≠ none) :
    DataSem.evaluate (.makeSpace amount (namesOfList names)) target =
      (none, DataSem.addSpace { target with locals := sptMkWf (sptInter target.locals (namesOfList names)) } amount) := by
  simp [DataSem.evaluate, cutEnv_namesOfList names target.locals present]

/-- After the compiler's make-space prelude, a supported successful BVI
primitive is simulated by the complete data dispatcher. Its explicit list
of roots must be present in the initial local environment. -/
theorem doApp_full_after_makeSpace {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (names : List Nat) (args : List DataSem.Value) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (related : stateRel source target)
    (present : ∀ key ∈ names, sptLookup key target.locals ≠ none)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    let cut := { target with locals := sptMkWf (sptInter target.locals (namesOfList names)) }
    let reserved := DataSem.addSpace cut (DataSpace.opSpaceReq op args.length)
    DataSem.evaluate (.makeSpace (DataSpace.opSpaceReq op args.length) (namesOfList names)) target = (none, reserved) ∧
    ∃ targetNext value, DataSem.doApp op args reserved = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext := by
  dsimp only
  refine ⟨evaluate_makeSpace_names target names _ present, ?_⟩
  have cutRel : stateRel source { target with locals := sptMkWf (sptInter target.locals (namesOfList names)) } := by
    simpa [stateRel] using related
  have reservedRel := stateRel_addSpace source _ (DataSpace.opSpaceReq op args.length) cutRel
  apply doApp_full_projection op _ source args result next notInstall notGreater notGreaterEq notWordGt notWordGeq
    notForce reservedRel
  · right
    simp [DataSem.addSpace]
  · exact run

/-- Execute the make-space and assignment sequence used for supported
non-live-name operations. The operands are read from the cut environment,
and the assigned result projects to the BVI primitive result. -/
theorem evaluate_makeSpace_assign {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (roots operands : List Nat) (args : List DataSem.Value) (dest : Nat)
    (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (noLiveNames : DataLang.opRequiresNames op = false)
    (related : stateRel source target)
    (present : ∀ key ∈ roots, sptLookup key target.locals ≠ none)
    (included : ∀ key ∈ operands, key ∈ roots)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (.seq (.makeSpace (DataSpace.opSpaceReq op args.length) (namesOfList roots))
        (.assign dest op operands none)) target =
          (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  let cut := { target with locals := sptMkWf (sptInter target.locals (namesOfList roots)) }
  let reserved := DataSem.addSpace cut (DataSpace.opSpaceReq op args.length)
  have prelude : DataSem.evaluate (.makeSpace (DataSpace.opSpaceReq op args.length) (namesOfList roots)) target =
      (none, reserved) := evaluate_makeSpace_names target roots _ present
  have readCut : DataSem.getVars operands reserved.locals = some args := by
    simpa [reserved, cut, DataSem.addSpace] using getVars_cut_exact roots target.locals operands args read included
  obtain ⟨_, targetNext, value, app, projected, finalRel⟩ :=
    doApp_full_after_makeSpace op target source roots args result next notInstall notGreater notGreaterEq
      notWordGt notWordGeq notForce related present run
  have assignment : DataSem.evaluate (.assign dest op operands none) reserved =
      (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
    simp [DataSem.evaluate, noLiveNames, readCut, DataSem.cutStateOpt, app, reserved, cut]
  refine ⟨targetNext, value, ?_, projected, ?_⟩
  · rw [DataSem.evaluate, prelude]
    simpa [DataSem.fixClock, reserved, cut, DataSem.addSpace] using assignment
  · simpa [stateRel, DataSem.setVar, DataSem.installSfs] using finalRel

/-- The actual `iAssign` make-space branch simulates a successful supported
primitive. Operand reads, live locals, and the current environment establish
that all compiler-selected roots are present. -/
theorem evaluate_iAssign_makeSpace {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (noLiveNames : DataLang.opRequiresNames op = false)
    (needsSpace : DataSpace.opSpaceReq op operands.length ≠ 0)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest op operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  have operandPresent := getVars_present operands target.locals args read
  have corrRead := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresentMapped := getVars_present corr (sptMap dataToBviValue target.locals) env corrRead
  have corrPresent : ∀ key ∈ corr, sptLookup key target.locals ≠ none := by
    intro key member absent
    have mapped := corrPresentMapped key member
    apply mapped
    simp [sptLookup_sptMap, absent]
  have rootsPresent : ∀ key ∈ operands ++ live ++ corr, sptLookup key target.locals ≠ none := by
    intro key member
    simp only [List.mem_append] at member
    rcases member with operandOrLive | corrMember
    · rcases operandOrLive with operand | liveMember
      · exact operandPresent key operand
      · exact livePresent key liveMember
    · exact corrPresent key corrMember
  have length := DataSpace.getVars_length operands target.locals args read
  have shape : iAssign dest op operands live corr =
      .seq (.makeSpace (DataSpace.opSpaceReq op args.length) (namesOfList (operands ++ live ++ corr)))
        (.assign dest op operands none) := by
    simp [iAssign, noLiveNames, needsSpace, length]
  rw [shape]
  exact evaluate_makeSpace_assign op target source (operands ++ live ++ corr) operands args dest result next
    notInstall notGreater notGreaterEq notWordGt notWordGeq notForce noLiveNames related rootsPresent
    (by intro key member; simp [member]) read run

private theorem iAssign_noSpace_shape (op : ClosLang.Op) (dest : Nat) (operands live corr : List Nat)
    (noLiveNames : DataLang.opRequiresNames op = false)
    (noSpace : DataSpace.opSpaceReq op operands.length = 0)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq))) :
    iAssign dest op operands live corr = .assign dest op operands none := by
  simp only [iAssign, noLiveNames, Bool.false_eq_true, if_false, noSpace, if_true]

/-- The direct `iAssign` branch simulates a successful supported primitive
when it needs neither a live-name cut nor a space reservation. -/
theorem evaluate_iAssign_noSpace {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (args : List DataSem.Value) (dest : Nat)
    (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (noLiveNames : DataLang.opRequiresNames op = false)
    (noSpace : DataSpace.opSpaceReq op operands.length = 0)
    (related : stateRel source target)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest op operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  have length := DataSpace.getVars_length operands target.locals args read
  have enough : DataLang.opSpaceReset op = true ∨ DataSpace.opSpaceReq op args.length ≤ target.space := by
    right
    simp [length, noSpace]
  obtain ⟨targetNext, value, app, projected, finalRel⟩ :=
    doApp_full_projection op target source args result next notInstall notGreater notGreaterEq notWordGt notWordGeq
      notForce related enough run
  refine ⟨targetNext, value, ?_, projected, ?_⟩
  · rw [iAssign_noSpace_shape op dest operands live corr noLiveNames noSpace notWordGt notWordGeq]
    simp [DataSem.evaluate, noLiveNames, read, DataSem.cutStateOpt, app]
  · simpa [stateRel, DataSem.setVar, DataSem.installSfs] using finalRel

/-- Successful supported operations that do not require live names are
simulated by the compiler's actual `iAssign`, whether or not space is needed. -/
theorem evaluate_iAssign_noLiveNames {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (noLiveNames : DataLang.opRequiresNames op = false)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest op operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  by_cases noSpace : DataSpace.opSpaceReq op operands.length = 0
  · exact evaluate_iAssign_noSpace op target source operands live corr args dest result next notInstall
      notGreater notGreaterEq notWordGt notWordGeq notForce noLiveNames noSpace related read run
  · exact evaluate_iAssign_makeSpace op target source operands live corr env args dest result next notInstall
      notGreater notGreaterEq notWordGt notWordGeq notForce noLiveNames noSpace related vars livePresent read run

private theorem requiresNames_space (op : ClosLang.Op) (count : Nat)
    (requires : DataLang.opRequiresNames op = true) :
    DataLang.opSpaceReset op = true ∨ DataSpace.opSpaceReq op count = 0 := by
  cases op <;> simp_all [DataLang.opRequiresNames, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case memOp op => cases op <;> simp_all

private theorem iAssign_live_shape (op : ClosLang.Op) (dest : Nat) (operands live corr : List Nat)
    (requires : DataLang.opRequiresNames op = true)
    (notGreater : op ≠ .intOp .greater) (notGreaterEq : op ≠ .intOp .greaterEq) :
    iAssign dest op operands live corr = .assign dest op operands (some (namesOfList (operands ++ live ++ corr))) := by
  simp only [iAssign, requires, if_true]

/-- The live-name `iAssign` branch simulates a successful supported
primitive after cutting the target environment to the compiler's roots. -/
theorem evaluate_iAssign_liveNames {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (requires : DataLang.opRequiresNames op = true)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest op operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  let roots := operands ++ live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  let prepared := { target with locals := cut }
  have operandPresent := getVars_present operands target.locals args read
  have corrRead := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresentMapped := getVars_present corr (sptMap dataToBviValue target.locals) env corrRead
  have corrPresent : ∀ key ∈ corr, sptLookup key target.locals ≠ none := by
    intro key member absent
    have mapped := corrPresentMapped key member
    apply mapped
    simp [sptLookup_sptMap, absent]
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none := by
    intro key member
    simp only [roots, List.mem_append] at member
    rcases member with operandOrLive | corrMember
    · rcases operandOrLive with operand | liveMember
      · exact operandPresent key operand
      · exact livePresent key liveMember
    · exact corrPresent key corrMember
  have cutRel : stateRel source prepared := by simpa [prepared, stateRel] using related
  have enough : DataLang.opSpaceReset op = true ∨ DataSpace.opSpaceReq op args.length ≤ prepared.space := by
    rcases requiresNames_space op args.length requires with resets | zero
    · exact Or.inl resets
    · exact Or.inr (by simp [zero])
  obtain ⟨targetNext, value, app, projected, finalRel⟩ :=
    doApp_full_projection op prepared source args result next notInstall notGreater notGreaterEq notWordGt notWordGeq
      notForce cutRel enough run
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut := by
    exact cutEnv_namesOfList roots target.locals rootsPresent
  refine ⟨targetNext, value, ?_, projected, ?_⟩
  · rw [iAssign_live_shape op dest operands live corr requires notGreater notGreaterEq]
    simpa [roots, prepared] using (show DataSem.evaluate (.assign dest op operands (some (namesOfList roots))) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) by
      simp [DataSem.evaluate, requires, read, DataSem.cutStateOpt, DataSem.cutState, cutEnv, app, prepared])
  · simpa [stateRel, DataSem.setVar, DataSem.installSfs] using finalRel

/-- A resetting primitive assignment succeeds with any present root list.
This form permits compiler rewrites that reorder operands while keeping the
original live-name tree. -/
theorem evaluate_assign_reset {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (roots operands : List Nat) (args : List DataSem.Value) (dest : Nat)
    (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (resets : DataLang.opSpaceReset op = true) (related : stateRel source target)
    (present : ∀ key ∈ roots, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (.assign dest op operands (some (namesOfList roots))) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  let prepared := { target with locals := cut }
  have cutRel : stateRel source prepared := by simpa [prepared, stateRel] using related
  obtain ⟨targetNext, value, app, projected, finalRel⟩ :=
    doApp_full_projection op prepared source args result next notInstall notGreater notGreaterEq notWordGt notWordGeq
      notForce cutRel (Or.inl resets) run
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals present
  have requires : DataLang.opRequiresNames op = true := by simp [DataLang.opRequiresNames, resets]
  refine ⟨targetNext, value, ?_, projected, ?_⟩
  · simp [DataSem.evaluate, requires, read, DataSem.cutStateOpt, DataSem.cutState, cutEnv, app, prepared]
  · simpa [stateRel, DataSem.setVar, DataSem.installSfs] using finalRel

/-- The compiler's complete `iAssign` structure simulates a successful
primitive, under the restrictions of the auxiliary primitive theorem. The
special operation rewrites and terminal FFI result remain separate cases. -/
theorem evaluate_iAssign_supported {C F : Type} (op : ClosLang.Op)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (notInstall : op ≠ .install) (notGreater : op ≠ .intOp .greater)
    (notGreaterEq : op ≠ .intOp .greaterEq)
    (notWordGt : op ≠ .wordOp (.wordTest .w8 (.compare .gt)))
    (notWordGeq : op ≠ .wordOp (.wordTest .w8 (.compare .geq)))
    (notForce : op ≠ .thunkOp .forceThunk)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp op (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest op operands live corr) target =
        (none, DataSem.setVar dest value (DataSem.installSfs op targetNext)) ∧
      result = dataToBviValue value ∧ stateRel next (DataSem.setVar dest value (DataSem.installSfs op targetNext)) := by
  cases requires : DataLang.opRequiresNames op with
  | false =>
    exact evaluate_iAssign_noLiveNames op target source operands live corr env args dest result next notInstall
      notGreater notGreaterEq notWordGt notWordGeq notForce requires related vars livePresent read run
  | true =>
    exact evaluate_iAssign_liveNames op target source operands live corr env args dest result next notInstall
      notGreater notGreaterEq notWordGt notWordGeq notForce requires related vars livePresent read run

end Flapjack.Compiler.Backend.BviToData
