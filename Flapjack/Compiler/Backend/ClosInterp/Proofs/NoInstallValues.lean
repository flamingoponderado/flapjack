import Flapjack.Compiler.Backend.ClosInterp.Proofs.InitRelation

/-! Values and states used for the no-install interpreter-insertion case.
These proof-side definitions await HOL carrier and statement review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

mutual
/-- A value contains no closure body that can execute installation. -/
def valueNoInstall : ClosSem.Value → Bool
  | .number _ | .word64 _ | .byteVector _ | .refPtr _ _ => true
  | .block _ values => valuesNoInstall values
  | .closure _ supplied captured _ body =>
      !ClosLang.hasInstall body && valuesNoInstall supplied && valuesNoInstall captured
  | .recclosure _ supplied captured functions index =>
      valuesNoInstall supplied && valuesNoInstall captured && decide (index < functions.length) &&
        !ClosLang.hasInstallFuns functions
termination_by value => sizeOf value

/-- The list clause of the no-install value predicate. -/
def valuesNoInstall : List ClosSem.Value → Bool
  | [] => true
  | value :: values => valueNoInstall value && valuesNoInstall values
termination_by values => sizeOf values
end

/-- The Boolean list predicate is equivalent to checking every member. -/
theorem valuesNoInstall_iff (values : List ClosSem.Value) :
    valuesNoInstall values = true ↔ ∀ value ∈ values, valueNoInstall value = true := by
  induction values with
  | nil => simp [valuesNoInstall]
  | cons value rest ih => simp [valuesNoInstall, Bool.and_eq_true, ih]

/-- An evaluator result contains only no-install values when it succeeds or
raises; an abort has no returned value to inspect. -/
def resultNoInstall : Result (List ClosSem.Value) ClosSem.Value → Prop
  | .val values => valuesNoInstall values = true
  | .err (.raise value) => valueNoInstall value = true
  | .err (.abort _) => True

/-- A reference payload contains only no-install values. -/
def refNoInstall : ClosSem.Ref ClosSem.Value → Prop
  | .valueArray values => valuesNoInstall values = true
  | .thunk _ value => valueNoInstall value = true
  | .byteArray _ => True

/-- Each reachable reference payload contains only no-install values. -/
def refsNoInstall (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) : Prop :=
  ∀ index entry, refs.lookup index = some entry → refNoInstall entry

/-- Relation for the no-install case: related compiler state plus the
no-install invariants for target globals and references. -/
def StateRelNoInstall {C F : Type} (source target : ClosSem.State C F) : Prop :=
  StateRel1 source target ∧
    (∀ entry ∈ target.globals, ∀ value, entry = some value → valueNoInstall value = true) ∧
    refsNoInstall target.refs

/-- Selecting environment variables preserves the no-install invariant. -/
theorem lookupVars_noInstall (indices : List Nat) (env selected : List ClosSem.Value)
    (valid : valuesNoInstall env = true) (run : ClosSem.lookupVars indices env = some selected) :
    valuesNoInstall selected = true := by
  induction indices generalizing selected with
  | nil =>
    simp [ClosSem.lookupVars] at run
    subst selected
    simp [valuesNoInstall]
  | cons index rest ih =>
    simp only [ClosSem.lookupVars] at run
    cases found : env[index]? with
    | none => simp [found] at run
    | some value =>
      simp only [found] at run
      cases remaining : ClosSem.lookupVars rest env with
      | none => simp [remaining] at run
      | some values =>
        simp [remaining] at run
        subst selected
        have valueOk : valueNoInstall value = true := (valuesNoInstall_iff env).1 valid value (List.mem_of_getElem? found)
        have valuesOk := ih values remaining
        simp [valuesNoInstall, valueOk, valuesOk]

/-- Appending no-install value lists preserves the invariant. -/
theorem valuesNoInstall_append (left right : List ClosSem.Value) :
    valuesNoInstall (left ++ right) = true ↔ valuesNoInstall left = true ∧ valuesNoInstall right = true := by
  simp [valuesNoInstall_iff, List.mem_append]
  aesop

/-- Reversing a no-install value list preserves the invariant. -/
theorem valuesNoInstall_reverse (values : List ClosSem.Value) :
    valuesNoInstall values.reverse = true ↔ valuesNoInstall values = true := by
  simp [valuesNoInstall_iff]

/-- Taking a prefix preserves the no-install invariant. -/
theorem valuesNoInstall_take (values : List ClosSem.Value) (count : Nat)
    (valid : valuesNoInstall values = true) : valuesNoInstall (values.take count) = true := by
  apply (valuesNoInstall_iff _).2
  intro value member
  exact (valuesNoInstall_iff values).1 valid value (List.mem_of_mem_take member)

/-- Dropping a prefix preserves the no-install invariant. -/
theorem valuesNoInstall_drop (values : List ClosSem.Value) (count : Nat)
    (valid : valuesNoInstall values = true) : valuesNoInstall (values.drop count) = true := by
  apply (valuesNoInstall_iff _).2
  intro value member
  exact (valuesNoInstall_iff values).1 valid value (List.mem_of_mem_drop member)

/-- A function bundle has no installation exactly when each body does not. -/
theorem hasInstallFuns_eq_false_iff (functions : List (Nat × ClosLang.Exp)) :
    ClosLang.hasInstallFuns functions = false ↔ ∀ entry ∈ functions, ClosLang.hasInstall entry.2 = false := by
  induction functions with
  | nil => simp [ClosLang.hasInstallFuns]
  | cons entry rest ih =>
    cases entry with
    | mk arity body => simp [ClosLang.hasInstallFuns, ih]

/-- A no-install function bundle yields no-install recursive closures at all
valid indices. -/
theorem recursiveClosure_noInstall (location : Option Nat) (captured : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (capturedOk : valuesNoInstall captured = true) (functionsOk : ClosLang.hasInstallFuns functions = false)
    (bound : index < functions.length) :
    valueNoInstall (.recclosure location [] captured functions index) = true := by
  simp [valueNoInstall, valuesNoInstall, capturedOk, functionsOk, bound]

/-- Decrementing both clocks preserves the no-install state relation. -/
theorem stateRelNoInstall_decClock {C F : Type} (source target : ClosSem.State C F)
    (related : StateRelNoInstall source target) (amount : Nat) :
    StateRelNoInstall (ClosSem.decClock amount source) (ClosSem.decClock amount target) := by
  rcases related with ⟨⟨safe, sc, tc, maxEq, maxPositive, clock, ffi, globals, refs, compiler, oracle⟩, globalOk, refsOk⟩
  exact ⟨⟨safe, sc, tc, maxEq, maxPositive, by simp [ClosSem.decClock, clock], ffi, globals, refs, compiler, oracle⟩,
    globalOk, refsOk⟩

/-- The two initial states satisfy the no-install relation when the source
oracle has no auxiliary code. -/
theorem initialStates_noInstall {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : ClosSem.CompileOracle C) (compiler : ClosSem.Compiler C)
    (safe : ∀ index, (oracle index).2.2 = []) (positive : 1 ≤ maxApp) :
    StateRelNoInstall
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc insertProgram compiler) clock)
      (ClosSem.initialState ffi maxApp HolFiniteMapExact.empty (pureCo insertProgram ∘ oracle) compiler clock) := by
  refine ⟨⟨safe, rfl, rfl, rfl, positive, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · simp [ClosSem.initialState]
  · simp [refsNoInstall, ClosSem.initialState]

/-- Every closure generated for a no-install recursive bundle is safe. -/
theorem recursiveClosure_bundle_noInstall (location : Option Nat) (captured : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (capturedOk : valuesNoInstall captured = true)
    (functionsOk : ClosLang.hasInstallFuns functions = false) :
    valuesNoInstall ((List.range functions.length).map
      (fun i => ClosSem.Value.recclosure location [] captured functions i)) = true := by
  apply (valuesNoInstall_iff _).2
  intro value member
  simp only [List.mem_map, List.mem_range] at member
  obtain ⟨index, bound, rfl⟩ := member
  exact recursiveClosure_noInstall location captured functions index capturedOk functionsOk bound

/-- A no-install closure application produces either a no-install partial
closure or a no-install body, environment, and remaining arguments. -/
theorem destClosure_noInstall (maxApp : Nat) (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (kind : ClosSem.AppKind)
    (functionOk : valueNoInstall function = true) (argsOk : valuesNoInstall args = true)
    (found : ClosSem.destClosure maxApp location function args = some kind) :
    match kind with
    | .partialApp value => valueNoInstall value = true
    | .fullApp body env remaining => ClosLang.hasInstall body = false ∧ valuesNoInstall env = true ∧ valuesNoInstall remaining = true := by
  cases function with
  | closure closureLocation supplied captured arity body =>
    simp only [valueNoInstall, Bool.and_eq_true] at functionOk
    rw [ClosSem.destClosure] at found
    split at found
    · split at found
      · simp at found
        subst kind
        simp [valueNoInstall, valuesNoInstall_append, argsOk, functionOk.1.2, functionOk.2, functionOk.1.1]
      · simp at found
        subst kind
        have bodyOk : ClosLang.hasInstall body = false := by
          cases h : ClosLang.hasInstall body <;> simp [h] at functionOk ⊢
        have reversed : valuesNoInstall args.reverse = true := (valuesNoInstall_reverse args).2 argsOk
        have taken := valuesNoInstall_take args.reverse (arity - supplied.length) reversed
        have dropped := valuesNoInstall_drop args.reverse (arity - supplied.length) reversed
        have takenRev := (valuesNoInstall_reverse _).2 taken
        have droppedRev := (valuesNoInstall_reverse _).2 dropped
        simp [bodyOk, valuesNoInstall_append, takenRev, droppedRev, functionOk.1.2, functionOk.2]
    · simp at found
  | recclosure closureLocation supplied captured functions index =>
    simp only [valueNoInstall, Bool.and_eq_true] at functionOk
    rw [ClosSem.destClosure] at found
    cases selected : functions[index]? with
    | none => simp [selected] at found
    | some entry =>
      rcases entry with ⟨arity, body⟩
      simp only [selected] at found
      split at found
      · split at found
        · simp at found
          subst kind
          simp [valueNoInstall, valuesNoInstall_append, argsOk, functionOk.1.1.1, functionOk.1.1.2,
            functionOk.1.2, functionOk.2]
        · simp at found
          subst kind
          have functionBodies : ClosLang.hasInstallFuns functions = false := by
            cases h : ClosLang.hasInstallFuns functions <;> simp [h] at functionOk ⊢
          have bodyOk : ClosLang.hasInstall body = false :=
            (hasInstallFuns_eq_false_iff functions).1 functionBodies (arity, body) (List.mem_of_getElem? selected)
          have reversed : valuesNoInstall args.reverse = true := (valuesNoInstall_reverse args).2 argsOk
          have taken := valuesNoInstall_take args.reverse (arity - supplied.length) reversed
          have dropped := valuesNoInstall_drop args.reverse (arity - supplied.length) reversed
          have takenRev := (valuesNoInstall_reverse _).2 taken
          have droppedRev := (valuesNoInstall_reverse _).2 dropped
          have recursiveOk := recursiveClosure_bundle_noInstall closureLocation captured functions functionOk.1.1.2 functionBodies
          simp [bodyOk, valuesNoInstall_append, takenRev, droppedRev, functionOk.1.1.1, functionOk.1.1.2, recursiveOk]
      · simp at found
  | _ => simp [ClosSem.destClosure] at found

/-- Constants decode to values without executable installation bodies. -/
theorem makeConst_noInstall (constant : ClosLang.Const) : valueNoInstall (ClosSem.makeConst constant) = true := by
  cases constant with
  | constInt value => simp [ClosSem.makeConst, valueNoInstall]
  | constWord64 value => simp [ClosSem.makeConst, valueNoInstall]
  | constStr value => simp [ClosSem.makeConst, valueNoInstall]
  | constCons tag fields =>
    simp only [ClosSem.makeConst, valueNoInstall, valuesNoInstall_iff]
    intro value member
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    exact makeConst_noInstall child
termination_by sizeOf constant
decreasing_by
  have h := List.sizeOf_lt_of_mem childMember
  simp_wf
  omega

/-- A list has no installation exactly when each of its expressions does not. -/
theorem hasInstallList_eq_false_iff (expressions : List ClosLang.Exp) :
    ClosLang.hasInstallList expressions = false ↔ ∀ expression ∈ expressions, ClosLang.hasInstall expression = false := by
  induction expressions with
  | nil => simp [ClosLang.hasInstallList]
  | cons expression rest ih => simp [ClosLang.hasInstallList, ih]

/-- Updating a reference with a safe payload preserves the reference invariant. -/
theorem refsNoInstall_update (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (index : Nat) (entry : ClosSem.Ref ClosSem.Value)
    (valid : refsNoInstall refs) (entryOk : refNoInstall entry) :
    refsNoInstall (refs.updateEq (index, entry)) := by
  intro key found lookup
  by_cases equal : key = index
  · subst key
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at lookup
    subst found
    exact entryOk
  · have oldLookup : refs.lookup key = some found := by
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, equal] using lookup
    exact valid key found oldLookup

/-- Updating both related reference stores with the same safe map preserves
the no-install relation. -/
theorem stateRelNoInstall_withRefs {C F : Type} (source target : ClosSem.State C F)
    (related : StateRelNoInstall source target) (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (refsOk : refsNoInstall refs) :
    StateRelNoInstall { source with refs := refs } { target with refs := refs } := by
  rcases related with ⟨⟨safe, sc, tc, maxEq, maxPositive, clock, ffi, globals, _, compiler, oracle⟩, globalOk, _⟩
  exact ⟨⟨safe, sc, tc, maxEq, maxPositive, clock, ffi, globals, rfl, compiler, oracle⟩, globalOk, refsOk⟩

/-- An inspected thunk in a safe store contains a no-install value. -/
theorem destThunk_value_noInstall (values : List ClosSem.Value)
    (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (mode : Flapjack.AstHOL.ThunkMode) (value : ClosSem.Value)
    (valid : refsNoInstall refs) (found : ClosSem.destThunk values refs = .isThunk mode value) :
    valueNoInstall value = true := by
  unfold ClosSem.destThunk at found
  repeat' split at found
  all_goals simp_all
  all_goals
    rename_i _ _ index _ _ _ heq _
    exact valid index (.thunk mode value) heq

/-- Updating a thunk with a no-install result preserves safe references. -/
theorem updateThunk_noInstall (targets values : List ClosSem.Value)
    (refs next : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (valid : refsNoInstall refs) (valuesOk : valuesNoInstall values = true)
    (run : ClosSem.updateThunk targets refs values = some next) : refsNoInstall next := by
  unfold ClosSem.updateThunk ClosSem.storeThunk at run
  repeat' split at run
  all_goals simp_all [valuesNoInstall]
  all_goals
    rw [← run]
    apply refsNoInstall_update
    · exact valid
    · exact valuesOk

end Flapjack.Compiler.Backend.ClosInterp
