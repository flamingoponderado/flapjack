import Flapjack.Compiler.Backend.DataLive.Proofs.PureMemory

/-! Resource-accounting relations for retained data-language assignments. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Updating the unobserved resource bookkeeping fields preserves the
liveness relation. This is auxiliary infrastructure. -/
theorem stateRel_bookkeeping {C F : Type} (source target : State C F) (live : NumSet)
    (sourceSafe targetSafe : Bool) (sourceMax targetMax : Option Nat) (sourcePeak targetPeak : Nat)
    (related : stateRel source target live) :
    stateRel { source with safeForSpace := sourceSafe, stackMax := sourceMax, peakHeapLength := sourcePeak }
      { target with safeForSpace := targetSafe, stackMax := targetMax, peakHeapLength := targetPeak } live := related

/-- Setting the same amount of available space in related states preserves
their relation. -/
theorem stateRel_setSpace {C F : Type} (source target : State C F) (live : NumSet)
    (amount : Nat) (related : stateRel source target live) :
    stateRel { source with space := amount } { target with space := amount } live := by
  rcases related with ⟨code, clock, _, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, clock, rfl, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- Resource-limit and stack bookkeeping retain the liveness relation even
when their unobserved safety and maximum-stack fields differ. -/
theorem stateRel_doStackLim {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (related : stateRel source target live) :
    stateRel (doStack op args (doLimSafe source op args)) (doStack op args (doLimSafe target op args)) live := by
  simpa [stateRel, doStack, doLimSafe] using related

/-- Space accounting either fails on both related states or succeeds with
related results; resource safety and peak statistics may differ. This is
untagged auxiliary infrastructure for the retained-assignment proof. -/
theorem stateRel_doSpace {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (related : stateRel source target live) :
    (doSpace op args source = none ∧ doSpace op args target = none) ∨
      ∃ sourceNext targetNext, doSpace op args source = some sourceNext ∧
        doSpace op args target = some targetNext ∧ stateRel sourceNext targetNext live := by
  by_cases reset : DataLang.opSpaceReset op = true
  · right
    simp only [doSpace, reset, ↓reduceIte]
    refine ⟨_, _, rfl, rfl, ?_⟩
    rcases related with ⟨code, clock, _, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
    exact ⟨code, clock, rfl, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  · by_cases zero : DataSpace.opSpaceReq op args.length = 0
    · right
      simp [doSpace, reset, zero]
      exact related
    · by_cases insufficient : source.space < DataSpace.opSpaceReq op args.length
      · left
        have targetInsufficient : target.space < DataSpace.opSpaceReq op args.length := by
          rw [← related.2.2.1]
          exact insufficient
        simp [doSpace, reset, zero, consumeSpace, insufficient, targetInsufficient]
      · right
        have targetEnough : ¬target.space < DataSpace.opSpaceReq op args.length := by
          rw [← related.2.2.1]
          exact insufficient
        simp only [doSpace, reset, ↓reduceIte, zero, consumeSpace, insufficient, targetEnough]
        refine ⟨_, _, rfl, rfl, ?_⟩
        rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
        exact ⟨code, clock, by simp [space], ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- Matching primitive outcomes have equal errors or values and related
result states. This relation is auxiliary and has no direct HOL declaration. -/
def appRel {C F : Type} (live : NumSet)
    (source target : Result (DataSem.Value × State C F) DataSem.Value) : Prop :=
  match source, target with
  | .err left, .err right => left = right
  | .val (left, sourceNext), .val (right, targetNext) => left = right ∧ stateRel sourceNext targetNext live
  | _, _ => False

/-- The integer auxiliary dispatcher returns the numeric result without
changing the state, or a type error. -/
theorem doAppAux_int_exact {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value) (state : State C F) :
    doAppAux (.intOp op) args state =
      match doIntApp op args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  cases result : doIntApp op args <;> simp [doAppAux, applyNonFfi, result]

/-- Except for the two rejected comparison constructors, integer dispatch
uses the common space and auxiliary-operation path. -/
theorem doApp_int_normal {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value) (state : State C F)
    (notGreater : op ≠ .greater) (notGreaterEq : op ≠ .greaterEq) :
    doApp (.intOp op) args state =
      match doSpace (.intOp op) args state with
      | none => .err (.abort .typeError)
      | some next => doAppAux (.intOp op) args (doStack (.intOp op) args (doLimSafe next (.intOp op) args)) := by
  cases op <;> simp_all [doApp] <;> rfl

/-- The integer dispatcher on related states returns equal outcomes and
preserves their relation, including both resource exhaustion and primitive
type errors. This is an untagged case of the HOL primitive relation. -/
theorem stateRel_doApp_int {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.IntOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.intOp op) args source) (doApp (.intOp op) args target) := by
  by_cases greater : op = .greater
  · subst op; rfl
  · by_cases greaterEq : op = .greaterEq
    · subst op; rfl
    · rw [doApp_int_normal op args source greater greaterEq, doApp_int_normal op args target greater greaterEq]
      rcases stateRel_doSpace source target live (.intOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
      · simp [failed.1, failed.2, appRel]
      · simp only [sourceRun, targetRun]
        rw [doAppAux_int_exact, doAppAux_int_exact]
        split
        · simp [appRel]
        · simp only [appRel, true_and]
          exact stateRel_doStackLim sourceNext targetNext live (.intOp op) args nextRel

/-- Flushing related states after a primitive error preserves the relation
at the empty live set. -/
theorem stateRel_flushInstall {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (related : stateRel source target live) :
    stateRel (flushState true (installSfs op source)) (flushState true (installSfs op target)) .ln := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨code, clock, space, ffi, refs, global, ?_, ?_, compiler, oracle, stamps, limits, frames, ?_⟩
  · exact handler
  · rfl
  · intro key member
    simp [sptMem, sptDomain, sptLookup] at member

/-- Installation safety bookkeeping preserves the liveness relation. -/
theorem stateRel_installSfs {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (related : stateRel source target live) :
    stateRel (installSfs op source) (installSfs op target) live := by
  simpa [stateRel, installSfs] using related

/-- A retained, unannotated assignment simulates when its primitive
dispatcher preserves the liveness relation. The primitive relation premise
is an open prerequisite for a complete assignment proof. -/
theorem simulationFor_retained_of_appRel {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : NumSet)
    (retained : ((sptLookup dest live).isNone && isPure op) = false)
    (primitiveRel : ∀ (source target : State C F) (args : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp op args source) (doApp op args target)) :
    simulationFor (C := C) (F := F) (.assign dest op names none) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target (sptListInsert names (sptDelete dest live)) := by
    simpa [compile, retained] using related
  have readEq := stateRel_getVars_listInsert source target names (sptDelete dest live) initial
  have smaller : stateRel source target (sptDelete dest live) :=
    stateRel_mono source target _ _ initial (fun key member => (mem_listInsert names _ key).2 (Or.inr member))
  by_cases invalid : (DataLang.opRequiresNames op == true) = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars names source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some args =>
      have targetRead : DataSem.getVars names target.locals = some args := by rw [← readEq, read]
      have appRelated := primitiveRel source target args smaller
      cases sourceApp : doApp op args source with
      | err error =>
        cases targetApp : doApp op args target with
        | val pair => simp [sourceApp, targetApp, appRel] at appRelated
        | err targetError =>
          simp [sourceApp, targetApp, appRel] at appRelated
          subst targetError
          simp [DataSem.evaluate, invalid, read, cutStateOpt, sourceApp] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨flushState true (installSfs op target), ?_, ?_⟩
          · simp [compile, retained, DataSem.evaluate, invalid, targetRead, cutStateOpt, targetApp]
          · exact stateRel_flushInstall source target _ op initial
      | val pair =>
        obtain ⟨value, sourceApplied⟩ := pair
        cases targetApp : doApp op args target with
        | err error => simp [sourceApp, targetApp, appRel] at appRelated
        | val targetPair =>
          obtain ⟨targetValue, targetApplied⟩ := targetPair
          simp [sourceApp, targetApp, appRel] at appRelated
          obtain ⟨rfl, appliedRel⟩ := appRelated
          simp [DataSem.evaluate, invalid, read, cutStateOpt, sourceApp] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨setVar dest value (installSfs op targetApplied), ?_, ?_⟩
          · simp [compile, retained, DataSem.evaluate, invalid, targetRead, cutStateOpt, targetApp]
          · exact stateRel_setVar _ _ live dest value (stateRel_installSfs _ _ _ op appliedRel)

/-- Retained unannotated integer assignments satisfy the liveness simulation. -/
theorem simulationFor_retained_int {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (names : List Nat) (live : NumSet)
    (retained : ((sptLookup dest live).isNone && isPure (.intOp op)) = false) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) names none) live := by
  apply simulationFor_retained_of_appRel dest (.intOp op) names live retained
  intro source target args related
  exact stateRel_doApp_int source target _ op args related

/-- The word auxiliary dispatcher returns the same word result without
changing its state, or reports a type error. -/
theorem doAppAux_word_exact {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value) (state : State C F) :
    doAppAux (.wordOp op) args state =
      match doWordApp op args with
      | none => .err (.abort .typeError)
      | some value => .val (value, state) := by
  cases result : doWordApp op args <;> simp [doAppAux, applyNonFfi, result]

/-- The word dispatcher preserves related states and produces equal results. -/
theorem stateRel_doApp_word {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.WordOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.wordOp op) args source) (doApp (.wordOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.wordOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    rw [doAppAux_word_exact, doAppAux_word_exact]
    split
    · simp [appRel]
    · simp only [appRel, true_and]
      exact stateRel_doStackLim sourceNext targetNext live (.wordOp op) args nextRel

/-- Retained unannotated word assignments satisfy the liveness simulation. -/
theorem simulationFor_retained_word {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (names : List Nat) (live : NumSet)
    (retained : ((sptLookup dest live).isNone && isPure (.wordOp op)) = false) :
    simulationFor (C := C) (F := F) (.assign dest (.wordOp op) names none) live := by
  apply simulationFor_retained_of_appRel dest (.wordOp op) names live retained
  intro source target args related
  exact stateRel_doApp_word source target _ op args related

/-- Every unannotated integer assignment satisfies the liveness simulation. -/
theorem simulationFor_assign_int {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (names : List Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) names none) live := by
  cases retained : ((sptLookup dest live).isNone && isPure (.intOp op)) with
  | false => exact simulationFor_retained_int dest op names live retained
  | true =>
    have parts : (sptLookup dest live).isNone = true ∧ isPure (.intOp op) = true := by simpa using retained
    have dead : sptLookup dest live = none := Option.isNone_iff_eq_none.mp parts.1
    exact simulationFor_removed_int dest op names live parts.2 dead

/-- Every unannotated word assignment satisfies the liveness simulation. -/
theorem simulationFor_assign_word {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (names : List Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.wordOp op) names none) live := by
  cases retained : ((sptLookup dest live).isNone && isPure (.wordOp op)) with
  | false => exact simulationFor_retained_word dest op names live retained
  | true =>
    have parts : (sptLookup dest live).isNone = true ∧ isPure (.wordOp op) = true := by simpa using retained
    have dead : sptLookup dest live = none := Option.isNone_iff_eq_none.mp parts.1
    exact simulationFor_removed_word dest op names live parts.2 dead

/-- The label dispatcher preserves related states and returns equal results. -/
theorem stateRel_doApp_label {C F : Type} (source target : State C F) (live : NumSet)
    (label : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.label label) args source) (doApp (.label label) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.label label) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    have accountRel := stateRel_doStackLim sourceNext targetNext live (.label label) args nextRel
    cases args with
    | cons first rest => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases found : sptLookup label sourceNext.code with
      | none =>
        have other : sptLookup label targetNext.code = none := by rw [← nextRel.1, found]
        simp [doAppAux, applyNonFfi, doStack, doLimSafe, found, other, appRel]
      | some entry =>
        have other : sptLookup label targetNext.code = some entry := by rw [← nextRel.1, found]
        simpa [doAppAux, applyNonFfi, doStack, doLimSafe, found, other, appRel, stateRel] using accountRel

/-- Every unannotated label assignment satisfies the liveness simulation. -/
theorem simulationFor_assign_label {C F : Type} (dest label : Nat) (names : List Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.label label) names none) live := by
  cases retained : ((sptLookup dest live).isNone && isPure (.label label)) with
  | false =>
    apply simulationFor_retained_of_appRel dest (.label label) names live retained
    intro source target args related
    exact stateRel_doApp_label source target _ label args related
  | true =>
    have dead : sptLookup dest live = none := by simpa [isPure] using retained
    exact simulationFor_removed_label dest label names live dead

/-- A successful source environment cut can be mirrored by cutting the
target to the live intersection. This auxiliary fact preserves all state
fields observed by the liveness relation. -/
theorem stateRel_cutState_inter {C F : Type} (source target sourceNext : State C F)
    (names live : NumSet) (related : stateRel source target (sptInter names live))
    (run : cutStateOpt (some names) source = some sourceNext) :
    ∃ targetNext, cutStateOpt (some (sptInter names live)) target = some targetNext ∧
      stateRel sourceNext targetNext live := by
  cases cut : cutEnv names source.locals with
  | none => simp [cutStateOpt, cutState, cut] at run
  | some sourceEnv =>
    obtain ⟨targetEnv, targetCut, locals⟩ := cutEnv_inter_related source target names live related sourceEnv cut
    simp [cutStateOpt, cutState, cut] at run
    subst sourceNext
    refine ⟨{ target with locals := targetEnv }, ?_, ?_⟩
    · simp [cutStateOpt, cutState, targetCut]
    · rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
      exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- An annotated assignment simulates when its primitive dispatcher
preserves the liveness relation. The primitive relation premise remains an
open prerequisite for the general assignment theorem. -/
theorem simulationFor_annotated_of_appRel {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names live : NumSet)
    (primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp op values source) (doApp op values target)) :
    simulationFor (C := C) (F := F) (.assign dest op args (some names)) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target (sptListInsert args (sptInter names (sptDelete dest live))) := by
    simpa [compile] using related
  have readEq := stateRel_getVars_listInsert source target args (sptInter names (sptDelete dest live)) initial
  have cutRel : stateRel source target (sptInter names (sptDelete dest live)) :=
    stateRel_mono source target _ _ initial (fun key member => (mem_listInsert args _ key).2 (Or.inr member))
  by_cases invalid : (DataLang.opRequiresNames op == false) = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars args source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some values =>
      have targetRead : DataSem.getVars args target.locals = some values := by rw [← readEq, read]
      cases cut : cutStateOpt (some names) source with
      | none =>
        simp [DataSem.evaluate, invalid, read, cut] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | some sourceCut =>
        obtain ⟨targetCut, targetCutRun, afterCut⟩ :=
          stateRel_cutState_inter source target sourceCut names (sptDelete dest live) cutRel cut
        have appRelated := primitiveRel sourceCut targetCut values afterCut
        cases sourceApp : doApp op values sourceCut with
        | err error =>
          cases targetApp : doApp op values targetCut with
          | val pair => simp [sourceApp, targetApp, appRel] at appRelated
          | err targetError =>
            simp [sourceApp, targetApp, appRel] at appRelated
            subst targetError
            simp [DataSem.evaluate, invalid, read, cut, sourceApp] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨flushState true (installSfs op targetCut), ?_, ?_⟩
            · simp [compile, DataSem.evaluate, invalid, targetRead, targetCutRun, targetApp]
            · exact stateRel_flushInstall sourceCut targetCut _ op afterCut
        | val pair =>
          obtain ⟨value, sourceApplied⟩ := pair
          cases targetApp : doApp op values targetCut with
          | err error => simp [sourceApp, targetApp, appRel] at appRelated
          | val targetPair =>
            obtain ⟨targetValue, targetApplied⟩ := targetPair
            simp [sourceApp, targetApp, appRel] at appRelated
            obtain ⟨rfl, appliedRel⟩ := appRelated
            simp [DataSem.evaluate, invalid, read, cut, sourceApp] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨setVar dest value (installSfs op targetApplied), ?_, ?_⟩
            · simp [compile, DataSem.evaluate, invalid, targetRead, targetCutRun, targetApp]
            · exact stateRel_setVar _ _ live dest value (stateRel_installSfs _ _ _ op appliedRel)

/-- Annotated integer assignments satisfy the liveness simulation. -/
theorem simulationFor_annotated_int {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (args : List Nat) (names live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) args (some names)) live := by
  apply simulationFor_annotated_of_appRel dest (.intOp op) args names live
  intro source target values related
  exact stateRel_doApp_int source target _ op values related

/-- Annotated word assignments satisfy the liveness simulation. -/
theorem simulationFor_annotated_word {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (args : List Nat) (names live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.wordOp op) args (some names)) live := by
  apply simulationFor_annotated_of_appRel dest (.wordOp op) args names live
  intro source target values related
  exact stateRel_doApp_word source target _ op values related

/-- Integer assignments satisfy the liveness simulation with or without a
live-name annotation. -/
theorem simulationFor_assign_int_all {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) args names) live := by
  cases names with
  | none => exact simulationFor_assign_int dest op args live
  | some names => exact simulationFor_annotated_int dest op args names live

/-- Word assignments satisfy the liveness simulation with or without a
live-name annotation. -/
theorem simulationFor_assign_word_all {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.wordOp op) args names) live := by
  cases names with
  | none => exact simulationFor_assign_word dest op args live
  | some names => exact simulationFor_annotated_word dest op args names live

/-- Label assignments satisfy the liveness simulation with or without a
live-name annotation. -/
theorem simulationFor_assign_label_all {C F : Type} (dest label : Nat)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.label label) args names) live := by
  cases names with
  | none => exact simulationFor_assign_label dest label args live
  | some names =>
    apply simulationFor_annotated_of_appRel dest (.label label) args names live
    intro source target values related
    exact stateRel_doApp_label source target _ label values related

end Flapjack.Compiler.Backend.DataLive
