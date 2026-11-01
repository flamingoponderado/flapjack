import Flapjack.Compiler.Backend.DataLive.Proofs.State

/-! Compositional simulation cases for data liveness. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- The live set required after an evaluation: stopped executions have no
continuing local-variable obligations. -/
def postLive (result : Option (Result (List DataSem.Value) DataSem.Value)) (live : NumSet) : NumSet :=
  match result with | none => live | some _ => .ln

/-- Corresponding exception jumps required by the source liveness proof. -/
def exceptionRel {C F : Type} (source target : State C F) : Prop :=
  ∀ sourceJump, jumpExc source = some sourceJump →
    ∃ targetJump, jumpExc target = some targetJump ∧ stateRel sourceJump targetJump .ln ∧
      targetJump.handler = sourceJump.handler ∧ targetJump.stack.length = sourceJump.stack.length

/-- The source-shaped liveness simulation for one program and output live
set. It is untagged pending data-evaluator and state-carrier review. -/
def simulationFor {C F : Type} (program : DataLang.Prog) (live : NumSet) : Prop :=
  ∀ (source target : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value)) (sourceNext : State C F),
    DataSem.evaluate program source = (result, sourceNext) →
    stateRel source target (compile program live).2 →
    result ≠ some (.err (.abort .typeError)) → exceptionRel source target →
    ∃ targetNext, DataSem.evaluate (compile program live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live)

/-- A relation for the continuing live set also supplies the weaker
postcondition for a stopped evaluation. -/
theorem stateRel_postLive {C F : Type} (source target : State C F) (live : NumSet)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (related : stateRel source target live) :
    stateRel source target (postLive result live) := by
  cases result with
  | none => exact related
  | some value =>
    apply stateRel_mono source target live .ln related
    intro key member
    simp [sptMem, sptDomain, sptLookup] at member

/-- The skip case of the liveness simulation. -/
theorem simulationFor_skip {C F : Type} (live : NumSet) : simulationFor (C := C) (F := F) .skip live := by
  intro source target result sourceNext run related notType exception
  simp [DataSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨target, (compile_skip_correct source target live related).1, (compile_skip_correct source target live related).2⟩

/-- The move case of the liveness simulation. -/
theorem simulationFor_move {C F : Type} (dest src : Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.move dest src) live := by
  intro source target result sourceNext run related notType exception
  obtain ⟨targetNext, targetRun, finalRel⟩ :=
    compile_move_correct source target sourceNext live dest src result related run notType
  exact ⟨targetNext, targetRun, stateRel_postLive sourceNext targetNext live result finalRel⟩

/-- The tick case of the liveness simulation. -/
theorem simulationFor_tick {C F : Type} (live : NumSet) : simulationFor (C := C) (F := F) .tick live := by
  intro source target result sourceNext run related notType exception
  obtain ⟨targetNext, targetRun, finalRel⟩ := compile_tick_correct source target live related
  rw [run] at targetRun finalRel
  exact ⟨targetNext, targetRun, stateRel_postLive sourceNext targetNext live result finalRel⟩

/-- The return case of the liveness simulation. -/
theorem simulationFor_return {C F : Type} (names : List Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.return names) live := by
  intro source target result sourceNext run related notType exception
  obtain ⟨targetNext, targetRun, finalRel⟩ :=
    compile_return_correct source target sourceNext live names result related run notType
  exact ⟨targetNext, targetRun, stateRel_postLive sourceNext targetNext live result finalRel⟩

/-- The make-space case of the liveness simulation. -/
theorem simulationFor_makeSpace {C F : Type} (amount : Nat) (names live : NumSet) :
    simulationFor (C := C) (F := F) (.makeSpace amount names) live := by
  intro source target result sourceNext run related notType exception
  obtain ⟨targetNext, targetRun, finalRel⟩ :=
    compile_makeSpace_correct source target sourceNext live names amount result related run notType
  exact ⟨targetNext, targetRun, stateRel_postLive sourceNext targetNext live result finalRel⟩

/-- Raising preserves the relation using the corresponding exception jump. -/
theorem simulationFor_raise {C F : Type} (name : Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.raise name) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target (sptInsert name () .ln) := by
    simpa [compile] using related
  have nameLive : sptMem name (sptInsert name () .ln) :=
    (sptMem_sptInsert name name () _).2 (Or.inl rfl)
  have readEq := stateRel_getVar source target _ name initial nameLive
  cases read : DataSem.getVar name source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar name target.locals = some value := by rw [← readEq, read]
    cases jump : jumpExc source with
    | none =>
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some sourceJump =>
      obtain ⟨targetJump, targetRun, after, _, _⟩ := exception sourceJump jump
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨targetJump, by simp [compile, DataSem.evaluate, targetRead, targetRun], after⟩

/-- The conditional case combines simulations of both branches and uses the
union of their input live sets. -/
theorem simulationFor_if {C F : Type} (name : Nat) (yes no : DataLang.Prog) (live : NumSet)
    (yesIH : simulationFor (C := C) (F := F) yes live)
    (noIH : simulationFor (C := C) (F := F) no live) :
    simulationFor (C := C) (F := F) (.ifThenElse name yes no) live := by
  intro source target result sourceNext run related notType exception
  generalize yesCompiled : compile yes live = yesPair
  obtain ⟨yesProg, yesLive⟩ := yesPair
  generalize noCompiled : compile no live = noPair
  obtain ⟨noProg, noLive⟩ := noPair
  have initial : stateRel source target (sptInsert name () (sptUnion yesLive noLive)) := by
    simpa [compile, yesCompiled, noCompiled] using related
  have nameLive : sptMem name (sptInsert name () (sptUnion yesLive noLive)) :=
    (sptMem_sptInsert name name () _).2 (Or.inl rfl)
  have readEq := stateRel_getVar source target _ name initial nameLive
  have yesRel : stateRel source target yesLive :=
    stateRel_mono source target _ _ initial (fun key member =>
      (sptMem_sptInsert key name () _).2 (Or.inr ((sptMem_sptUnion yesLive noLive key).2 (Or.inl member))))
  have noRel : stateRel source target noLive :=
    stateRel_mono source target _ _ initial (fun key member =>
      (sptMem_sptInsert key name () _).2 (Or.inr ((sptMem_sptUnion yesLive noLive key).2 (Or.inr member))))
  cases read : DataSem.getVar name source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar name target.locals = some value := by rw [← readEq, read]
    by_cases isTrue : DataSem.isBool true value
    · have sourceRun : DataSem.evaluate yes source = (result, sourceNext) := by
        simpa [DataSem.evaluate, read, isTrue] using run
      have branchRel : stateRel source target (compile yes live).2 := by simpa [yesCompiled] using yesRel
      obtain ⟨targetNext, targetRun, finalRel⟩ := yesIH source target result sourceNext sourceRun branchRel notType exception
      refine ⟨targetNext, ?_, finalRel⟩
      simpa [compile, yesCompiled, noCompiled, DataSem.evaluate, targetRead, isTrue] using targetRun
    · by_cases isFalse : DataSem.isBool false value
      · have sourceRun : DataSem.evaluate no source = (result, sourceNext) := by
          simpa [DataSem.evaluate, read, isTrue, isFalse] using run
        have branchRel : stateRel source target (compile no live).2 := by simpa [noCompiled] using noRel
        obtain ⟨targetNext, targetRun, finalRel⟩ := noIH source target result sourceNext sourceRun branchRel notType exception
        refine ⟨targetNext, ?_, finalRel⟩
        simpa [compile, yesCompiled, noCompiled, DataSem.evaluate, targetRead, isTrue, isFalse] using targetRun
      · simp [DataSem.evaluate, read, isTrue, isFalse] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)

end Flapjack.Compiler.Backend.DataLive
