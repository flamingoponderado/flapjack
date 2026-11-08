import Flapjack.Compiler.Backend.DataLive.Proofs.Force
import Flapjack.Compiler.Backend.Semantics.DataProps.PrimitiveLocals

/-! Full primitive relation for the data liveness proof. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- The auxiliary block dispatcher preserves related outcomes for every
block operation. This is untagged pending evaluator and carrier review. -/
theorem stateRel_doAppAux_block {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.BlockOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.blockOp op) args source) (doAppAux (.blockOp op) args target) := by
  by_cases pure : isPure (.blockOp op) = true
  · exact stateRel_doAppAux_pureBlock source target live op args pure related
  · cases op <;> simp [isPure] at pure
    case cons tag => exact stateRel_doAppAux_cons source target live tag args related
    case consExtend tag => exact stateRel_doAppAux_consExtend source target live tag args related
    case fromList tag => exact stateRel_doAppAux_fromList source target live tag args related
    case listAppend => exact stateRel_doAppAux_listAppend source target live args related
    case equal => exact stateRel_doAppAux_equal source target live args related
    case build parts => exact stateRel_doAppAux_build source target live parts args related

/-- Every primitive application produces matching errors or values and
related successful states. This is the current Lean evaluator's counterpart
of the source primitive simulation, untagged pending source review. -/
theorem stateRel_doApp {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp op args source) (doApp op args target) := by
  cases op with
  | label label => exact stateRel_doApp_label source target live label args related
  | ffi name => exact stateRel_doApp_ffi source target live name args related
  | intOp op => exact stateRel_doApp_int source target live op args related
  | wordOp op => exact stateRel_doApp_word source target live op args related
  | blockOp op =>
    apply stateRel_doApp_block_of_aux source target live op args related
    intro left right relation
    exact stateRel_doAppAux_block left right live op args relation
  | globOp op => exact stateRel_doApp_global source target live op args related
  | memOp op =>
    apply stateRel_doApp_memory_of_aux source target live op args related
    intro left right relation
    exact stateRel_doAppAux_memory left right live op args relation
  | install => exact stateRel_doApp_install source target live args related
  | thunkOp op => exact stateRel_doApp_thunk source target live op args related

/-- A source primitive error is reproduced by every related target state. -/
theorem stateRel_doApp_error {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (error : ErrorResult DataSem.Value)
    (related : stateRel source target live) (run : doApp op args source = .err error) :
    doApp op args target = .err error := by
  have simulation := stateRel_doApp source target live op args related
  rw [run] at simulation
  cases targetRun : doApp op args target with
  | err targetError =>
    simp [targetRun, appRel] at simulation
    cases simulation
    rfl
  | val value => simp [targetRun, appRel] at simulation

/-- A successful source primitive has a matching target result and related
post-state. -/
theorem stateRel_doApp_success {C F : Type} (source target sourceNext : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (value : DataSem.Value)
    (related : stateRel source target live) (run : doApp op args source = .val (value, sourceNext)) :
    ∃ targetNext, doApp op args target = .val (value, targetNext) ∧ stateRel sourceNext targetNext live := by
  have simulation := stateRel_doApp source target live op args related
  rw [run] at simulation
  cases targetRun : doApp op args target with
  | err error => simp [targetRun, appRel] at simulation
  | val pair =>
    obtain ⟨targetValue, targetNext⟩ := pair
    simp [targetRun, appRel] at simulation
    obtain ⟨rfl, nextRel⟩ := simulation
    exact ⟨targetNext, rfl, nextRel⟩

/-- If the initial local environments are equal, a successful primitive
preserves that equality as well as the liveness relation. This auxiliary
fact supports the evaluator stack-swap proof. -/
theorem stateRel_doApp_success_sameLocals {C F : Type} (source target sourceNext : State C F) (live : NumSet)
    (op : ClosLang.Op) (args : List DataSem.Value) (value : DataSem.Value)
    (related : stateRel source target live) (sameLocals : source.locals = target.locals)
    (run : doApp op args source = .val (value, sourceNext)) :
    ∃ targetNext, doApp op args target = .val (value, targetNext) ∧ stateRel sourceNext targetNext live ∧
      sourceNext.locals = targetNext.locals := by
  obtain ⟨targetNext, targetRun, after⟩ := stateRel_doApp_success source target sourceNext live op args value related run
  refine ⟨targetNext, targetRun, after, ?_⟩
  rw [(doApp_control op args source sourceNext value run).1,
    (doApp_control op args target targetNext value targetRun).1]
  exact sameLocals

/-- Equal local environments make the liveness relation valid for any live
set, once the states agree at the empty set. -/
theorem stateRel_of_sameLocals {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals) :
    stateRel source target live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  rw [sameLocals]

/-- Cutting equal local environments either fails on both sides or produces
related states with equal locals. -/
theorem stateRel_cutStateOpt_sameLocals {C F : Type} (source target : State C F) (live : NumSet)
    (names : Option NumSet) (related : stateRel source target live) (sameLocals : source.locals = target.locals) :
    (cutStateOpt names source = none ∧ cutStateOpt names target = none) ∨
      ∃ sourceNext targetNext, cutStateOpt names source = some sourceNext ∧
        cutStateOpt names target = some targetNext ∧ stateRel sourceNext targetNext live ∧
        sourceNext.locals = targetNext.locals := by
  cases names with
  | none => exact Or.inr ⟨source, target, rfl, rfl, related, sameLocals⟩
  | some names =>
    cases cut : cutEnv names source.locals with
    | none =>
      left
      simp [cutStateOpt, cutState, ← sameLocals, cut]
    | some env =>
      right
      refine ⟨{ source with locals := env }, { target with locals := env }, ?_, ?_, ?_, rfl⟩
      · simp [cutStateOpt, cutState, cut]
      · simp [cutStateOpt, cutState, ← sameLocals, cut]
      · rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
        exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, fun _ _ => rfl⟩

end Flapjack.Compiler.Backend.DataLive
