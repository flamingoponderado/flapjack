import Flapjack.Compiler.Backend.DataLive.Proofs.Simulation

/-! Error behavior of pure data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A pure operation cannot be an FFI call. -/
theorem isPure_ne_ffi (op : ClosLang.Op) (pure : isPure op = true)
    (name : Flapjack.Basis.Pure.MlString.MlString) : op ≠ .ffi name := by
  intro equal
  subst op
  simp [isPure] at pure

/-- A pure operation cannot install code. -/
theorem isPure_ne_install (op : ClosLang.Op) (pure : isPure op = true) : op ≠ .install := by
  intro equal
  subst op
  simp [isPure] at pure

/-- Non-FFI primitive dispatch can fail only with a type error. This is
untagged auxiliary infrastructure for the HOL pure-operation proof. -/
theorem doAppAux_error_nonFfi {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (error : ErrorResult DataSem.Value)
    (noFfi : ∀ name, op ≠ .ffi name) (run : doAppAux op args state = .err error) :
    error = .abort .typeError := by
  simp only [doAppAux] at run
  repeat' (split at run <;> try simp_all)

/-- A pure primitive application can fail only with a type error. This
statement is untagged until the source evaluator and carriers are reviewed. -/
theorem pure_doApp_error {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (error : ErrorResult DataSem.Value)
    (pure : isPure op = true) (run : doApp op args state = .err error) :
    error = .abort .typeError := by
  have noFfi := isPure_ne_ffi op pure
  have noInstall := isPure_ne_install op pure
  simp only [doApp] at run
  repeat' (split at run <;> try simp_all)
  all_goals exact doAppAux_error_nonFfi op args _ error noFfi run

/-- A successful pure integer operation changes only resource bookkeeping,
so it leaves the liveness relation to its input state intact. This is an
untagged case of the still-open pure-operation success lemma. -/
theorem pure_int_doApp_stateRel {C F : Type} (op : ClosLang.IntOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (live : NumSet)
    (pure : isPure (.intOp op) = true) (run : doApp (.intOp op) args state = .val (value, next)) :
    stateRel next state live := by
  cases op <;> simp [isPure] at pure
  case greater => simp [doApp] at run
  case greaterEq => simp [doApp] at run
  case const number =>
    cases found : doIntApp (.const number) args with
    | none => simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, found] at run
    | some result =>
      simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, found] at run
      obtain ⟨_, rfl⟩ := run
      simp [stateRel, doStack, doLimSafe]
  case lessConstSmall number =>
    cases found : doIntApp (.lessConstSmall number) args with
    | none => simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, found] at run
    | some result =>
      simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, found] at run
      obtain ⟨_, rfl⟩ := run
      simp [stateRel, doStack, doLimSafe]

/-- The liveness state relation is transitive at a fixed live set. -/
theorem stateRel_trans {C F : Type} (first middle last : State C F) (live : NumSet)
    (left : stateRel first middle live) (right : stateRel middle last live) : stateRel first last live := by
  rcases left with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, al⟩
  rcases right with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, bl⟩
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8, a9.trans b9, a10.trans b10, a11.trans b11, a12.trans b12, a13.trans b13,
    fun key member => (al key member).trans (bl key member)⟩

/-- Updating a dead local cannot affect the liveness relation. -/
theorem stateRel_setVar_dead {C F : Type} (source target : State C F) (live : NumSet)
    (dest : Nat) (value : DataSem.Value) (related : stateRel source target live)
    (dead : sptLookup dest live = none) : stateRel (setVar dest value source) target live := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  have different : key ≠ dest := by
    intro same
    subst key
    simp [sptMem, sptDomain, dead] at member
  simpa [setVar, sptLookup_sptInsert_ne dest key value _ different] using locals key member

/-- The liveness pass can remove an unused pure integer assignment. This
is a genuine subcase of the assignment simulation, untagged pending review. -/
theorem simulationFor_removed_int {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (names : List Nat) (live : NumSet) (pure : isPure (.intOp op) = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) names none) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target live := by simpa [compile, dead, pure] using related
  by_cases invalid : (DataLang.opRequiresNames (.intOp op) == true) = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars names source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some args =>
      cases app : doApp (.intOp op) args source with
      | err error =>
        have errorEq := pure_doApp_error (.intOp op) args source error pure app
        subst error
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | val pair =>
        obtain ⟨value, applied⟩ := pair
        have appliedRel := pure_int_doApp_stateRel op args source applied value live pure app
        have finalRel := stateRel_setVar_dead applied target live dest value
          (stateRel_trans applied source target live appliedRel initial) dead
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · simp [compile, dead, pure, DataSem.evaluate]
        · cases applied
          simpa [installSfs, postLive] using finalRel

end Flapjack.Compiler.Backend.DataLive
