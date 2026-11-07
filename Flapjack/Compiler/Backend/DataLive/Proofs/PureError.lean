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

/-- Pure word primitives do not consume or reset heap space. -/
theorem pure_word_doSpace {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (state : State C F) (pure : isPure (.wordOp op) = true) : doSpace (.wordOp op) args state = some state := by
  cases op <;> simp [isPure] at pure
  case wordOpw size operation =>
    cases size <;> simp_all [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case wordShift size operation amount =>
    cases size <;> simp_all [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case wordTest size test =>
    cases size <;> simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]
  case fpCmp cmp => simp [doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq]

/-- Successful pure word primitives preserve the state observed by the
liveness simulation. Resource bookkeeping is allowed to change. -/
theorem pure_word_doApp_stateRel {C F : Type} (op : ClosLang.WordOp) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (live : NumSet)
    (pure : isPure (.wordOp op) = true) (run : doApp (.wordOp op) args state = .val (value, next)) :
    stateRel next state live := by
  have space := pure_word_doSpace op args state pure
  cases found : doWordApp op args with
  | none => simp [doApp, space, doAppAux, applyNonFfi, found] at run
  | some result =>
    simp [doApp, space, doAppAux, applyNonFfi, found] at run
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

/-- The shared removal argument for an unused pure assignment. Its success
frame premise remains to be proved for every pure primitive, so this helper
is not the complete assignment case of the HOL pass theorem. -/
theorem simulationFor_removed_of_frame {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : NumSet) (pure : isPure op = true)
    (dead : sptLookup dest live = none)
    (successFrame : ∀ (args : List DataSem.Value) (state next : State C F) (value : DataSem.Value),
      doApp op args state = .val (value, next) → stateRel next state live) :
    simulationFor (C := C) (F := F) (.assign dest op names none) live := by
  intro source target result sourceNext run related notType exception
  have initial : stateRel source target live := by simpa [compile, dead, pure] using related
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
      cases app : doApp op args source with
      | err error =>
        have errorEq := pure_doApp_error op args source error pure app
        subst error
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | val pair =>
        obtain ⟨value, applied⟩ := pair
        have appliedRel := successFrame args source applied value app
        have finalRel := stateRel_setVar_dead applied target live dest value
          (stateRel_trans applied source target live appliedRel initial) dead
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · simp [compile, dead, pure, DataSem.evaluate]
        · cases op <;> try simp [isPure] at pure <;> cases applied <;>
            simpa [installSfs, postLive] using finalRel

/-- The liveness pass can remove an unused pure integer assignment. This
is a genuine subcase of the assignment simulation, untagged pending review. -/
theorem simulationFor_removed_int {C F : Type} (dest : Nat) (op : ClosLang.IntOp)
    (names : List Nat) (live : NumSet) (pure : isPure (.intOp op) = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.intOp op) names none) live := by
  apply simulationFor_removed_of_frame dest (.intOp op) names live pure dead
  intro args state next value run
  exact pure_int_doApp_stateRel op args state next value live pure run

/-- The liveness pass can remove an unused pure word assignment. -/
theorem simulationFor_removed_word {C F : Type} (dest : Nat) (op : ClosLang.WordOp)
    (names : List Nat) (live : NumSet) (pure : isPure (.wordOp op) = true)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.wordOp op) names none) live := by
  apply simulationFor_removed_of_frame dest (.wordOp op) names live pure dead
  intro args state next value run
  exact pure_word_doApp_stateRel op args state next value live pure run

/-- Successful label lookup changes no state observed by liveness. -/
theorem label_doApp_stateRel {C F : Type} (label : Nat) (args : List DataSem.Value)
    (state next : State C F) (value : DataSem.Value) (live : NumSet)
    (run : doApp (.label label) args state = .val (value, next)) : stateRel next state live := by
  cases args with
  | cons first rest =>
    simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi] at run
  | nil =>
    cases found : sptLookup label state.code with
    | none => simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, doStack, doLimSafe, found] at run
    | some entry =>
      simp [doApp, doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, doAppAux, applyNonFfi, doStack, doLimSafe, found] at run
      obtain ⟨_, rfl⟩ := run
      simp [stateRel]

/-- The liveness pass can remove an unused label lookup. -/
theorem simulationFor_removed_label {C F : Type} (dest label : Nat) (names : List Nat) (live : NumSet)
    (dead : sptLookup dest live = none) :
    simulationFor (C := C) (F := F) (.assign dest (.label label) names none) live := by
  apply simulationFor_removed_of_frame dest (.label label) names live rfl dead
  intro args state next value run
  exact label_doApp_stateRel label args state next value live run

end Flapjack.Compiler.Backend.DataLive
