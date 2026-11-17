module

public import Flapjack.Compiler.Backend.Semantics.DataProps.CcCoOnlyDiffApp
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

@[expose] public section

/-!
# Evaluation under a compiler-configuration change

Every state operation of the data evaluator except primitive application reads
only the fields compared by `ccCoOnlyDiff`, so each of them commutes with the
compiler rebuild. With those facts, evaluation at a rebuilt state mirrors
evaluation at the original state, and the two final states still agree.

These declarations are Flapjack-only infrastructure: they are the field-level
steps for the port of HOL `evaluate_cc_co_only_diff`
(`dataPropsScript.sml:3114`), which is not ported yet, so they carry no `@[hol]`
tag of their own.

The per-case lemmas at the end are the induction's step lemmas, proved for every
program form except the returning call, whose handler body is evaluated at a
smaller clock. The assembled theorem is still open.
-/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- Replacing the locals commutes with the rebuild.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem castCompiler_locals {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) :
    { castCompiler s t with locals := env } = castCompiler { s with locals := env } t := rfl

/-- Reading a local variable reads only the environment.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem getVar_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (name : Nat) :
    getVar name (castCompiler s t).locals = getVar name s.locals := rfl

/-- Reading several local variables reads only the environment.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem getVars_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : List Nat) :
    getVars names (castCompiler s t).locals = getVars names s.locals := rfl

/-- Writing a local variable commutes with the rebuild.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem setVar_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (name : Nat) (value : DataSem.Value) :
    setVar name value (castCompiler s t) = castCompiler (setVar name value s) t := rfl

/-- Writing several local variables commutes with the rebuild.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem setVars_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : List Nat) (values : List DataSem.Value) :
    setVars names values (castCompiler s t) = castCompiler (setVars names values s) t := rfl

/-- Clock decrement commutes with the rebuild.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem decClock_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    decClock (castCompiler s t) = castCompiler (decClock s) t := rfl

/-- Clock clamping commutes with the rebuild.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem fixClock_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (outcome : Option (Result (List DataSem.Value) DataSem.Value)) (mid : State C1 F) :
    fixClock (castCompiler s t) (outcome, castCompiler mid t) =
      (outcome, castCompiler (fixClock s (outcome, mid)).2 t) := rfl

/-- Clock clamping preserves agreement of the resulting states when the two
    clamping states agree on the clock as well.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem fixClock_agree_clocks {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (outcome : Option (Result (List DataSem.Value) DataSem.Value)) (mid : State C1 F)
    (other : State C2 F) (clocks : ccCoOnlyDiff s t) (agree : ccCoOnlyDiff mid other) :
    ccCoOnlyDiff (fixClock s (outcome, mid)).2 (fixClock t (outcome, other)).2 := by
  obtain ⟨l1, s1, k1, m1, f1, g1, h1, r1, c1, d1, i1, p1, t1, li1, sf1, pk1⟩ := clocks
  obtain ⟨l2, s2, k2, m2, f2, g2, h2, r2, c2, d2, i2, p2, t2, li2, sf2, pk2⟩ := agree
  simp only [fixClock, ccCoOnlyDiff]
  simp_all

/-- Clock clamping preserves agreement of the resulting states.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem fixClock_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (outcome : Option (Result (List DataSem.Value) DataSem.Value)) (mid : State C1 F)
    (other : State C2 F) (agree : ccCoOnlyDiff mid other) :
    ccCoOnlyDiff (fixClock s (outcome, mid)).2
      (fixClock (castCompiler s t) (outcome, other)).2 := by
  simp only [fixClock, ccCoOnlyDiff] at agree ⊢
  simp_all

/-- Flushing the locals commutes with the rebuild.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem flushState_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (all : Bool) :
    flushState all (castCompiler s t) = castCompiler (flushState all s) t := by
  cases all <;> rfl

/-- The installation safety update commutes with the rebuild.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem installSfs_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) :
    installSfs op (castCompiler s t) = castCompiler (installSfs op s) t := rfl

/-- Space allocation commutes with the rebuild.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem addSpace_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (amount : Nat) :
    addSpace (castCompiler s t) amount = castCompiler (addSpace s amount) t := rfl

/-- Cutting the local environment reads only the environment.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem cutEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : NumSet) :
    cutEnv names (castCompiler s t).locals = cutEnv names s.locals := rfl

/-- Cutting the local environment of the state commutes with the rebuild.
    Flapjack infrastructure toward the parked HOL theorem
    `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem cutState_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : NumSet) :
    cutState names (castCompiler s t) =
      (cutState names s).map (fun next => castCompiler next t) := by
  simp only [cutState]
  cases h : cutEnv names s.locals with
  | none => rfl
  | some env => rfl

/-- The optional environment cut commutes with the rebuild.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem cutStateOpt_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : Option NumSet) :
    cutStateOpt names (castCompiler s t) =
      (cutStateOpt names s).map (fun next => castCompiler next t) := by
  cases names with
  | none => rfl
  | some names => exact cutState_castCompiler s t names

/-- Exception unwinding commutes with the rebuild.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem jumpExc_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    jumpExc (castCompiler s t) =
      (jumpExc s).map (fun next => castCompiler next t) := by
  simp only [jumpExc]
  by_cases inside : s.handler < s.stack.length
  · simp only [inside, if_true]
    cases h : s.stack.drop (s.stack.length - (s.handler + 1)) with
    | nil => rfl
    | cons frame rest =>
      cases frame with
      | env size env => rfl
      | exc size env handler => rfl
  · simp [inside]

/-- Popping a frame commutes with the rebuild.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem popEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    popEnv (castCompiler s t) = (popEnv s).map (fun next => castCompiler next t) := by
  simp only [popEnv]
  cases h : s.stack with
  | nil => rfl
  | cons frame rest =>
    cases frame with
    | env size env => rfl
    | exc size env handler => rfl

/-- Entering a call commutes with the rebuild.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem callEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (args : List DataSem.Value) (size : Option Nat) :
    callEnv args size (castCompiler s t) = castCompiler (callEnv args size s) t := rfl

/-- Pushing an environment commutes with the rebuild.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem pushEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) (handler : Bool) :
    pushEnv env handler (castCompiler s t) = castCompiler (pushEnv env handler s) t := rfl

/-- Exception unwinding keeps the two states in agreement.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem jumpExc_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (s1 : State C1 F)
    (premises : ccCoOnlyDiff s t ∧ jumpExc s = some s1) :
    ∃ t1, jumpExc t = some t1 ∧ ccCoOnlyDiff s1 t1 := by
  obtain ⟨diff, run⟩ := premises
  rw [← (ccCoOnlyDiff_iff_castCompiler s t).1 diff, jumpExc_castCompiler, run]
  simp only [Option.map_some]
  exact ⟨castCompiler s1 t, rfl, ccCoOnlyDiff_castCompiler s1 t⟩

/-- The installation safety update only clears the flag for installation.
    Flapjack infrastructure toward the parked HOL theorem
    `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem installSfs_safeForSpace_of_ne {C F : Type} (op : ClosLang.Op) (state : State C F)
    (ne : op ≠ .install) : (installSfs op state).safeForSpace = state.safeForSpace := by
  cases op <;> simp_all [installSfs]

/-- Installing clears the safety flag.  Flapjack infrastructure toward the
    parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem installSfs_safeForSpace_install {C F : Type} (state : State C F) :
    (installSfs .install state).safeForSpace = false := by
  simp [installSfs]

/-- Flushing the locals never changes the safety flag.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem flushState_safeForSpace {C F : Type} (all : Bool) (state : State C F) :
    (flushState all state).safeForSpace = state.safeForSpace := by
  cases all <;> rfl

/-- Writing a local variable never changes the safety flag.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem setVar_safeForSpace {C F : Type} (name : Nat) (value : DataSem.Value)
    (state : State C F) : (setVar name value state).safeForSpace = state.safeForSpace := rfl

/-- Writing several local variables never changes the safety flag.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem setVars_safeForSpace {C F : Type} (names : List Nat) (values : List DataSem.Value)
    (state : State C F) :
    (setVars names values state).safeForSpace = state.safeForSpace := rfl

/-- Writing a local variable preserves agreement.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem setVar_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (name : Nat)
    (value : DataSem.Value) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (setVar name value s) (setVar name value t) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (setVar name value s) t

/-- Writing several local variables preserves agreement.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem setVars_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (names : List Nat)
    (values : List DataSem.Value) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (setVars names values s) (setVars names values t) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (setVars names values s) t

/-- Clock decrement preserves agreement.  Flapjack infrastructure toward the
    parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem decClock_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (diff : ccCoOnlyDiff s t) : ccCoOnlyDiff (decClock s) (decClock t) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (decClock s) t

/-- Flushing the locals preserves agreement.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem flushState_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (all : Bool)
    (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (flushState all s) (flushState all t) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  cases all
  · exact ccCoOnlyDiff_castCompiler (flushState false s) t
  · exact ccCoOnlyDiff_castCompiler (flushState true s) t

/-- The installation safety update preserves agreement.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem installSfs_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (installSfs op s) (installSfs op t) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  cases op <;> exact ccCoOnlyDiff_castCompiler (installSfs _ s) t

/-- Space allocation preserves agreement.  Flapjack infrastructure toward the
    parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem addSpace_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (amount : Nat)
    (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (addSpace s amount) (addSpace t amount) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (addSpace s amount) t

/-- Replacing the locals preserves agreement.  Flapjack infrastructure toward
    the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem localsUpdate_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff { s with locals := env } { t with locals := env } := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler { s with locals := env } t

/-- Entering a call preserves agreement.  Flapjack infrastructure toward the
    parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem callEnv_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (args : List DataSem.Value) (size : Option Nat) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (callEnv args size (decClock s)) (callEnv args size (decClock t)) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (callEnv args size (decClock s)) t

/-- Pushing an environment preserves agreement.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem pushEnv_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) (handler : Bool) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (pushEnv env handler (decClock s)) (pushEnv env handler (decClock t)) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (pushEnv env handler (decClock s)) t

/-- The property the evaluator induction establishes: a run at a safe state has
an agreeing run at any state agreeing on the sixteen compared fields. -/
private def CcCoOnlyDiffAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ (C' : Type) (target : State C' F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F),
    evaluate program state = (result, next) →
    next.safeForSpace = true →
    ccCoOnlyDiff state target →
    ∃ t1, evaluate program target = (result, t1) ∧ ccCoOnlyDiff next t1

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Skip case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_skip {C F : Type} (state : State C F) :
    CcCoOnlyDiffAt .skip state := by
  intro C' target result next run safe diff
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨target, by simp only [evaluate], diff⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Move case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_move {C F : Type} (dest src : Nat) (state : State C F) :
    CcCoOnlyDiffAt (.move dest src) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨setVar dest value target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, setVar]
    · exact setVar_agree state target dest value
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Assign case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (names : List Nat) (live : Option NumSet) (state : State C F) :
    CcCoOnlyDiffAt (.assign dest op names live) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  have same := (ccCoOnlyDiff_iff_castCompiler state target).1
    ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
      ffi, space, tstamps, limits, safeFlag, peak⟩
  by_cases namesReq : DataLang.opRequiresNames op == live.isNone
  · simp only [evaluate] at run ⊢
    rw [if_pos namesReq] at run ⊢
    simp only [typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, rfl, ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs,
      clock, code, ffi, space, tstamps, limits, safeFlag, peak⟩⟩
  · simp only [evaluate] at run ⊢
    rw [if_neg namesReq] at run ⊢
    cases read : getVars names state.locals with
    | none =>
      simp only [read, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [← locals, read, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | some values =>
      cases cut : cutStateOpt live state with
      | none =>
        simp only [read, cut, typeError, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have tCut : cutStateOpt live target = none := by
          rw [← same, cutStateOpt_castCompiler, cut]
          rfl
        refine ⟨target, ?_, ?_⟩
        · simp only [← locals, read, tCut, typeError]
        · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
            code, ffi, space, tstamps, limits, safeFlag, peak⟩
      | some middle =>
        obtain ⟨middleT, tCut, agreeMiddle⟩ := cutStateOpt_ccCoOnlyDiff state target live middle
          ⟨⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
            ffi, space, tstamps, limits, safeFlag, peak⟩, cut⟩
        cases appRun : doApp op values middle with
        | err error =>
          simp only [read, cut, appRun, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have ne : op ≠ .install := by
            intro eq
            rw [eq, flushState_safeForSpace, installSfs_safeForSpace_install] at safe
            exact absurd safe (by simp)
          have appT := doApp_ccCoOnlyDiff_rerr middle middleT op values error
            ⟨appRun, ne, agreeMiddle⟩
          refine ⟨flushState true (installSfs op middleT), ?_, ?_⟩
          · simp only [← locals, read, tCut, appT, installSfs]
          · exact flushState_agree (installSfs op middle) (installSfs op middleT) true
              (installSfs_agree middle middleT op agreeMiddle)
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [read, cut, appRun, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have ne : op ≠ .install := by
            intro eq
            rw [eq, setVar_safeForSpace, installSfs_safeForSpace_install] at safe
            exact absurd safe (by simp)
          have lastSafe : last.safeForSpace = true := by
            rw [setVar_safeForSpace, installSfs_safeForSpace_of_ne op last ne] at safe
            exact safe
          obtain ⟨lastT, appT, agreeLast⟩ := doApp_ccCoOnlyDiff_rval middle middleT op values value
            last ⟨appRun, lastSafe, agreeMiddle⟩
          refine ⟨setVar dest value (installSfs op lastT), ?_, ?_⟩
          · simp only [← locals, read, tCut, appT, setVar, installSfs]
          · exact setVar_agree (installSfs op last) (installSfs op lastT) dest value
              (installSfs_agree last lastT op agreeLast)

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Tick case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_tick {C F : Type} (state : State C F) :
    CcCoOnlyDiffAt .tick state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  by_cases zero : state.clock = 0
  · simp only [evaluate] at run ⊢
    rw [if_pos zero] at run
    rw [← clock] at ⊢
    rw [if_pos zero] at ⊢
    simp only [timeoutError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState true target, ?_, ?_⟩
    · simp only [timeoutError]
    · exact flushState_agree state target true
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩
  · simp only [evaluate] at run ⊢
    rw [if_neg zero] at run
    rw [← clock] at ⊢
    rw [if_neg zero] at ⊢
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨decClock target, ?_, ?_⟩
    · rfl
    · exact decClock_agree state target
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (MakeSpace case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : CcCoOnlyDiffAt (.makeSpace amount names) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, cut, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    have tCut : cutEnv names target.locals = some env := by
      rw [← locals]
      exact cut
    refine ⟨addSpace { target with locals := env } amount, ?_, ?_⟩
    · rw [evaluate, tCut]
    · exact addSpace_agree { state with locals := env } { target with locals := env } amount
        (localsUpdate_agree state target env
          ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
            ffi, space, tstamps, limits, safeFlag, peak⟩)

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Raise case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_raise {C F : Type} (name : Nat) (state : State C F) :
    CcCoOnlyDiffAt (.raise name) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  have same := (ccCoOnlyDiff_iff_castCompiler state target).1
    ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
      ffi, space, tstamps, limits, safeFlag, peak⟩
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some value =>
    cases exc : jumpExc state with
    | none =>
      simp only [evaluate, read, exc, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have tExc : jumpExc target = none := by
        rw [← same, jumpExc_castCompiler, exc]
        rfl
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, read, tExc, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | some next0 =>
      simp only [evaluate, read, exc, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨targetNext, tExc, agreeNext⟩ := jumpExc_agree state target next0
        ⟨⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩, exc⟩
      exact ⟨targetNext, by simp only [evaluate, ← locals, read, tExc], agreeNext⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Return case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_return {C F : Type} (names : List Nat) (state : State C F) :
    CcCoOnlyDiffAt (.return names) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some values =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState false target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, flushState]
    · exact flushState_agree state target false
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (Seq case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_seq {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (firstIH : CcCoOnlyDiffAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → CcCoOnlyDiffAt second mid) :
    CcCoOnlyDiffAt (.seq first second) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  have same := (ccCoOnlyDiff_iff_castCompiler state target).1
    ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
      ffi, space, tstamps, limits, safeFlag, peak⟩
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    simp only [evaluate, firstRun, fixClock] at run
    cases outcome with
    | none =>
      have secondRun : evaluate second { mid with clock := min state.clock mid.clock } =
          (result, next) := by
        simpa only [fixClock] using run
      have midSafe : mid.safeForSpace = true := by
        have clamped := evaluate_safety_of_result second
          { mid with clock := min state.clock mid.clock } result next ⟨secondRun, safe⟩
        simpa using clamped
      obtain ⟨t1, tFirst, agreeMid⟩ := firstIH C' target none mid firstRun midSafe
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩
      have agreeFix := fixClock_agree state target none mid t1 agreeMid
      rw [same] at agreeFix
      have bound : ({ mid with clock := min state.clock mid.clock } : State C F).clock ≤
          state.clock := by
        simp only
        omega
      obtain ⟨t2, tSecond, agreeNext⟩ := secondIH _ bound C'
        (fixClock target (none, t1)).2 result next secondRun safe agreeFix
      refine ⟨t2, ?_, agreeNext⟩
      simp only [evaluate, tFirst, fixClock]
      exact tSecond
    | some stopped =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have midSafe : mid.safeForSpace = true := by
        simpa using safe
      obtain ⟨t1, tFirst, agreeMid⟩ := firstIH C' target (some stopped) mid firstRun midSafe
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩
      have agreeFix := fixClock_agree state target (some stopped) mid t1 agreeMid
      rw [same] at agreeFix
      exact ⟨(fixClock target (some stopped, t1)).2,
        by simp only [evaluate, tFirst, fixClock], agreeFix⟩

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (If case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : CcCoOnlyDiffAt yes state) (noIH : CcCoOnlyDiffAt no state) :
    CcCoOnlyDiffAt (.ifThenElse name yes no) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some value =>
    by_cases yesValue : isBool true value
    · simp only [evaluate, ← locals, read] at run ⊢
      rw [if_pos yesValue] at run ⊢
      exact yesIH C' target result next run safe
        ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
          ffi, space, tstamps, limits, safeFlag, peak⟩
    · by_cases noValue : isBool false value
      · simp only [evaluate, ← locals, read] at run ⊢
        rw [if_neg yesValue, if_pos noValue] at run ⊢
        exact noIH C' target result next run safe
          ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
            ffi, space, tstamps, limits, safeFlag, peak⟩
      · simp only [evaluate, ← locals, read] at run ⊢
        rw [if_neg yesValue, if_neg noValue] at run ⊢
        simp only [typeError, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · rfl
        · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
            code, ffi, space, tstamps, limits, safeFlag, peak⟩

/-- Clearing the stack and locals preserves agreement.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem stackClear_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff { s with stack := [], locals := .ln } { t with stack := [], locals := .ln } := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler { s with stack := [], locals := .ln } t

/-- Entering a call through a pushed environment preserves agreement.
    Flapjack infrastructure toward the parked HOL theorem
    `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem callEnvPush_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (args : List DataSem.Value) (size : Option Nat) (env : Spt DataSem.Value)
    (handler : Bool) (diff : ccCoOnlyDiff s t) :
    ccCoOnlyDiff (callEnv args size (pushEnv env handler (decClock s)))
      (callEnv args size (pushEnv env handler (decClock t))) := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  exact ccCoOnlyDiff_castCompiler (callEnv args size (pushEnv env handler (decClock s))) t

/-- Popping a frame never changes the safety flag.  Flapjack infrastructure
    toward the parked HOL theorem `evaluate_cc_co_only_diff`; no separate HOL original. -/
theorem popEnv_safeForSpace {C F : Type} (state next : State C F)
    (run : popEnv state = some next) : next.safeForSpace = state.safeForSpace := by
  cases frames : state.stack with
  | nil => simp [popEnv, frames] at run
  | cons frame rest =>
    cases frame with
    | env size env =>
      simp only [popEnv, frames, Option.some.injEq] at run
      rw [← run]
    | exc size env handler =>
      simp only [popEnv, frames, Option.some.injEq] at run
      rw [← run]

/-- A stackless source frame means the target is stackless too.  Flapjack
    infrastructure toward the parked HOL theorem `evaluate_cc_co_only_diff`;
    no separate HOL original. -/
theorem popEnv_none_of_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (diff : ccCoOnlyDiff s t) (run : popEnv s = none) : popEnv t = none := by
  have same := (ccCoOnlyDiff_iff_castCompiler s t).1 diff
  rw [← same]
  cases frames : s.stack with
  | nil => simp [popEnv, frames]
  | cons frame rest =>
    cases frame with
    | env size env =>
      simp only [popEnv, frames] at run
      simp_all
    | exc size env handler =>
      simp only [popEnv, frames] at run
      simp_all

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (tail-call Force case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_tailForce {C F : Type} (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → CcCoOnlyDiffAt body called) :
    CcCoOnlyDiffAt (.force none label src) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← refs, read, th, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← refs, read, th, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp only [evaluate, read, th, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨flushState false target, ?_, ?_⟩
        · simp only [evaluate, ← locals, ← refs, read, th, flushState]
        · exact flushState_agree state target false
            ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
              ffi, space, tstamps, limits, safeFlag, peak⟩
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨target, ?_, ?_⟩
          · simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found, typeError]
          · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
              code, ffi, space, tstamps, limits, safeFlag, peak⟩
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          by_cases zero : state.clock = 0
          · simp only [evaluate, read, th, found] at run
            rw [if_pos zero] at run
            simp only [timeoutError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ target with stack := [], locals := .ln }, ?_, ?_⟩
            · simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found]
              rw [← clock]
              rw [if_pos zero]
              simp only [timeoutError]
            · exact stackClear_agree state target
                ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                  code, ffi, space, tstamps, limits, safeFlag, peak⟩
          · let called := callEnv args size (decClock state)
            have clockLt : called.clock < state.clock := by
              simp [called, callEnv, decClock]
              omega
            let targetCalled := callEnv args size (decClock target)
            have agreeCalled : ccCoOnlyDiff called targetCalled := by
              simp only [called, targetCalled]
              exact callEnv_agree state target args size
                ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                  code, ffi, space, tstamps, limits, safeFlag, peak⟩
            generalize bodyRun : evaluate body called = res
            obtain ⟨outcome, last⟩ := res
            simp only [evaluate, read, th, found] at run
            rw [if_neg zero] at run
            rw [bodyRun] at run
            cases outcome with
            | none =>
              simp only [typeError, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨t1, tRun, tAgree⟩ := bodyIH body called clockLt C' targetCalled none last
                bodyRun safe agreeCalled
              refine ⟨t1, ?_, tAgree⟩
              simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found]
              rw [← clock]
              rw [if_neg zero]
              simp only [targetCalled, tRun, typeError]
            | some value =>
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨t1, tRun, tAgree⟩ := bodyIH body called clockLt C' targetCalled
                (some value) last bodyRun safe agreeCalled
              refine ⟨t1, ?_, tAgree⟩
              simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found]
              rw [← clock]
              rw [if_neg zero]
              simp only [targetCalled, tRun]
/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (returning-call Force case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_returningForce {C F : Type} (dest : Nat) (live : NumSet)
    (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → CcCoOnlyDiffAt body called) :
    CcCoOnlyDiffAt (.force (some (dest, live)) label src) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← refs, read, th, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← refs, read, th, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, read, th, cut, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨target, ?_, ?_⟩
          · simp only [evaluate, ← locals, ← refs, read, th, cut, typeError]
          · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
              code, ffi, space, tstamps, limits, safeFlag, peak⟩
        | some env =>
          simp only [evaluate, read, th, cut, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have tCut : cutEnv live target.locals = some env := by
            rw [← locals]
            exact cut
          refine ⟨setVar dest value { target with locals := env }, ?_, ?_⟩
          · simp only [evaluate, ← locals, ← refs, read, th, cut, setVar]
          · exact setVar_agree { state with locals := env } { target with locals := env } dest value
              (localsUpdate_agree state target env
                ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                  code, ffi, space, tstamps, limits, safeFlag, peak⟩)
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨target, ?_, ?_⟩
          · simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found, typeError]
          · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
              code, ffi, space, tstamps, limits, safeFlag, peak⟩
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          cases cut : cutEnv live state.locals with
          | none =>
            simp only [evaluate, read, th, found, cut, typeError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨target, ?_, ?_⟩
            · simp only [evaluate, ← locals, ← refs, ← code, ← frameSizes, read, th, found, cut,
                typeError]
            · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs,
                clock, code, ffi, space, tstamps, limits, safeFlag, peak⟩
          | some env =>
            let callState := callEnv args size (pushEnv env false (decClock state))
            let targetCallState := callEnv args size (pushEnv env false (decClock target))
            have agreeCall : ccCoOnlyDiff callState targetCallState := by
              simp only [callState, targetCallState]
              exact callEnvPush_agree state target args size env false
                ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                  code, ffi, space, tstamps, limits, safeFlag, peak⟩
            by_cases zero : state.clock = 0
            · simp only [evaluate, read, th, found, cut] at run
              rw [if_pos zero] at run
              simp only [timeoutError, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨{ targetCallState with stack := [], locals := .ln }, ?_, ?_⟩
              · simp only [evaluate, targetCallState, ← locals]
                rw [cut]
                simp only [← refs, ← code, ← frameSizes, read, th, found]
                rw [← clock]
                rw [if_pos zero]
                simp only [timeoutError]
              · exact stackClear_agree callState targetCallState agreeCall
            · have clockLt : callState.clock < state.clock := by
                simp [callState, callEnv, pushEnv, decClock]
                omega
              cases called : fixClock callState (evaluate body callState) with
              | mk outcome last =>
                have bodyRun : evaluate body callState = (outcome, last) := by
                  simpa [fixClock_evaluate] using called
                simp only [callState] at called bodyRun
                simp only [bodyRun] at called
                simp only [evaluate, read, th, found, cut] at run
                rw [if_neg zero] at run
                simp only [bodyRun, called] at run
                cases outcome with
                | none =>
                  simp only [typeError, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run
                  obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C' targetCallState none
                    last bodyRun safe agreeCall
                  have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                      (none, t1) := by
                    rw [fixClock_evaluate, tRun]
                  refine ⟨t1, ?_, tAgree⟩
                  simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read, th,
                    found]
                  rw [← clock]
                  rw [if_neg zero]
                  simp only [targetCallState, clampedT, typeError]
                | some stopped =>
                  cases stopped with
                  | err error =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C' targetCallState
                      (some (.err error)) last bodyRun safe agreeCall
                    have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                        (some (.err error), t1) := by
                      rw [fixClock_evaluate, tRun]
                    refine ⟨t1, ?_, tAgree⟩
                    simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read, th,
                      found]
                    rw [← clock]
                    rw [if_neg zero]
                    simp only [targetCallState, clampedT]
                  | val values =>
                    cases values with
                    | nil =>
                      simp only [typeError, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                        targetCallState (some (.val [])) last bodyRun safe agreeCall
                      have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                          (some (.val []), t1) := by
                        rw [fixClock_evaluate, tRun]
                      refine ⟨t1, ?_, tAgree⟩
                      simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read, th,
                        found]
                      rw [← clock]
                      rw [if_neg zero]
                      simp only [targetCallState, clampedT, typeError]
                    | cons head tail =>
                      cases tail with
                      | cons second rest =>
                        simp only [typeError, Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                          targetCallState (some (.val (head :: second :: rest))) last bodyRun safe
                          agreeCall
                        have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                            (some (.val (head :: second :: rest)), t1) := by
                          rw [fixClock_evaluate, tRun]
                        refine ⟨t1, ?_, tAgree⟩
                        simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read,
                          th, found]
                        rw [← clock]
                        rw [if_neg zero]
                        simp only [targetCallState, clampedT, typeError]
                      | nil =>
                        cases pop : popEnv last with
                        | none =>
                          simp only [pop, typeError, Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                            targetCallState (some (.val [head])) last bodyRun safe agreeCall
                          have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                              (some (.val [head]), t1) := by
                            rw [fixClock_evaluate, tRun]
                          have tPop : popEnv t1 = none := popEnv_none_of_agree last t1 tAgree pop
                          refine ⟨t1, ?_, tAgree⟩
                          simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read,
                            th, found]
                          rw [← clock]
                          rw [if_neg zero]
                          simp only [targetCallState, clampedT, tPop, typeError]
                        | some popped =>
                          simp only [pop, Prod.mk.injEq] at run
                          obtain ⟨rfl, rfl⟩ := run
                          have nextSafe : popped.safeForSpace = true := by
                            rw [setVar_safeForSpace] at safe
                            exact safe
                          have lastSafe : last.safeForSpace = true := by
                            rw [popEnv_safeForSpace last popped pop] at nextSafe
                            exact nextSafe
                          obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                            targetCallState (some (.val [head])) last bodyRun lastSafe agreeCall
                          have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                              (some (.val [head]), t1) := by
                            rw [fixClock_evaluate, tRun]
                          obtain ⟨t2, tPop, agreePopped⟩ := popEnv_ccCoOnlyDiff last t1 popped
                            ⟨tAgree, pop⟩
                          refine ⟨setVar dest head t2, ?_, ?_⟩
                          · simp only [evaluate, ← locals, cut, ← refs, ← code, ← frameSizes, read,
                              th, found]
                            rw [← clock]
                            rw [if_neg zero]
                            simp only [targetCallState, clampedT, tPop, setVar]
                          · exact setVar_agree popped t2 dest head agreePopped

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (tail-call case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_tailCall {C F : Type} (dest : Option Nat) (names : List Nat)
    (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → CcCoOnlyDiffAt body called) :
    CcCoOnlyDiffAt (.call none dest names handler) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, read, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← code, ← frameSizes, read, found, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      cases handler with
      | some h =>
        obtain ⟨hname, hbody⟩ := h
        simp [evaluate, read, found] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · simp [evaluate, ← locals, ← code, ← frameSizes, read, found]
        · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
            code, ffi, space, tstamps, limits, safeFlag, peak⟩
      | none =>
        by_cases zero : state.clock = 0
        · simp [evaluate, read, found, zero] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨flushState true target, ?_, ?_⟩
          · simp [evaluate, ← locals, ← code, ← frameSizes, read, found, ← clock, zero]
          · exact flushState_agree state target true
              ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                code, ffi, space, tstamps, limits, safeFlag, peak⟩
        · let called := callEnv args size (decClock state)
          have clockLt : called.clock < state.clock := by
            simp [called, callEnv, decClock]
            omega
          let targetCalled := callEnv args size (decClock target)
          have agreeCalled : ccCoOnlyDiff called targetCalled := by
            simp only [called, targetCalled]
            exact callEnv_agree state target args size
              ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                code, ffi, space, tstamps, limits, safeFlag, peak⟩
          cases calledRun : evaluate body called with
          | mk outcome last =>
            simp only [called] at calledRun
            simp [evaluate, read, found, zero] at run
            simp only [calledRun] at run
            cases outcome with
            | none =>
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨t1, tRun, tAgree⟩ := bodyIH body called clockLt C' targetCalled none last
                calledRun safe agreeCalled
              refine ⟨t1, ?_, tAgree⟩
              simp [evaluate, ← locals, ← code, ← frameSizes, read, found, ← clock, zero,
                targetCalled, tRun, typeError]
            | some value =>
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              obtain ⟨t1, tRun, tAgree⟩ := bodyIH body called clockLt C' targetCalled
                (some value) last calledRun safe agreeCalled
              refine ⟨t1, ?_, tAgree⟩
              simp [evaluate, ← locals, ← code, ← frameSizes, read, found, ← clock, zero,
                targetCalled, tRun]

/-- Flapjack infrastructure toward the parked HOL `evaluate_cc_co_only_diff`
    (returning-call case); no separate HOL original. -/
private theorem ccCoOnlyDiffAt_returningCall {C F : Type} (returns : List Nat) (live : NumSet)
    (dest : Option Nat) (names : List Nat) (handler : Option (Nat × DataLang.Prog))
    (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → CcCoOnlyDiffAt body called) :
    CcCoOnlyDiffAt (.call (some (returns, live)) dest names handler) state := by
  intro C' target result next run safe diff
  obtain ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
    ffi, space, tstamps, limits, safeFlag, peak⟩ := diff
  cases read : getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨target, ?_, ?_⟩
    · simp only [evaluate, ← locals, read, typeError]
    · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock, code,
        ffi, space, tstamps, limits, safeFlag, peak⟩
  | some values =>
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, read, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨target, ?_, ?_⟩
      · simp only [evaluate, ← locals, ← code, ← frameSizes, read, found, typeError]
      · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
          code, ffi, space, tstamps, limits, safeFlag, peak⟩
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, read, found, cut] at run
          rw [if_neg (by simp [distinct])] at run
          simp only [typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨target, ?_, ?_⟩
          · simp only [evaluate, ← locals, ← code, ← frameSizes, read, found, cut, typeError]
            rw [if_neg (by simp [distinct])]
          · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
              code, ffi, space, tstamps, limits, safeFlag, peak⟩
        | some env =>
          let callState := callEnv args size (pushEnv env handler.isSome (decClock state))
          let targetCallState := callEnv args size (pushEnv env handler.isSome (decClock target))
          have agreeCall : ccCoOnlyDiff callState targetCallState := by
            simp only [callState, targetCallState]
            exact callEnvPush_agree state target args size env handler.isSome
              ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
                code, ffi, space, tstamps, limits, safeFlag, peak⟩
          by_cases zero : state.clock = 0
          · simp only [evaluate, read, found, cut] at run
            rw [if_neg (by simp [distinct])] at run
            rw [if_pos zero] at run
            simp only [timeoutError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨{ targetCallState with stack := [], locals := .ln }, ?_, ?_⟩
            · simp only [evaluate, targetCallState, ← locals, ← code, ← frameSizes]
              rw [cut]
              simp only [read, found]
              rw [if_neg (by simp [distinct])]
              rw [← clock]
              rw [if_pos zero]
              simp only [timeoutError]
            · exact stackClear_agree callState targetCallState agreeCall
          · have clockLt : callState.clock < state.clock := by
              simp [callState, callEnv, pushEnv, decClock]
              omega
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              have lastClock : last.clock < state.clock := by
                have bound := evaluate_clock_le body callState
                rw [bodyRun] at bound
                change last.clock ≤ callState.clock at bound
                omega
              simp only [evaluate, read, found, cut] at run
              rw [if_neg (by simp [distinct])] at run
              rw [if_neg zero] at run
              simp only [fixClock_evaluate] at run
              simp only [callState] at bodyRun
              rw [bodyRun] at run
              cases outcome with
              | none =>
                simp only [typeError, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C' targetCallState none
                  last bodyRun safe agreeCall
                have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                    (none, t1) := by
                  rw [fixClock_evaluate, tRun]
                refine ⟨t1, ?_, tAgree⟩
                simp only [evaluate, ← locals, ← code, ← frameSizes]
                rw [cut]
                simp only [read, found]
                rw [if_neg (by simp [distinct])]
                rw [← clock]
                rw [if_neg zero]
                simp only [targetCallState, clampedT, typeError]
              | some stopped =>
                cases stopped with
                | val returned =>
                  by_cases lengthEq : returned.length = returns.length
                  · cases pop : popEnv last with
                    | none =>
                      simp only [if_pos lengthEq, pop, typeError, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                        targetCallState (some (.val returned)) last bodyRun safe agreeCall
                      have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                          (some (.val returned), t1) := by
                        rw [fixClock_evaluate, tRun]
                      have tPop : popEnv t1 = none := popEnv_none_of_agree last t1 tAgree pop
                      refine ⟨t1, ?_, tAgree⟩
                      simp only [evaluate, ← locals, ← code, ← frameSizes]
                      rw [cut]
                      simp only [read, found]
                      rw [if_neg (by simp [distinct])]
                      rw [← clock]
                      rw [if_neg zero]
                      simp only [targetCallState, clampedT, if_pos lengthEq, tPop, typeError]
                    | some popped =>
                      simp only [if_pos lengthEq, pop, Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have nextSafe : popped.safeForSpace = true := by
                        rw [setVars_safeForSpace] at safe
                        exact safe
                      have lastSafe : last.safeForSpace = true := by
                        rw [popEnv_safeForSpace last popped pop] at nextSafe
                        exact nextSafe
                      obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                        targetCallState (some (.val returned)) last bodyRun lastSafe agreeCall
                      have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                          (some (.val returned), t1) := by
                        rw [fixClock_evaluate, tRun]
                      obtain ⟨t2, tPop, agreePopped⟩ :=
                        popEnv_ccCoOnlyDiff last t1 popped ⟨tAgree, pop⟩
                      refine ⟨setVars returns returned t2, ?_, ?_⟩
                      · simp only [evaluate, ← locals, ← code, ← frameSizes]
                        rw [cut]
                        simp only [read, found]
                        rw [if_neg (by simp [distinct])]
                        rw [← clock]
                        rw [if_neg zero]
                        simp only [targetCallState, clampedT, if_pos lengthEq, tPop, setVars]
                      · exact setVars_agree popped t2 returns returned agreePopped
                  · simp only [if_neg lengthEq, typeError, Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                      targetCallState (some (.val returned)) last bodyRun safe agreeCall
                    have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                        (some (.val returned), t1) := by
                      rw [fixClock_evaluate, tRun]
                    refine ⟨t1, ?_, tAgree⟩
                    simp only [evaluate, ← locals, ← code, ← frameSizes]
                    rw [cut]
                    simp only [read, found]
                    rw [if_neg (by simp [distinct])]
                    rw [← clock]
                    rw [if_neg zero]
                    simp only [targetCallState, clampedT, if_neg lengthEq, typeError]
                | err error =>
                  cases error with
                  | abort reason =>
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                      targetCallState (some (.err (.abort reason))) last bodyRun safe agreeCall
                    have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                        (some (.err (.abort reason)), t1) := by
                      rw [fixClock_evaluate, tRun]
                    refine ⟨t1, ?_, tAgree⟩
                    simp only [evaluate, ← locals, ← code, ← frameSizes]
                    rw [cut]
                    simp only [read, found]
                    rw [if_neg (by simp [distinct])]
                    rw [← clock]
                    rw [if_neg zero]
                    simp only [targetCallState, clampedT]
                  | raise value =>
                    cases handler with
                    | none =>
                      simp only [Prod.mk.injEq] at run
                      obtain ⟨rfl, rfl⟩ := run
                      obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                        targetCallState (some (.err (.raise value))) last bodyRun safe agreeCall
                      have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                          (some (.err (.raise value)), t1) := by
                        rw [fixClock_evaluate, tRun]
                      refine ⟨t1, ?_, tAgree⟩
                      simp only [evaluate, ← locals, ← code, ← frameSizes]
                      rw [cut]
                      simp only [read, found]
                      rw [if_neg (by simp [distinct])]
                      rw [← clock]
                      rw [if_neg zero]
                      simp only [targetCallState, clampedT]
                    | some entry =>
                      obtain ⟨hname, hbody⟩ := entry
                      have handlerRun : evaluate hbody (setVar hname value last) =
                          (result, next) := by
                        simpa using run
                      have enteredSafe : (setVar hname value last).safeForSpace = true := by
                        exact evaluate_safety_of_result hbody (setVar hname value last) result next
                          ⟨handlerRun, safe⟩
                      have lastSafe : last.safeForSpace = true := by
                        simpa [setVar] using enteredSafe
                      obtain ⟨t1, tRun, tAgree⟩ := bodyIH body callState clockLt C'
                        targetCallState (some (.err (.raise value))) last bodyRun lastSafe agreeCall
                      have clampedT : fixClock targetCallState (evaluate body targetCallState) =
                          (some (.err (.raise value)), t1) := by
                        rw [fixClock_evaluate, tRun]
                      have enteredLt : (setVar hname value last).clock < state.clock := by
                        simpa [setVar] using lastClock
                      obtain ⟨t2, tRun2, tAgree2⟩ := bodyIH hbody (setVar hname value last)
                        enteredLt C' (setVar hname value t1) result next handlerRun safe
                        (setVar_agree last t1 hname value tAgree)
                      refine ⟨t2, ?_, tAgree2⟩
                      simp only [evaluate, ← locals, ← code, ← frameSizes]
                      rw [cut]
                      simp only [read, found]
                      rw [if_neg (by simp [distinct])]
                      rw [← clock]
                      rw [if_neg zero]
                      simp only [targetCallState, clampedT, tRun2]
      · simp only [evaluate, read, found] at run
        rw [if_pos (by simp [distinct])] at run
        simp only [typeError, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨target, ?_, ?_⟩
        · simp only [evaluate, ← locals, ← code, ← frameSizes, read, found, typeError]
          rw [if_pos (by simp [distinct])]
        · exact ⟨locals, localsSize, stack, stackMax, frameSizes, global, handlerEq, refs, clock,
            code, ffi, space, tstamps, limits, safeFlag, peak⟩

/-- The evaluator's own induction establishes `CcCoOnlyDiffAt` for every
    program.  Flapjack infrastructure toward the parked HOL theorem
    `evaluate_cc_co_only_diff`; no separate HOL original. -/
private theorem ccCoOnlyDiffAt_all {C F : Type} (program : DataLang.Prog) (state : State C F) :
    CcCoOnlyDiffAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => CcCoOnlyDiffAt program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact ccCoOnlyDiffAt_skip state
  | move dest src => exact ccCoOnlyDiffAt_move dest src state
  | assign dest op names live => exact ccCoOnlyDiffAt_assign dest op names live state
  | tick => exact ccCoOnlyDiffAt_tick state
  | makeSpace amount names => exact ccCoOnlyDiffAt_makeSpace amount names state
  | raise name => exact ccCoOnlyDiffAt_raise name state
  | «return» names => exact ccCoOnlyDiffAt_return names state
  | seq first second =>
    apply ccCoOnlyDiffAt_seq first second state
    · exact exprIH first state (by omega)
        (by simp only [DataLang.Prog.seq.sizeOf_spec]; omega)
    · intro mid bound
      exact exprIH second mid bound
        (by simp only [DataLang.Prog.seq.sizeOf_spec]; omega)
  | ifThenElse name yes no =>
    apply ccCoOnlyDiffAt_if name yes no state
    · exact exprIH yes state (by omega)
        (by simp only [DataLang.Prog.ifThenElse.sizeOf_spec]; omega)
    · exact exprIH no state (by omega)
        (by simp only [DataLang.Prog.ifThenElse.sizeOf_spec]; omega)
  | force ret label src =>
    cases ret with
    | none => exact ccCoOnlyDiffAt_tailForce label src state smaller
    | some ret =>
      obtain ⟨dest, live⟩ := ret
      exact ccCoOnlyDiffAt_returningForce dest live label src state smaller
  | call ret dest names handler =>
    cases ret with
    | none => exact ccCoOnlyDiffAt_tailCall dest names handler state smaller
    | some ret =>
      obtain ⟨returns, live⟩ := ret
      exact ccCoOnlyDiffAt_returningCall returns live dest names handler state smaller

/-- Evaluation at a rebuilt compiler configuration mirrors evaluation at the
    original one, and the two result states still agree on the sixteen compared
    fields. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_cc_co_only_diff"]
theorem evaluate_cc_co_only_diff {C1 C2 F : Type} (prog : DataLang.Prog) (s : State C1 F)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (s1 : State C1 F) (t : State C2 F)
    (premises : evaluate prog s = (res, s1) ∧ s1.safeForSpace = true ∧ ccCoOnlyDiff s t) :
    ∃ t1, evaluate prog t = (res, t1) ∧ ccCoOnlyDiff s1 t1 := by
  obtain ⟨run, safe, diff⟩ := premises
  exact ccCoOnlyDiffAt_all prog s C2 t res s1 run safe diff

end Flapjack.Compiler.Backend.DataProps
