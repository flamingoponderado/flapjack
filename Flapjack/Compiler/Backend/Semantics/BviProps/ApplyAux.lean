module

public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyClockEvents
public import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyError
public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame
public import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyCode
public import Flapjack.Compiler.Backend.WordElim.Proofs.Locations
public import Flapjack.HolRef

@[expose] public section

/-!
# BVI-specific primitive results: clock, trace, errors and code

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:462-513`:
`do_app_err`, `do_app_aux_const`, `do_app_with_code`, `do_app_with_code_err`,
`do_app_aux_with_clock` and `do_app_aux_io_events_mono`. Each keeps HOL's
binder order and single-premise shape; the underlying facts are the untagged
BVI dispatcher lemmas in the neighbouring modules.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.WordElim
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace ApplyAuxCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BviSem.BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ApplyAuxCarrier

/-- Handled BVI primitives leave the clock unchanged. -/
theorem doAppAux_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t))) : t.clock = s.clock := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Handled BVI primitives leave the FFI state untouched, so they cannot
shrink the I/O-event trace. -/
theorem doAppAux_ioEvents_prefix {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s t : BviState C F) (value : Value)
    (run : doAppAux op args s = some (some (value, t))) : s.ffi.ioEvents <+: t.ffi.ioEvents := by
  rw [doAppAux_ffi op args s t value run]

/-- Replacing the clock in a handled BVI primitive result follows the source
`OPTION_MAP` composition. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_aux_with_clock"
  (fmap_as_finite_support := [refs])]
theorem doAppAux_with_clock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (clock : Nat) :
    doAppAux op args { state with clock := clock } =
      Option.map (Option.map (fun (x, y) => (x, { y with clock := clock })))
        (doAppAux op args state) := by
  simpa [setClockAux] using doAppAux_setClock op args state clock

/-- A handled BVI primitive result extends the I/O-event trace. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_aux_io_events_mono"
  (fmap_as_finite_support := [refs])]
theorem doAppAux_io_events_mono {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (value : Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : doAppAux op args state = some (some (value, next))) :
    state.ffi.ioEvents <+: next.ffi.ioEvents :=
  doAppAux_ioEvents_prefix op args state next value run

/-- A handled BVI primitive result keeps the incoming clock. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_aux_const"
  (fmap_as_finite_support := [refs])]
theorem doAppAux_const {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (value : Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (run : doAppAux op args state = some (some (value, next))) :
    next.clock = state.clock :=
  doAppAux_clock op args state next value run

/-- A BVI primitive error is a type error or an FFI error. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_err"
  (fmap_as_finite_support := [refs])]
theorem doApp_err {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (error : ErrorResult ExnOrRet) (run : doApp op args state = .err error) :
    error = .abort .typeError ∨
      ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) := by
  simp only [doApp] at run
  split at run
  · unfold doInstall at run
    repeat' split at run
    all_goals simp_all
    all_goals split at run
    all_goals simp_all
  · simp only [doAppFallback] at run
    cases aux : doAppAux op args state with
    | none =>
      simp [aux] at run
      exact Or.inl run.symm
    | some inner =>
      cases inner with
      | some pair =>
        simp [aux] at run
      | none =>
        simp only [aux] at run
        cases fallback : BvlSem.doApp op args (toBvl state) with
        | val pair => simp [fallback] at run
        | err error' =>
          have classified := BvlProps.doAppError op args (toBvl state) error' fallback
          rcases classified with typeErr | ⟨name, outcome, opEq, errEq⟩
          · simp [fallback, typeErr] at run
            exact Or.inl run.symm
          · simp [fallback, errEq] at run
            exact Or.inr ⟨name, outcome, opEq, run.symm⟩

/-- Flapjack helper: building the BVL fallback state commutes with replacing
code, because every payload is the single arbitrary BVL expression. -/
theorem toBvl_setCode {C F : Type} (state : BviState C F) (code : Spt (Nat × Bvi.Exp)) :
    toBvl { state with code := code } =
      { toBvl state with
        code := sptMap
          (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code } := by
  simp [toBvl]

/-- Flapjack helper: copying the shared fields back commutes with code
replacement. -/
theorem fromBvl_setCode {C F : Type} (source : BvlSem.State C F) (state : BviState C F)
    (code : Spt (Nat × Bvi.Exp)) :
    fromBvl source { state with code := code } = { fromBvl source state with code := code } := by
  cases source
  cases state
  rfl

/-- Flapjack helper: the runtime frame built from a code replacement is that
same replacement. -/
theorem runtimeFrame_setCode {C F : Type} (state : BviState C F)
    (code : Spt (Nat × Bvi.Exp)) :
    runtimeFrame state { state with code := code } = { state with code := code } := by
  cases state
  rfl

/-- Flapjack helper: a handled result is preserved when the incoming code tree
is extended. -/
theorem doAppAux_setCode_of_run {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value) (code : Spt (Nat × Bvi.Exp))
    (run : doAppAux op args state = some (some (value, next)))
    (growth : sptDomainSet state.code ⊆ sptDomainSet code) :
    doAppAux op args { state with code := code } =
      some (some (value, { next with code := code })) := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | cons arg rest => simp [doAppAux] at run
    | nil =>
      simp only [doAppAux] at run ⊢
      split at run
      · rename_i found
        simp at run
        obtain ⟨rfl, rfl⟩ := run
        have present : (sptLookup name code).isSome = true := by
          apply growth
          show (sptLookup name state.code).isSome = true
          exact found
        simp [present]
      · simp_all
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args state { state with code := code }
      (Or.inr notLabel)
    have fields := doAppAux_compiler_fields op args state next value run
    rw [← runtimeFrame_setCode state code]
    rw [frame, run]
    simp only [Option.map_some]
    simp [runtimeFrame, fields.1, fields.2.1]

/-- Flapjack helper: an unhandled operation stays unhandled when the
replacement code tree is contained in the incoming one. -/
theorem doAppAux_setCode_none {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (code : Spt (Nat × Bvi.Exp))
    (run : doAppAux op args state = none)
    (shrink : sptDomainSet code ⊆ sptDomainSet state.code) :
    doAppAux op args { state with code := code } = none := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | cons arg rest => simp [doAppAux]
    | nil =>
      simp only [doAppAux] at run ⊢
      split at run
      · simp_all
      · rename_i missing
        split
        · rename_i newFound
          have present : (sptLookup name state.code).isSome = true := by
            apply shrink
            show (sptLookup name code).isSome = true
            exact newFound
          simp [missing] at present
        · rfl
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args state { state with code := code }
      (Or.inr notLabel)
    rw [← runtimeFrame_setCode state code]
    rw [frame, run]
    rfl

/-- Flapjack helper: a delegated operation stays delegated when the code tree
is replaced. -/
theorem doAppAux_setCode_some_none {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : BviState C F) (code : Spt (Nat × Bvi.Exp))
    (run : doAppAux op args state = some none) :
    doAppAux op args { state with code := code } = some none := by
  by_cases hlabel : ∃ name, op = .label name
  · obtain ⟨name, rfl⟩ := hlabel
    cases args with
    | cons arg rest => simp [doAppAux] at run
    | nil => simp [doAppAux] at run
  · have notLabel : ∀ name, op ≠ .label name := by
      intro name eq
      exact hlabel ⟨name, eq⟩
    have frame := doAppAux_frame op args state { state with code := code }
      (Or.inr notLabel)
    rw [← runtimeFrame_setCode state code]
    rw [frame, run]
    rfl

/-- A successful non-install primitive application survives an extended code
tree. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_with_code"
  (fmap_as_finite_support := [refs])]
theorem doApp_with_code {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F) (value : Value)
    (next : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (code : Spt (Nat × Bvi.Exp)) (run : doApp op args state = .val (value, next))
    (growth : sptDomainSet state.code ⊆ sptDomainSet code ∧ op ≠ .install) :
    doApp op args { state with code := code } = .val (value, { next with code := code }) := by
  obtain ⟨dom, notInstall⟩ := growth
  by_cases hinstall : op = .install
  · subst hinstall
    exact (notInstall rfl).elim
  · simp only [doApp, doAppFallback] at run ⊢
    cases aux : doAppAux op args state with
    | none => simp [aux] at run
    | some inner =>
      cases inner with
      | some pair =>
        obtain ⟨value', next'⟩ := pair
        simp only [aux] at run
        rw [doAppAux_setCode_of_run op args state next' value' code aux dom]
        cases run
        rfl
      | none =>
        simp only [aux] at run ⊢
        cases fallback : BvlSem.doApp op args (toBvl state) with
        | err error' =>
          split at run
          all_goals simp_all
        | val pair =>
          obtain ⟨value', next'⟩ := pair
          simp only [fallback] at run
          rw [toBvl_setCode]
          have domBvl : ∀ key, sptDomain (toBvl state).code key →
              sptDomain (sptMap
                (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code) key := by
            intro key present
            rw [toBvl_domain] at present
            rw [sptDomain_sptMap]
            exact dom present
          have applied := BvlProps.doAppWithCode op args (toBvl state) value' next'
            (sptMap (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code)
            (toBvl state).compile (toBvl state).compileOracle ⟨fallback, notInstall⟩ domBvl
          rw [doAppAux_setCode_some_none op args state code aux]
          rw [applied]
          cases run
          simp [fromBvl]

/-- A non-install primitive error survives when the replacement code tree is
contained in the incoming one, or the error is not a type error. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "do_app_with_code_err"
  (fmap_as_finite_support := [refs])]
theorem doApp_with_code_err {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : Flapjack.Compiler.Backend.BviSem.BviState C F)
    (error : ErrorResult ExnOrRet) (code : Spt (Nat × Bvi.Exp))
    (run : doApp op args state = .err error)
    (guard : (sptDomainSet code ⊆ sptDomainSet state.code ∨ error ≠ .abort .typeError) ∧
      op ≠ .install) :
    doApp op args { state with code := code } = .err error := by
  obtain ⟨contained, notInstall⟩ := guard
  by_cases hinstall : op = .install
  · subst hinstall
    exact (notInstall rfl).elim
  · simp only [doApp, doAppFallback] at run ⊢
    cases aux : doAppAux op args state with
    | none =>
      simp only [aux] at run
      cases run
      rcases contained with shrink | notType
      · rw [doAppAux_setCode_none op args state code aux shrink]
      · exact absurd rfl notType
    | some inner =>
      cases inner with
      | some pair =>
        simp [aux] at run
      | none =>
        simp only [aux] at run ⊢
        cases fallback : BvlSem.doApp op args (toBvl state) with
        | val pair => simp [fallback] at run
        | err error' =>
          have classified := BvlProps.doAppError op args (toBvl state) error' fallback
          rcases classified with typeErr | ⟨name, outcome, opEq, errEq⟩
          · rw [typeErr] at fallback
            simp only [fallback] at run
            cases run
            rcases contained with shrink | notType
            · have bvlGuard : ∀ key, sptDomain
                  (sptMap (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code)
                  key → sptDomain (toBvl state).code key := by
                intro key present
                rw [sptDomain_sptMap] at present
                rw [toBvl_domain]
                exact shrink present
              have applied := BvlProps.doAppWithCodeErr op args (toBvl state)
                (.abort .typeError)
                (sptMap (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code)
                (toBvl state).compile (toBvl state).compileOracle ⟨fallback, notInstall⟩
                (Or.inl bvlGuard)
              rw [doAppAux_setCode_some_none op args state code aux]
              rw [toBvl_setCode, applied]
            · exact absurd rfl notType
          · simp only [fallback, errEq] at run
            cases run
            have bvlGuard : error' ≠ .abort .typeError := by
              rw [errEq]
              simp
            have applied := BvlProps.doAppWithCodeErr op args (toBvl state) error'
              (sptMap (fun _ => @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, Bvl.Exp.var 0)⟩) code)
              (toBvl state).compile (toBvl state).compileOracle ⟨fallback, notInstall⟩
              (Or.inr bvlGuard)
            rw [errEq] at applied
            rw [doAppAux_setCode_some_none op args state code aux]
            rw [toBvl_setCode, applied]

end Flapjack.Compiler.Backend.BviProps
