import Flapjack.FfiHOL
import Mathlib.Logic.Relation

namespace Flapjack

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_LENGTH"]
theorem callFFIHOL_length {σ : Type} (st : HolFfiState σ) (index : HolFfiName)
    (conf x : List (BitVec 8)) (newSt : HolFfiState σ) (newBytes : List (BitVec 8))
    (h : callFFIHOL st index conf x = .ret newSt newBytes) : x.length = newBytes.length :=
  (callFFIHOL_ret_length st index conf x newBytes newSt h).symm

/-- HOL's single successful FFI-call relation. All four witnesses are retained:
the name, configuration, input bytes, and returned bytes. This is the step
relation, rather than its reflexive-transitive closure. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_rel_def"]
def callFFIRelHOL {σ : Type} (before after : HolFfiState σ) : Prop :=
  ∃ (name : HolFfiName) (configuration bytes returned : List (BitVec 8)),
    callFFIHOL before name configuration bytes = .ret after returned

/-- Flapjack infrastructure: HOL's empty external call supplies a genuine
successful step for every native FFI state, independently of its oracle. -/
theorem callFFIRelHOL_refl {σ : Type} (state : HolFfiState σ) :
    callFFIRelHOL state state := by
  refine ⟨.extCall (Basis.Pure.MlString.MlString.implode []), [], [], [], ?_⟩
  simp [callFFIHOL]

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_rel_consts"]
theorem callFFIRelHOL_consts {σ : Type} (s1 s2 : HolFfiState σ)
    (h : callFFIRelHOL s1 s2) : s2.oracle = s1.oracle := by
  obtain ⟨name, conf, bytes, returned, hcall⟩ := h
  unfold callFFIHOL at hcall
  split at hcall
  · cases hcall
    rfl
  · cases horacle : s1.oracle name s1.ffiState conf bytes with
    | final outcome => simp [horacle] at hcall
    | ret next bytes' =>
      simp only [horacle] at hcall
      split at hcall
      · cases hcall
        rfl
      · cases hcall

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "RTC_call_FFI_rel_consts"]
theorem callFFIRelHOL_rtc_consts {σ : Type} (s1 s2 : HolFfiState σ)
    (h : Relation.ReflTransGen callFFIRelHOL s1 s2) : s2.oracle = s1.oracle := by
  induction h with
  | refl => rfl
  | @tail middle last hsteps hstep ih =>
      exact (callFFIRelHOL_consts middle last hstep).trans ih

/-- FFI trace growth and state equality when no event was appended. -/
@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "io_events_mono_def"]
def ioEventsMonoHOL {σ : Type} (before after : HolFfiState σ) : Prop :=
  before.ioEvents <+: after.ioEvents ∧ (after.ioEvents = before.ioEvents → after = before)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "io_events_mono_refl"]
theorem ioEventsMonoHOL_refl {σ : Type} (ffi : HolFfiState σ) : ioEventsMonoHOL ffi ffi :=
  ⟨List.prefix_refl _, fun _ => rfl⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "io_events_mono_trans"]
theorem ioEventsMonoHOL_trans {σ : Type} (ffi1 ffi2 ffi3 : HolFfiState σ)
    (h : ioEventsMonoHOL ffi1 ffi2 ∧ ioEventsMonoHOL ffi2 ffi3) : ioEventsMonoHOL ffi1 ffi3 := by
  refine ⟨h.1.1.trans h.2.1, ?_⟩
  intro eq
  have eq12 : ffi2.ioEvents = ffi1.ioEvents := (eq ▸ h.2.1).eq_of_length_le h.1.1.length_le
  have eq23 : ffi3.ioEvents = ffi2.ioEvents := eq.trans eq12.symm
  exact (h.2.2 eq23).trans (h.1.2 eq12)

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "io_events_mono_antisym"]
theorem ioEventsMonoHOL_antisym {σ : Type} (s1 s2 : HolFfiState σ)
    (h : ioEventsMonoHOL s1 s2 ∧ ioEventsMonoHOL s2 s1) : s1 = s2 := by
  exact (h.1.2 (h.2.1.eq_of_length_le h.1.1.length_le)).symm

/-- Flapjack helper, with no separately named HOL original: one successful
FFI transition preserves and extends its trace. -/
theorem callFFIRelHOL_ioEventsMono {σ : Type} {s1 s2 : HolFfiState σ}
    (h : callFFIRelHOL s1 s2) : ioEventsMonoHOL s1 s2 := by
  obtain ⟨name, conf, bytes, returned, hcall⟩ := h
  exact ⟨callFFIHOL_return_ioEvents_prefix s1 name conf bytes s2 returned hcall,
    callFFIHOL_ret_ffi_eq_of_ioEvents_eq s1 s2 name conf bytes returned hcall⟩

@[hol "cakeml/semantics/proofs/evaluatePropsScript.sml" "call_FFI_rel_io_events_mono"]
theorem callFFIRelHOL_rtc_ioEventsMono {σ : Type} (s1 s2 : HolFfiState σ)
    (h : Relation.ReflTransGen callFFIRelHOL s1 s2) : ioEventsMonoHOL s1 s2 := by
  induction h with
  | refl => exact ioEventsMonoHOL_refl _
  | @tail middle last hsteps hstep ih =>
      exact ioEventsMonoHOL_trans s1 middle last ⟨ih, callFFIRelHOL_ioEventsMono hstep⟩

end Flapjack
