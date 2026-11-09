import Flapjack.Compiler.Backend.ClosAnnotate.Free.SourceEquations
import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Flapjack.Compiler.Backend.ClosAnnotate.Shift
import Flapjack.Compiler.Backend.ClosAnnotate.Shift.OriginalEquivalence
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension

/-! Pure-binding replacement prerequisites for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosLang
open Flapjack.Compiler.Backend.DbVars

/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- If none of the first `count` variables occurs, any present variable is
outside that prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "no_overlap_has_var_IMP"]
theorem noOverlap_hasVar_bound (count : Nat) (set : DbVarSet) (index : Nat)
    (h : noOverlap count set = true ∧ hasVar index set = true) : count ≤ index := by
  obtain ⟨noOverlapRun, present⟩ := h
  induction count with
  | zero => omega
  | succ count ih =>
    simp only [noOverlap, Bool.and_eq_true] at noOverlapRun
    have bound := ih noOverlapRun.2
    have different : index ≠ count := by
      intro equal
      subst index
      simp [present] at noOverlapRun
    omega

/-- Shifting a source zero expression leaves it unchanged. -/
theorem shiftList_replicate_const0 (count : Nat) (trace : BackendCommon.Tra)
    (m l : Nat) (index : Spt Nat) :
    shiftList (List.replicate count (const0 trace)) m l index = List.replicate count (const0 trace) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, shiftList, ih]
    rfl

/-- The replacement zeros evaluate to zeros without changing state. -/
@[hol "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml" "evaluate_shift_REPLICATE_const_0"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_shift_replicate_const0 {C F : Type} (count : Nat) (trace : BackendCommon.Tra)
    (m l : Nat) (index : Spt Nat) (env : List Value) (state : State C F) :
    evaluate (shiftSource (List.replicate count (const0 trace)) m l index) env state =
      (.val (List.replicate count (.number 0)), state) := by
  rw [shiftSource_eq_shiftList, shiftList_replicate_const0]
  induction count with
  | zero => simp [evaluate]
  | succ count ih =>
    have first : evaluate [const0 trace] env state = (.val [.number 0], state) := by
      simp [const0, evaluate, fixClock, doApp, applyNumeric, doIntApp]
    rw [List.replicate_succ, ClosProps.evaluate_cons_value _ _ _ _ _ _ first, ih]
    rfl

/-- Replacing unused pure bindings with zeros preserves the environment
relation at every free variable of the body. -/
theorem envOk_unused_bindings (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (m l : Nat) (index : Spt Nat) (env nextEnv values : List Value)
    (valueLength : values.length = bindings.length) (pure : pureList bindings = true)
    (unused : noOverlap bindings.length (altFree [body]).2 = true)
    (vars : ∀ n, altFv n [.let trace bindings body] = true → EnvOk m l index env nextEnv n)
    (n : Nat) (present : altFv n [body] = true) :
    EnvOk m (l + bindings.length) index (values ++ env)
      (List.replicate bindings.length (.number 0) ++ nextEnv) n := by
  have bound : bindings.length ≤ n := by
    apply noOverlap_hasVar_bound bindings.length (altFree [body]).2 n
    exact ⟨unused, present⟩
  have tailRel : EnvOk m l index env nextEnv (n - bindings.length) := by
    apply vars (n - bindings.length)
    rw [altFv_let]
    have shifted : n - bindings.length + bindings.length = n := by omega
    simp [pure, shifted, present]
  have result := envOk_extend_ignore (List.replicate bindings.length (.number 0)) values n values.length
    m l index env nextEnv ⟨by simpa using valueLength.symm, by omega, rfl, by simpa [valueLength] using tailRel⟩
  simpa [valueLength] using result

end Flapjack.Compiler.Backend.ClosAnnotate
