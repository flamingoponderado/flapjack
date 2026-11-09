module

public import Flapjack.Compiler.Backend.ClosAnnotate.Free.SourceEquations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PureEvaluate
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension

@[expose] public section

/-! Pure-binding replacement prerequisites for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosLang
open Flapjack.Compiler.Backend.DbVars

/-- If none of the first `count` variables occurs, any present variable is
outside that prefix. -/
theorem noOverlap_hasVar_bound (count : Nat) (set : DbVarSet) (index : Nat)
    (noOverlapRun : noOverlap count set = true) (present : hasVar index set = true) : count ≤ index := by
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
theorem evaluate_shift_replicate_const0 {C F : Type} (count : Nat) (trace : BackendCommon.Tra)
    (m l : Nat) (index : Spt Nat) (env : List Value) (state : State C F) :
    evaluate (shiftList (List.replicate count (const0 trace)) m l index) env state =
      (.val (List.replicate count (.number 0)), state) := by
  rw [shiftList_replicate_const0]
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
    · exact unused
    · exact present
  have tailRel : EnvOk m l index env nextEnv (n - bindings.length) := by
    apply vars (n - bindings.length)
    rw [altFv_let]
    have shifted : n - bindings.length + bindings.length = n := by omega
    simp [pure, shifted, present]
  have result := envOk_extend_ignore m l index values (List.replicate bindings.length (.number 0))
    env nextEnv n (by simpa using valueLength.symm) (by omega) (by simpa [valueLength] using tailRel)
  simpa [valueLength] using result

end Flapjack.Compiler.Backend.ClosAnnotate
