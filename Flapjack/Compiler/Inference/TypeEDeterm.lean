module

public import Flapjack.TypeSystemHOL.Patterns
public import Flapjack.Compiler.Inference.Unify.Vars
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant

@[expose] public section

/-! Pattern-typing prerequisites for inference determinacy. -/
namespace Flapjack.Compiler.Inference.TypeEDeterm
open Flapjack Flapjack.TypeSystemHOL Flapjack.AstHOL

/-- Pattern typing preserves the source ordering of bound names. -/
@[hol "cakeml/compiler/inference/proofs/type_eDetermScript.sml" "type_p_pat_bindings"]
theorem typePPatBindings :
    (∀ tvs env p t bindings, TypeP tvs env p t bindings → bindings.map Prod.fst = patBindings p) ∧
    (∀ tvs env ps ts bindings, TypePs tvs env ps ts bindings → bindings.map Prod.fst = patsBindings ps) := by
  constructor <;> intro tvs env p t bindings typed
  all_goals
    first
    | refine TypeP.rec (motive_1 := fun p t bindings _ => bindings.map Prod.fst = patBindings p)
        (motive_2 := fun ps ts bindings _ => bindings.map Prod.fst = patsBindings ps)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypePs.rec (motive_1 := fun p t bindings _ => bindings.map Prod.fst = patBindings p)
        (motive_2 := fun ps ts bindings _ => bindings.map Prod.fst = patsBindings ps)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    all_goals simp_all [patBindings, patsBindings, List.map_append]
open Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify

private theorem checkList (n : Nat) (s : Nat → Prop) (ts : List InferT) :
    checkTList n s ts ↔ ∀ t ∈ ts, checkT n s t := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

private theorem findVar (s : Nat → Prop) (t : InferT) :
    ¬ checkT 0 (fun _ => False) t ∧ checkT 0 s t → ∃ n, s n ∧ tVars t n := by
  intro ⟨notClosed, checked⟩
  cases t with
  | varDb n => simp at checked
  | uvar n =>
    refine ⟨n, by simpa using checked, ?_⟩
    rw [tVarsEqn.2.2]
    rfl
  | app ts tag =>
    have checkedAll : ∀ t ∈ ts, checkT 0 s t := (checkList 0 s ts).1 (by simpa using checked)
    have notAll : ¬ ∀ t ∈ ts, checkT 0 (fun _ => False) t := by
      intro all
      exact notClosed (by simpa using (checkList 0 (fun _ => False) ts).2 all)
    classical
    have ⟨t, member, bad⟩ : ∃ t ∈ ts, ¬ checkT 0 (fun _ => False) t := by simpa using notAll
    obtain ⟨n, allowed, occurs⟩ := findVar s t ⟨bad, checkedAll t member⟩
    refine ⟨n, allowed, ?_⟩
    rw [tVarsEqn.2.1]
    exact ⟨tVars t, ⟨t, member, rfl⟩, occurs⟩
termination_by sizeOf t

/-- An inference type that is valid only with allowed unification variables contains one. -/
@[hol "cakeml/compiler/inference/proofs/type_eDetermScript.sml" "t_vars_check_t"]
theorem tVarsCheckT (s : Nat → Prop) :
    (∀ t, ¬ checkT 0 (fun _ => False) t ∧ checkT 0 s t → ∃ n, s n ∧ tVars t n) ∧
    (∀ (ts : List InferT) x, x ∈ ts → ¬ checkT 0 (fun _ => False) x ∧ checkT 0 s x → ∃ n, s n ∧ tVars x n) := by
  exact ⟨findVar s, fun _ x _ => findVar s x⟩
end Flapjack.Compiler.Inference.TypeEDeterm
