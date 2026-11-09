module

public import Flapjack.Compiler.Backend.ClosCall
public import Mathlib.Tactic

@[expose] public section

/-! Source-shaped direct-call stub generators and their executable forms. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- Generate variable expressions in source order. The original index
parameter is retained even though it does not affect the result. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "GENLIST_Var_def"]
def variablesSource (t : BackendCommon.Tra) : Nat → Nat → List Exp
  | _, 0 => []
  | i, n + 1 => variablesSource t (i + 1) n ++ [.var t n]

/-- The source variable generator equals the range map used by the compiler. -/
theorem variablesSource_eq_variables (t : BackendCommon.Tra) (i n : Nat) :
    variablesSource t i n = ClosCall.variables t n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [variablesSource, ih, ClosCall.variables, List.range_succ, List.map_append, List.map_singleton]

/-- Generate one direct-call stub for each function. The ignored original
function payload remains polymorphic, and the source index is retained. -/
@[hol "cakeml/compiler/backend/clos_callScript.sml" "calls_list_def"]
def callsListSource {A : Type} (t : BackendCommon.Tra) : Nat → Nat → List (Nat × A) → List (Nat × Exp)
  | _, _, [] => []
  | i, loc, (arity, _) :: fns =>
      (arity, .call t 0 (loc + 1) (variablesSource t 1 arity)) ::
        callsListSource t (i + 1) (loc + 2) fns

/-- Indexed range form of the source stub generator. -/
theorem callsListSource_eq_range {A : Type} (t : BackendCommon.Tra) (i loc : Nat)
    (fns : List (Nat × A)) :
    callsListSource t i loc fns = (fns.zip (List.range fns.length)).map
      (fun ((arity, _), j) => (arity, .call t 0 (loc + 2 * j + 1) (ClosCall.variables t arity))) := by
  induction fns generalizing i loc with
  | nil => rfl
  | cons fn rest ih =>
    obtain ⟨arity, body⟩ := fn
    simp only [callsListSource, ih, variablesSource_eq_variables, List.length_cons,
      List.range_succ_eq_map, List.zip_cons_cons, List.map_cons, List.zip_map_right,
      List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro pair member
    rcases pair with ⟨⟨a, b⟩, j⟩
    simp only [Function.comp_apply, Prod.map, id_eq]
    congr 2
    omega

/-- The executed generator is the source generator at the trace and index
used in direct-call conversion. -/
theorem callsList_eq_source (loc : Nat) (fns : List (Nat × Exp)) :
    callsList loc fns = callsListSource .none 1 loc fns := by
  rw [callsListSource_eq_range]
  rfl

end Flapjack.Compiler.Backend.ClosCall
