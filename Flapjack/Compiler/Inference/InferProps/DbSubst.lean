module

public import Flapjack.Compiler.Inference.InferProps.Freevars
public import Flapjack.Compiler.Inference.InferProps.IndexedNames
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant
public import Flapjack.Misc.FindIndex.Bounds

@[expose] public section

/-! Bounds for indexed named type substitutions. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack Flapjack.Misc Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

mutual
private theorem core (m : Nat) (names : List MlString) (t : SemanticT) (n : Nat) (u : Nat → Prop)
    (vars : List MlString) (free : checkFreevars m names t = true)
    (bound : m + vars.length ≤ n) (emptyBound : vars = [] → 0 < m) :
    Infer.checkT n u (Infer.inferTypeSubst (vars.zip ((List.range vars.length).map InferT.varDb)) t) := by
  cases t with
  | var name =>
    have positive : 0 < n := by
      cases vars with
      | nil => simp only [List.length_nil, Nat.add_zero] at bound; have := emptyBound rfl; omega
      | cons a rest => simp only [List.length_cons] at bound; omega
    simp only [Infer.inferTypeSubst, lookupIndex0]
    cases found : findIndex name vars 0 with
    | none => simp [positive]
    | some index =>
      have h := (findIndexLessLength vars name 0 index found).2
      have inRange : index < n := by omega
      simp [inRange]
  | varDb index =>
    have lt : index < m := by simpa [checkFreevars] using free
    have lt' : index < n := by omega
    simp [Infer.inferTypeSubst, lt']
  | app ts id =>
    have all : checkFreevarsList m names ts = true := by simpa [checkFreevars] using free
    simpa [Infer.inferTypeSubst] using listCore m names ts n u vars all bound emptyBound
termination_by sizeOf t

private theorem listCore (m : Nat) (names : List MlString) (ts : List SemanticT) (n : Nat) (u : Nat → Prop)
    (vars : List MlString) (free : checkFreevarsList m names ts = true)
    (bound : m + vars.length ≤ n) (emptyBound : vars = [] → 0 < m) :
    Infer.checkTList n u (Infer.inferTypeSubstList (vars.zip ((List.range vars.length).map InferT.varDb)) ts) := by
  cases ts with
  | nil => simp [Infer.inferTypeSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at free
    simp only [Infer.inferTypeSubstList, Infer.checkTList_cons]
    exact ⟨core m names t n u vars free.1 bound emptyBound,
      listCore m names ts n u vars free.2 bound emptyBound⟩
termination_by sizeOf ts
end

/-- Indexed type substitution preserves the source check bound. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "check_t_infer_type_subst_dbs"]
theorem checkTInferTypeSubstDbs (m : Nat) (names : List MlString) (t : SemanticT) (n : Nat) (u : Nat → Prop) (vars : List MlString) :
    checkFreevars m names t = true ∧ m + vars.length ≤ n ∧ (vars = [] → 0 < m) →
      Infer.checkT n u (Infer.inferTypeSubst (vars.zip ((List.range vars.length).map InferT.varDb)) t) := by
  intro ⟨free, bound, emptyBound⟩
  exact core m names t n u vars free bound emptyBound
end Flapjack.Compiler.Inference.InferProps
