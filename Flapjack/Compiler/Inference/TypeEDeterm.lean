module

public import Flapjack.TypeSystemHOL.Patterns
public import Flapjack.Compiler.Inference.Unify.Vars
public import Flapjack.Compiler.Inference.Unify.Walkstar
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
private theorem mapEqAt {α β : Type} (f g : α → β) (xs : List α)
    (equal : xs.map f = xs.map g) (x : α) (member : x ∈ xs) : f x = g x := by
  induction xs with
  | nil => simp at member
  | cons a rest ih =>
    simp only [List.map_cons, List.cons.injEq] at equal
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst x; exact equal.1
    · exact ih equal.2 member

private theorem diff (s1 s2 : HolFiniteMapExact Nat InferT) (n : Nat)
    (w1 : tWfs s1) (w2 : tWfs s2) (different : tWalkstar s1 (.uvar n) ≠ tWalkstar s2 (.uvar n))
    (t : InferT) : tVars t n → tWalkstar s1 t ≠ tWalkstar s2 t := by
  intro member equal
  cases t with
  | varDb i =>
    rw [tVarsEqn.1] at member
    exact member.elim
  | uvar i =>
    rw [tVarsEqn.2.2] at member
    change n = i at member
    subst i
    exact different equal
  | app ts tag =>
    rw [tVarsEqn.2.1] at member
    obtain ⟨_, ⟨t, inTs, rfl⟩, occurs⟩ := member
    have listsEqual : ts.map (tWalkstar s1) = ts.map (tWalkstar s2) := by
      have h1 := (tWalkstarEqn1 s1 0 ts tag w1).2
      have h2 := (tWalkstarEqn1 s2 0 ts tag w2).2
      rw [h1, h2] at equal
      exact InferT.app.inj equal |>.1
    exact diff s1 s2 n w1 w2 different t occurs (mapEqAt _ _ ts listsEqual t inTs)
termination_by sizeOf t
decreasing_by
  have bound := List.sizeOf_lt_of_mem inTs
  simp_all only [InferT.app.sizeOf_spec]
  omega

/-- Both source substitutions use the canonical finite-map carrier. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarDiff_s1
    (s1 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).lookup key = s1.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1)).finiteSupport = s1.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s1) = s1 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s1 key

/-- The second source substitution has the same canonical map representation. -/
theorem holFmapAsFiniteSupportParamWitness_tWalkstarDiff_s2
    (s2 : HolFiniteMapExact Nat InferT) (key : Nat) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).lookup key = s2.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2)).finiteSupport = s2.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad s2) = s2 :=
  holFmapAsFiniteSupportParamWitness_tVR_subst s2 key

/-- A difference at an occurring variable remains visible after walking a type. -/
@[hol "cakeml/compiler/inference/proofs/type_eDetermScript.sml" "t_walkstar_diff"
  (fmap_as_finite_support_parameters := [s1, s2])]
theorem tWalkstarDiff (s1 s2 : HolFiniteMapExact Nat InferT) (n : Nat) :
    tWfs s1 ∧ tWfs s2 ∧ tWalkstar s1 (.uvar n) ≠ tWalkstar s2 (.uvar n) →
      (∀ t, tVars t n → tWalkstar s1 t ≠ tWalkstar s2 t) ∧
      (∀ (ts : List InferT) x, x ∈ ts → tVars x n → tWalkstar s1 x ≠ tWalkstar s2 x) := by
  rintro ⟨w1, w2, different⟩
  exact ⟨diff s1 s2 n w1 w2 different, fun _ x _ => diff s1 s2 n w1 w2 different x⟩
end Flapjack.Compiler.Inference.TypeEDeterm
