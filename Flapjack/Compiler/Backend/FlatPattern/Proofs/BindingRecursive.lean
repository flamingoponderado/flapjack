import Flapjack.Compiler.Backend.FlatPattern.Proofs.BindingSimulation

/-! Recursive proof obligations for generated pattern bindings. The evaluator
and carriers are still pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The work-list simulation at a fixed compiler input. This is proof-side
infrastructure for the full HOL theorem, not a reviewed HOL declaration. -/
def BindingSimulation {C F : Type} (trace : BackendCommon.Tra) (upper : Nat)
    (todo : List (FlatLang.Pat × Nat × FlatLang.Exp)) (body : FlatLang.Exp) : Prop :=
  ∀ (lower : Nat) (state : FlatSem.State C F) (values : List FlatSem.Value)
    (pre bindings : List (VarN × FlatSem.Value)) (env : FlatSem.Environment FlatSem.Value)
    (final : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (base : List (VarN × FlatSem.Value)),
    FlatSem.pmatchList state (todo.map Prod.fst) values pre = .match bindings →
    FlatSem.evaluate env state [(compilePatBindings trace upper todo body).2] = (final, result) →
    BindingInputs lower upper (compilePatBindings trace upper todo body).1 env state todo values →
    (∀ entry ∈ pre, decNameToNum entry.1 < lower) → lower < upper →
    aLookupRel (fun name => decNameToNum name < lower) Eq env.v (pre ++ base) →
    (∀ item ∈ todo, (∀ name ∈ FlatLang.patBindings item.1, decNameToNum name < lower) ∧
      lower < item.2.1 ∧ item.2.1 < upper) →
    ∃ env2, FlatSem.evaluate env2 state [body] = (final, result) ∧
      aLookupRel (fun name => decNameToNum name < lower) Eq env2.v (bindings ++ base)

/-- Empty work lists already evaluate the continuation in the original
environment. -/
theorem bindingSimulation_nil {C F : Type} (trace : BackendCommon.Tra) (upper : Nat) (body : FlatLang.Exp) :
    @BindingSimulation C F trace upper [] body := by
  intro lower state values pre bindings env final result base matched evaluated inputs preBound bound related itemBounds
  cases values with
  | nil =>
    simp [FlatSem.pmatchList] at matched
    subst bindings
    exact ⟨env, by simpa [compilePatBindings] using evaluated, related⟩
  | cons _ _ => simp [FlatSem.pmatchList] at matched

/-- Wildcard case of the binding simulation; no environment entry is added. -/
theorem bindingSimulation_any {C F : Type} (trace : BackendCommon.Tra) (upper key : Nat)
    (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (ih : @BindingSimulation C F trace upper rest body) :
    @BindingSimulation C F trace upper ((.pany, key, expression) :: rest) body := by
  intro lower state values pre bindings env final result base matched evaluated inputs preBound bound related itemBounds
  cases values with
  | nil => simp [FlatSem.pmatchList] at matched
  | cons value values =>
    have tailMatch : FlatSem.pmatchList state (rest.map Prod.fst) values pre = .match bindings := by
      simpa [FlatSem.pmatchList, FlatSem.pmatch] using matched
    have tailEval : FlatSem.evaluate env state [(compilePatBindings trace upper rest body).2] = (final, result) := by
      simpa [compilePatBindings] using evaluated
    have tailInputs : BindingInputs lower upper (compilePatBindings trace upper rest body).1 env state rest values := by
      simp only [compilePatBindings] at inputs
      cases inputs with | cons _ tail => exact tail
    have tailBounds : ∀ item ∈ rest, (∀ n ∈ FlatLang.patBindings item.1, decNameToNum n < lower) ∧
        lower < item.2.1 ∧ item.2.1 < upper := by
      intro item member
      exact itemBounds item (by simp [member])
    exact ih lower state values pre bindings env final result base tailMatch tailEval tailInputs preBound bound related tailBounds

/-- A successful literal match leaves its incoming bindings unchanged. -/
theorem pmatch_literal_bindings {C F : Type} (state : FlatSem.State C F) (lit : Lit)
    (value : FlatSem.Value) (pre next : List (VarN × FlatSem.Value))
    (matched : FlatSem.pmatch state (.plit lit) value pre = .match next) : next = pre := by
  cases value with
  | litv actual =>
    by_cases same : lit = actual
    · simpa [FlatSem.pmatch, same] using matched.symm
    · simp [FlatSem.pmatch, same] at matched
      split at matched <;> simp_all
  | conv _ _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ =>
    simp [FlatSem.pmatch] at matched

/-- Literal case of the binding simulation; a successful literal match adds
no binding and the generated code is the recursive continuation. -/
theorem bindingSimulation_lit {C F : Type} (trace : BackendCommon.Tra) (upper key : Nat)
    (lit : Lit) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (ih : @BindingSimulation C F trace upper rest body) :
    @BindingSimulation C F trace upper ((.plit lit, key, expression) :: rest) body := by
  intro lower state values pre bindings env final result base matched evaluated inputs preBound bound related itemBounds
  cases values with
  | nil => simp [FlatSem.pmatchList] at matched
  | cons value values =>
    cases head : FlatSem.pmatch state (.plit lit) value pre with
    | typeError => simp [FlatSem.pmatchList, head] at matched
    | noMatch =>
      cases tail : FlatSem.pmatchList state (rest.map Prod.fst) values pre <;>
        simp [FlatSem.pmatchList, head, tail] at matched
    | «match» next =>
      have eq := pmatch_literal_bindings state lit value pre next head
      subst next
      have tailMatch : FlatSem.pmatchList state (rest.map Prod.fst) values pre = .match bindings := by
        simpa [FlatSem.pmatchList, head] using matched
      have tailEval : FlatSem.evaluate env state [(compilePatBindings trace upper rest body).2] = (final, result) := by
        simpa [compilePatBindings] using evaluated
      have tailInputs : BindingInputs lower upper (compilePatBindings trace upper rest body).1 env state rest values := by
        simp only [compilePatBindings] at inputs
        cases inputs with | cons _ tail => exact tail
      have tailBounds : ∀ item ∈ rest, (∀ n ∈ FlatLang.patBindings item.1, decNameToNum n < lower) ∧
          lower < item.2.1 ∧ item.2.1 < upper := by
        intro item member
        exact itemBounds item (by simp [member])
      exact ih lower state values pre bindings env final result base tailMatch tailEval tailInputs preBound bound related tailBounds

/-- Variable case of the binding simulation, assuming the recursive work-list
case at the same upper bound. -/
theorem bindingSimulation_var {C F : Type} (trace : BackendCommon.Tra) (upper key : Nat)
    (name : VarN) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (ih : @BindingSimulation C F trace upper rest body) :
    @BindingSimulation C F trace upper ((.pvar name, key, expression) :: rest) body := by
  intro lower state values pre bindings env final result base matched evaluated inputs preBound bound related itemBounds
  cases values with
  | nil => simp [FlatSem.pmatchList] at matched
  | cons value values =>
    cases compiled : compilePatBindings trace upper rest body with
    | mk used continuation =>
      have hInputs : BindingInputs lower upper (sptInsert key () used) env state
          ((.pvar name, key, expression) :: rest) (value :: values) := by
        simpa [compilePatBindings, compiled] using inputs
      have nameBound : decNameToNum name < lower := by
        have h := itemBounds (.pvar name, key, expression) (by simp)
        exact h.1 name (by simp [FlatLang.patBindings])
      have pure := bindingInputs_var_head lower upper key used env state name expression rest value values hInputs
      have tailInputs := bindingInputs_var_tail lower upper key used env state name expression rest value values nameBound hInputs
      have tailMatch : FlatSem.pmatchList state (rest.map Prod.fst) values ((name, value) :: pre) = .match bindings := by
        simpa [FlatSem.pmatchList, FlatSem.pmatch] using matched
      have tailEval : FlatSem.evaluate { env with v := (name, value) :: env.v } state [continuation] = (final, result) := by
        have step := compilePatBindings_var_evaluate trace upper key name expression body rest env state value pure
        rw [evaluated] at step
        simpa [compiled] using step.symm
      have tailPreBound : ∀ entry ∈ ((name, value) :: pre), decNameToNum entry.1 < lower := by
        intro entry member
        rcases List.mem_cons.mp member with equal | inPre
        · subst entry
          exact nameBound
        · exact preBound entry inPre
      have tailRelated : aLookupRel (fun n => decNameToNum n < lower) Eq
          ((name, value) :: env.v) (((name, value) :: pre) ++ base) :=
        aLookupRel_cons _ _ name value value env.v (pre ++ base) (fun _ => rfl) related
      have tailBounds : ∀ item ∈ rest, (∀ n ∈ FlatLang.patBindings item.1, decNameToNum n < lower) ∧
          lower < item.2.1 ∧ item.2.1 < upper := by
        intro item member
        exact itemBounds item (by simp [member])
      apply ih lower state values ((name, value) :: pre) bindings { env with v := (name, value) :: env.v }
        final result base tailMatch
      · simpa [compiled] using tailEval
      · simpa [compiled] using tailInputs
      · exact tailPreBound
      · exact bound
      · exact tailRelated
      · exact tailBounds

end Flapjack.Compiler.Backend.FlatPattern
