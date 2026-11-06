import Flapjack.Compiler.Backend.ClosMti.Proofs.FuelStable

/-! A total proof-side view of the executed multi-argument traversal. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- Extract the unique result of the executed retrying traversal for one
expression. This helper has no separate HOL declaration. -/
noncomputable def introExp (maxApp : Nat) (e : Exp) : Exp :=
  Classical.choose (introMultiBounded_succeeds 0 maxApp e)

/-- Total multi-argument introduction. `introExp` extracts the unique output
of the executed pass; the equations below establish every recursive clause. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "intro_multi_def"]
noncomputable def introList (maxApp : Nat) (es : List Exp) : List Exp :=
  es.map (introExp maxApp)

/-- The extracted expression is the actual executed pass output at any fuel. -/
theorem introExp_bounded (fuel maxApp : Nat) (e : Exp) :
    introMultiBounded fuel maxApp e = some (introExp maxApp e) := by
  rw [introMultiBounded_fuel_independent fuel 0 maxApp e]
  exact Classical.choose_spec (introMultiBounded_succeeds 0 maxApp e)

/-- Any successful ordinary traversal returns the extracted result. -/
theorem introExp_eq_of_fuel (fuel maxApp : Nat) (e result : Exp)
    (run : introMultiFuel fuel maxApp e = some result) : introExp maxApp e = result := by
  have bounded := introMultiBounded_eq_of_success fuel maxApp e result run
  rw [introExp_bounded] at bounded
  exact Option.some.inj bounded

/-- Every structurally sufficient traversal returns the extracted result. -/
theorem introExp_fuel (fuel maxApp : Nat) (e : Exp) (bound : expBudget e < fuel) :
    introMultiFuel fuel maxApp e = some (introExp maxApp e) := by
  obtain ⟨result, run⟩ := introMultiFuel_succeeds fuel maxApp e bound
  rw [introExp_eq_of_fuel fuel maxApp e result run]
  exact run

/-- A list traversal at sufficient fuel yields the total view elementwise. -/
theorem introList_fuel (fuel maxApp : Nat) (es : List Exp)
    (bound : ∀ e ∈ es, expBudget e < fuel) :
    es.mapM (introMultiFuel fuel maxApp) = some (introList maxApp es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have head := introExp_fuel fuel maxApp e (bound e (by simp))
    have tail := ih (by intro x member; exact bound x (by simp [member]))
    simp [List.mapM_cons, introList, head, tail]

/-- The total list view agrees with the production pass for every fuel. -/
theorem compileFuel_introList (fuel maxApp : Nat) (es : List Exp) :
    compileFuel fuel true maxApp es = some (introList maxApp es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [compileFuel, ↓reduceIte, introList] at ih ⊢
    simp [List.mapM_cons, introExp_bounded, ih]

/-- The proof-side total list traversal preserves the number of expressions. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "intro_multi_length"]
theorem introList_length (maxApp : Nat) (es : List Exp) :
    (introList maxApp es).length = es.length := by
  simp [introList]

/-- Transforming one expression returns exactly one expression. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "intro_multi_sing"]
theorem introList_singleton (e : Exp) (maxApp : Nat) :
    ∃ result, introList maxApp [e] = [result] := by
  exact ⟨introExp maxApp e, rfl⟩

/-- The total list traversal commutes with a leading expression. -/
theorem introList_cons (maxApp : Nat) (e : Exp) (es : List Exp) :
    introList maxApp (e :: es) = introExp maxApp e :: introList maxApp es := rfl

/-- Variables are unchanged by the executed traversal. -/
theorem introExp_var (maxApp : Nat) (trace : BackendCommon.Tra) (index : Nat) :
    introExp maxApp (.var trace index) = .var trace index := by
  apply introExp_eq_of_fuel 1
  rfl

/-- Raising an expression recurses into its payload. -/
theorem introExp_raise (maxApp : Nat) (trace : BackendCommon.Tra) (body : Exp) :
    introExp maxApp (.raise trace body) = .raise trace (introExp maxApp body) := by
  apply introExp_eq_of_fuel (expBudget body + 2)
  rw [introMultiFuel]
  rw [introExp_fuel (expBudget body + 1) maxApp body (by omega)]
  rfl

/-- A tick retains its trace while transforming the body. -/
theorem introExp_tick (maxApp : Nat) (trace : BackendCommon.Tra) (body : Exp) :
    introExp maxApp (.tick trace body) = .tick trace (introExp maxApp body) := by
  apply introExp_eq_of_fuel (expBudget body + 2)
  rw [introMultiFuel]
  rw [introExp_fuel (expBudget body + 1) maxApp body (by omega)]
  rfl

/-- Conditionals transform each of their three expressions. -/
theorem introExp_if (maxApp : Nat) (trace : BackendCommon.Tra) (x y z : Exp) :
    introExp maxApp (.ifThenElse trace x y z) =
      .ifThenElse trace (introExp maxApp x) (introExp maxApp y) (introExp maxApp z) := by
  let fuel := expBudget x + expBudget y + expBudget z + 1
  have hx := introExp_fuel fuel maxApp x (by dsimp [fuel]; omega)
  have hy := introExp_fuel fuel maxApp y (by dsimp [fuel]; omega)
  have hz := introExp_fuel fuel maxApp z (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hx, hy, hz]
  rfl

/-- Handler and protected expression are both transformed. -/
theorem introExp_handle (maxApp : Nat) (trace : BackendCommon.Tra) (body handler : Exp) :
    introExp maxApp (.handle trace body handler) =
      .handle trace (introExp maxApp body) (introExp maxApp handler) := by
  let fuel := expBudget body + expBudget handler + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  have hh := introExp_fuel fuel maxApp handler (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hb, hh]
  rfl

/-- Let bindings and their body are transformed by the same total view. -/
theorem introExp_let (maxApp : Nat) (trace : BackendCommon.Tra) (bindings : List Exp) (body : Exp) :
    introExp maxApp (.let trace bindings body) =
      .let trace (introList maxApp bindings) (introExp maxApp body) := by
  let fuel := listBudget bindings + expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  have hs := introList_fuel fuel maxApp bindings (by
    intro e member
    have h := member_budget_lt bindings e member
    dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hs, hb]
  rfl

/-- Direct calls transform all argument expressions. -/
theorem introExp_call (maxApp : Nat) (trace : BackendCommon.Tra) (ticks location : Nat) (args : List Exp) :
    introExp maxApp (.call trace ticks location args) =
      .call trace ticks location (introList maxApp args) := by
  let fuel := listBudget args + 1
  have hs := introList_fuel fuel maxApp args (by
    intro e member
    have h := member_budget_lt args e member
    dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hs]
  rfl

/-- Primitive operations transform all argument expressions. -/
theorem introExp_op (maxApp : Nat) (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List Exp) :
    introExp maxApp (.op trace op args) = .op trace op (introList maxApp args) := by
  let fuel := listBudget args + 1
  have hs := introList_fuel fuel maxApp args (by
    intro e member
    have h := member_budget_lt args e member
    dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hs]
  rfl

/-- An indirect application collects nested argument lists before recursively
transforming the resulting head and arguments. -/
theorem introExp_app_none (maxApp : Nat) (trace : BackendCommon.Tra) (body : Exp) (args : List Exp) :
    introExp maxApp (.app trace none body args) =
      let (collected, head) := collectApps maxApp args body
      .app trace none (introExp maxApp head) (introList maxApp collected) := by
  cases h : collectApps maxApp args body with
  | mk collected head =>
    let fuel := expBudget head + listBudget collected + 1
    have hh := introExp_fuel fuel maxApp head (by dsimp [fuel]; omega)
    have hs := introList_fuel fuel maxApp collected (by
      intro e member
      have h := member_budget_lt collected e member
      dsimp [fuel]; omega)
    dsimp only
    apply introExp_eq_of_fuel (fuel + 1)
    rw [introMultiFuel, h]
    dsimp only
    rw [hh, hs]
    rfl

/-- A direct application retains its location and transforms its children. -/
theorem introExp_app_some (maxApp : Nat) (trace : BackendCommon.Tra) (location : Nat)
    (body : Exp) (args : List Exp) :
    introExp maxApp (.app trace (some location) body args) =
      .app trace (some location) (introExp maxApp body) (introList maxApp args) := by
  let fuel := expBudget body + listBudget args + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  have hs := introList_fuel fuel maxApp args (by
    intro e member
    have h := member_budget_lt args e member
    dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hb, hs]
  rfl

/-- An unannotated function collects nested arguments before transforming its
remaining body. -/
theorem introExp_fn_none (maxApp : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (arity : Nat) (body : Exp) :
    introExp maxApp (.fn name none none arity body) =
      let (arity', body') := collectArgs maxApp arity body
      .fn name none none arity' (introExp maxApp body') := by
  cases h : collectArgs maxApp arity body with
  | mk arity' body' =>
    let fuel := expBudget body' + 1
    have hb := introExp_fuel fuel maxApp body' (by dsimp [fuel]; omega)
    dsimp only
    apply introExp_eq_of_fuel (fuel + 1)
    rw [introMultiFuel, h]
    dsimp only
    rw [hb]
    rfl

/-- A function with a location annotation does not collect nested arguments. -/
theorem introExp_fn_location (maxApp : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Nat) (vars : Option (List Nat)) (arity : Nat) (body : Exp) :
    introExp maxApp (.fn name (some location) vars arity body) =
      .fn name (some location) vars arity (introExp maxApp body) := by
  let fuel := expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  cases vars <;> rw [introMultiFuel, hb] <;> simp_all

/-- A function with an explicit free-variable list is transformed without
collecting nested arguments. -/
theorem introExp_fn_vars (maxApp : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (vars : List Nat) (arity : Nat) (body : Exp) :
    introExp maxApp (.fn name none (some vars) arity body) =
      .fn name none (some vars) arity (introExp maxApp body) := by
  let fuel := expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hb] <;> simp_all

/-- The collected recursive-function body and its transformed expression. -/
noncomputable def introFun (maxApp : Nat) (function : Nat × Exp) : Nat × Exp :=
  let (arity, body) := collectArgs maxApp function.1 function.2
  (arity, introExp maxApp body)

/-- The recursive-function traversal at sufficient fuel matches `introFun`. -/
theorem introFuns_fuel (fuel maxApp : Nat) (funs : List (Nat × Exp))
    (bound : ∀ arity body, (arity, body) ∈ funs → expBudget body < fuel) :
    funs.mapM (fun p => do
      let (arity, body) := collectArgs maxApp p.1 p.2
      pure (arity, ← introMultiFuel fuel maxApp body)) = some (funs.map (introFun maxApp)) := by
  induction funs with
  | nil => rfl
  | cons function funs ih =>
    obtain ⟨arity, body⟩ := function
    have smaller := collectArgs_budget maxApp arity body
    have bodyBound := bound arity body (by simp)
    have head := introExp_fuel fuel maxApp (collectArgs maxApp arity body).2 (by omega)
    have tail := ih (by intro a b member; exact bound a b (by simp [member]))
    cases found : collectArgs maxApp arity body with
    | mk newArity newBody =>
      simp only [found] at head
      simp only [List.mapM_cons, List.map_cons, introFun, found]
      rw [head, tail]
      rfl

/-- Unannotated recursive functions collect arguments in each function and
transform their bodies, as well as the enclosing body. -/
theorem introExp_letrec_none (maxApp : Nat) (names : List Flapjack.Basis.Pure.MlString.MlString)
    (funs : List (Nat × Exp)) (body : Exp) :
    introExp maxApp (.letrec names none none funs body) =
      .letrec names none none (funs.map (introFun maxApp)) (introExp maxApp body) := by
  let fuel := funsBudget funs + expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  have hf := introFuns_fuel fuel maxApp funs (by
    intro a b member
    have h := fun_member_budget_lt funs a b member
    dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hf, hb]
  rfl

/-- Recursive functions carrying a location retain their function bundle. -/
theorem introExp_letrec_location (maxApp : Nat) (names : List Flapjack.Basis.Pure.MlString.MlString)
    (location : Nat) (vars : Option (List Nat)) (funs : List (Nat × Exp)) (body : Exp) :
    introExp maxApp (.letrec names (some location) vars funs body) =
      .letrec names (some location) vars funs (introExp maxApp body) := by
  let fuel := expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  cases vars <;> rw [introMultiFuel, hb] <;> simp_all

/-- Recursive functions carrying explicit free variables retain their bundle. -/
theorem introExp_letrec_vars (maxApp : Nat) (names : List Flapjack.Basis.Pure.MlString.MlString)
    (vars : List Nat) (funs : List (Nat × Exp)) (body : Exp) :
    introExp maxApp (.letrec names none (some vars) funs body) =
      .letrec names none (some vars) funs (introExp maxApp body) := by
  let fuel := expBudget body + 1
  have hb := introExp_fuel fuel maxApp body (by dsimp [fuel]; omega)
  apply introExp_eq_of_fuel (fuel + 1)
  rw [introMultiFuel, hb] <;> simp_all

/-- Apply multi-argument introduction when enabled. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "compile_def"]
noncomputable def compile (enabled : Bool) (maxApp : Nat) (es : List Exp) : List Exp :=
  if enabled then introList maxApp es else es

/-- The total compiler agrees with the executed fuel-based compiler. -/
theorem compileFuel_eq_compile (fuel : Nat) (enabled : Bool) (maxApp : Nat) (es : List Exp) :
    compileFuel fuel enabled maxApp es = some (compile enabled maxApp es) := by
  cases enabled with
  | false => rfl
  | true => exact compileFuel_introList fuel maxApp es

/-- Incremental multi-argument compilation transforms the main expression
list and returns an empty auxiliary list. The input and output payloads are
independent, as in the inferred HOL type. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "compile_inc_def"]
noncomputable def compileInc {Input Output : Type} (maxApp : Nat)
    (program : List Exp × Input) : List Exp × List Output :=
  (introList maxApp program.1, [])

/-- Optionally run the incremental transformation. -/
@[hol "cakeml/compiler/backend/clos_mtiScript.sml" "cond_mti_compile_inc_def"]
noncomputable def condCompileInc {Output : Type} (enabled : Bool) (maxApp : Nat) :
    List Exp × List Output → List Exp × List Output :=
  if enabled then compileInc maxApp else id

/-- Incremental compilation always returns an empty auxiliary list. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "SND_compile_inc"]
theorem compileInc_snd {Input Output : Type} (maxApp : Nat) (program : List Exp × Input) :
    (compileInc (Output := Output) maxApp program).2 = [] := rfl

end Flapjack.Compiler.Backend.ClosMti
