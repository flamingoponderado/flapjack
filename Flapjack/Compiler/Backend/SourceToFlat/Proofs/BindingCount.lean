import Flapjack.Compiler.Backend.SourceToFlat.CompileDecs

/-! Counts of globally allocated source bindings. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

mutual
/-- The number of slots allocated by a declaration. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "num_bindings_def"]
def numBindings : Dec → Nat
  | .dlet _ p e => if (simpleDlet p e).isSome then 0 else (patBindings p).length
  | .dletrec _ funs => funs.length
  | .dmod _ ds => numBindingsList ds
  | .dlocal locals ds => numBindingsList locals + numBindingsList ds
  | .denv _ => 1
  | _ => 0
termination_by d => sizeOf d

/-- Structural sum used for nested declaration lists. -/
def numBindingsList : List Dec → Nat
  | [] => 0
  | d :: ds => numBindings d + numBindingsList ds
termination_by ds => sizeOf ds
end

/-- The structural sum is the source's SUM of the mapped counts. -/
theorem numBindingsList_eq_sum (ds : List Dec) : numBindingsList ds = (ds.map numBindings).sum := by
  induction ds with
  | nil => simp [numBindingsList]
  | cons d ds ih => simp [numBindingsList, ih]

/-- The output variable counter advances by exactly the source binding count. -/
theorem compileDecs_bindingCount (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) :
    (ds : List Dec) → (compileDecs t n next env envs ds).2.1.vidx = next.vidx + numBindingsList ds
  | [] => by simp [compileDecs, numBindingsList]
  | [d] => by
    cases d with
    | dlet loc p e =>
      cases h : simpleDlet p e with
      | some value =>
        obtain ⟨pv, v⟩ := value
        cases lookup : nsLookup env.v v <;> simp [compileDecs, numBindingsList, numBindings, h, lookup]
        case some name => cases name <;> simp
      | none => simp [compileDecs, numBindingsList, numBindings, h]
    | dletrec loc funs => simp [compileDecs, numBindingsList, numBindings]
    | dtype loc types => simp [compileDecs, numBindingsList, numBindings]
    | dtabbrev loc vars name typ => simp [compileDecs, numBindingsList, numBindings]
    | dexn loc name types => simp [compileDecs, numBindingsList, numBindings]
    | denv name => simp [compileDecs, numBindingsList, numBindings]
    | dmod name ds =>
      have h := compileDecs_bindingCount (name :: t) n next env envs ds
      generalize hc : compileDecs (name :: t) n next env envs ds = result
      obtain ⟨n', next', env', envs', code⟩ := result
      simp only [hc] at h
      simpa [compileDecs, hc, numBindingsList, numBindings] using h
    | dlocal locals body =>
      have hlocal := compileDecs_bindingCount t n next env envs locals
      generalize hc : compileDecs t n next env envs locals = first
      obtain ⟨n', next', env', envs', code⟩ := first
      simp only [hc] at hlocal
      have hbody := compileDecs_bindingCount t n' next' (extendEnv env' env) envs' body
      generalize hb : compileDecs t n' next' (extendEnv env' env) envs' body = second
      obtain ⟨n'', next'', env'', envs'', bodyCode⟩ := second
      simp only [hb] at hbody
      simp only [compileDecs, hc, hb, numBindingsList, numBindings]
      omega
  | d :: d2 :: ds => by
    have hfirst := compileDecs_bindingCount t n next env envs [d]
    generalize hc : compileDecs t n next env envs [d] = first
    obtain ⟨n', next', env', envs', code⟩ := first
    simp only [hc, numBindingsList, Nat.add_zero] at hfirst
    have hrest := compileDecs_bindingCount t n' next' (extendEnv env' env) envs' (d2 :: ds)
    generalize hr : compileDecs t n' next' (extendEnv env' env) envs' (d2 :: ds) = rest
    obtain ⟨n'', next'', env'', envs'', restCode⟩ := rest
    simp only [hr, numBindingsList] at hrest
    simp only [compileDecs, hc, hr, numBindingsList]
    omega
termination_by ds => sizeOf ds
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have positive : 0 < sizeOf d2 := by cases d2 <;> simp <;> omega
       omega)

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_num_bindings"]
theorem compileDecs_numBindings (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) (ds : List Dec)
    (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (code : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs ds = (n', next', env', envs', code)) :
    next.vidx ≤ next'.vidx ∧ (ds.map numBindings).sum = next'.vidx - next.vidx := by
  have h := compileDecs_bindingCount t n next env envs ds
  simp only [compiled] at h
  rw [← numBindingsList_eq_sum]
  omega

end Flapjack.Compiler.Backend.SourceToFlat
