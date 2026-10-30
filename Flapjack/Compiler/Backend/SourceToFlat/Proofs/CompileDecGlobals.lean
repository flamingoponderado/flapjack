import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileGlobals
import Flapjack.Compiler.Backend.SourceToFlat.CompileProg

/-! Declaration-level global-initialization invariants for source-to-flat. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon Flapjack.Compiler.Backend.FlatProps

/-- Global initialization generated for bound names is never captured by
a nested function. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "make_varls_esgc_free"]
theorem makeVarls_esgcFree (n : Nat) (t : Tra) (idx : Nat) (xs : List VarN) :
    esgcFree (makeVarls n t idx xs) := by
  induction xs generalizing n t idx with
  | nil => simp [makeVarls, esgcFree, esgcFreeList]
  | cons x xs ih =>
    cases xs with
    | nil => simp [makeVarls, esgcFree, esgcFreeList]
    | cons y ys => simp [makeVarls, esgcFree, esgcFreeList, ih]

private theorem esgcFreeList_append (xs ys : List FlatLang.Exp) :
    esgcFreeList (xs ++ ys) ↔ esgcFreeList xs ∧ esgcFreeList ys := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih, and_assoc]

/-- Every emitted declaration expression satisfies the global-write invariant. -/
theorem compileDecs_esgcList (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) :
    (ds : List Dec) → esgcFreeList (compileDecs t n next env envs ds).2.2.2.2
  | [] => by simp [compileDecs, esgcFreeList]
  | [d] => by
    cases d with
    | dlet loc p e =>
      cases h : simpleDlet p e with
      | some value =>
        obtain ⟨pv, v⟩ := value
        cases lookup : nsLookup env.v v <;> simp [compileDecs, h, lookup, esgcFreeList]
        case some name => cases name <;> simp [esgcFreeList]
      | none =>
        have he := compileExp_globalSafe ((AstHOL.patBindings p).reverse ++ t) env e
        have hm := makeVarls_esgcFree 0 .none next.vidx (AstHOL.patBindings p).reverse
        simp [compileDecs, h, esgcFreeList, esgcFree, esgcFreeRows, he.1, hm]
    | dletrec loc funs =>
      let names := funs.map Prod.fst
      let newEnv := nsBindList (names.map fun x => (x, VarName.localName .none x)) env.v
      have hf := compileFuns_globalSafe t { env with v := newEnv } funs
      have hm := makeVarls_esgcFree 0 .none next.vidx names.reverse
      simp only [newEnv, names, List.map_map] at hf
      simp [compileDecs, esgcFreeList, esgcFree, hf.2, hm, names]
    | dtype loc types => simp [compileDecs, esgcFreeList]
    | dtabbrev loc vars name typ => simp [compileDecs, esgcFreeList]
    | dexn loc name types => simp [compileDecs, esgcFreeList]
    | denv name => simp [compileDecs, esgcFreeList, esgcFree, envIdTuple]
    | dmod name ds =>
      have h := compileDecs_esgcList (name :: t) n next env envs ds
      generalize hc : compileDecs (name :: t) n next env envs ds = result
      obtain ⟨n', next', env', envs', code⟩ := result
      simp only [hc] at h
      simpa [compileDecs, hc] using h
    | dlocal locals body =>
      have hlocal := compileDecs_esgcList t n next env envs locals
      generalize hc : compileDecs t n next env envs locals = first
      obtain ⟨n', next', env', envs', code⟩ := first
      simp only [hc] at hlocal
      have hbody := compileDecs_esgcList t n' next' (extendEnv env' env) envs' body
      generalize hb : compileDecs t n' next' (extendEnv env' env) envs' body = second
      obtain ⟨n'', next'', env'', envs'', bodyCode⟩ := second
      simp only [hb] at hbody
      simpa [compileDecs, hc, hb, esgcFreeList_append] using And.intro hlocal hbody
  | d :: d2 :: ds => by
    have hfirst := compileDecs_esgcList t n next env envs [d]
    generalize hc : compileDecs t n next env envs [d] = first
    obtain ⟨n', next', env', envs', code⟩ := first
    simp only [hc] at hfirst
    have hrest := compileDecs_esgcList t n' next' (extendEnv env' env) envs' (d2 :: ds)
    generalize hr : compileDecs t n' next' (extendEnv env' env) envs' (d2 :: ds) = rest
    obtain ⟨n'', next'', env'', envs'', restCode⟩ := rest
    simp only [hr] at hrest
    simpa [compileDecs, hc, hr, esgcFreeList_append] using And.intro hfirst hrest
termination_by ds => sizeOf ds
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have positive : 0 < sizeOf d2 := by cases d2 <;> simp <;> omega
       omega)

private theorem esgcFreeList_iff (xs : List FlatLang.Exp) :
    esgcFreeList xs ↔ ∀ x ∈ xs, esgcFree x := by
  induction xs with
  | nil => simp [esgcFreeList]
  | cons x xs ih => simp [esgcFreeList, ih]

/-- The emitted declarations do not initialize globals inside functions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_esgc_free"]
theorem compileDecs_esgcFree (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) (ds : List Dec)
    (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (code : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs ds = (n', next', env', envs', code)) :
    ∀ e ∈ code, esgcFree e := by
  have h := compileDecs_esgcList t n next env envs ds
  rw [compiled] at h
  exact (esgcFreeList_iff code).mp h

private theorem compileProg_esgcList (c : Config) (p : List Dec) :
    esgcFreeList (compileProg c p).2 := by
  let next := { c.next with vidx := c.next.vidx + 1 }
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have h := compileDecs_esgcList [] 1 next c.modEnv envs p
  generalize hc : compileDecs [] 1 next c.modEnv envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at h
  simpa [compileProg, next, envs, hc, esgcFreeList, esgcFree, globAlloc, allocEnvRef] using h

/-- Whole-program initialization preserves the declaration invariant. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_prog_esgc_free"]
theorem compileProg_esgcFree (c : Config) (p : List Dec) (c1 : Config)
    (p1 : List FlatLang.Exp) (compiled : compileProg c p = (c1, p1)) :
    ∀ e ∈ p1, esgcFree e := by
  have h := compileProg_esgcList c p
  rw [compiled] at h
  exact (esgcFreeList_iff p1).mp h

/-- Incremental compilation also keeps global initialization outside functions. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_prog_esgc_free"]
theorem incCompileProg_esgcFree (envId : Nat × Nat) (c : Config) (p : List Dec) :
    ∀ e ∈ (incCompileProg envId c p).2, esgcFree e := by
  let env := lookupEnvId envId c.envs
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have h := compileDecs_esgcList [] 1 c.next env envs p
  generalize hc : compileDecs [] 1 c.next env envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at h
  apply (esgcFreeList_iff _).mp
  simpa [incCompileProg, env, envs, hc, esgcFreeList, esgcFreeList_append,
    esgcFree, globAlloc, storeEnvId, envIdTuple] using h

end Flapjack.Compiler.Backend.SourceToFlat
