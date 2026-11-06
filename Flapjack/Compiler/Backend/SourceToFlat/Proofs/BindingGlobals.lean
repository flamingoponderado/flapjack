import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BindingCount
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.CompileGlobals
import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
import Flapjack.Compiler.Backend.FlatPattern.Proofs.GlobalBounds
import Flapjack.Compiler.Backend.FlatElim.Proofs.GlobalInvariants
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup

/-! Global-write bags produced by source declaration compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon Flapjack.Compiler.Backend.FlatProps

/-- Multiplicity bag for a consecutive range, using the original list-to-bag
construction over `COUNT_LIST` (Lean `List.range`). -/
def bindingRangeBag (start count : Nat) : GlobalBag :=
  fun key => ((List.range count).map (start + ·)).count key

private theorem bindingRangeBag_zero (start : Nat) : bindingRangeBag start 0 = emptyGlobalBag := by
  funext key
  simp [bindingRangeBag, emptyGlobalBag]

private theorem bindingRangeBag_succ (start count : Nat) :
    bindingRangeBag start (count + 1) =
      unionGlobalBag (fun key => if key = start then 1 else 0) (bindingRangeBag (start + 1) count) := by
  funext key
  by_cases h : key = start
  · subst key
    simp [bindingRangeBag, List.range_succ_eq_map, List.map_map, Function.comp_def,
      unionGlobalBag, Nat.add_comm, Nat.add_left_comm]
  · have h' : start ≠ key := Ne.symm h
    simp [bindingRangeBag, List.range_succ_eq_map, List.map_map, Function.comp_def,
      unionGlobalBag, Nat.add_comm, Nat.add_left_comm, h, h']

private theorem bindingRangeBag_add (start a b : Nat) :
    bindingRangeBag start (a + b) =
      unionGlobalBag (bindingRangeBag start a) (bindingRangeBag (start + a) b) := by
  induction a generalizing start with
  | zero =>
    simp only [Nat.zero_add, bindingRangeBag_zero, Nat.add_zero]
    funext key
    simp [unionGlobalBag, emptyGlobalBag]
  | succ a ih =>
    simp only [Nat.succ_add]
    rw [bindingRangeBag_succ, ih, bindingRangeBag_succ]
    funext key
    simp only [unionGlobalBag]
    have eq : start + (a + 1) = start + 1 + a := by omega
    rw [eq]
    omega

private theorem elistGlobals_append (xs ys : List FlatLang.Exp) :
    elistGlobals (xs ++ ys) = unionGlobalBag (elistGlobals xs) (elistGlobals ys) := by
  induction xs with
  | nil =>
    funext key
    simp [elistGlobals, emptyGlobalBag, unionGlobalBag]
  | cons x xs ih =>
    simp only [List.cons_append, elistGlobals, ih]
    funext key
    simp only [unionGlobalBag]
    omega

/-- Generated variable initializers write precisely the allocated slot range. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "set_globals_make_varls"]
theorem setGlobals_makeVarls (n : Nat) (t : Tra) (idx : Nat) (xs : List VarN) :
    setGlobals (makeVarls n t idx xs) = bindingRangeBag idx xs.length := by
  induction xs generalizing n t idx with
  | nil => simp [makeVarls, setGlobals, elistGlobals, bindingRangeBag_zero]
  | cons x xs ih =>
    cases xs with
    | nil =>
      funext key
      by_cases h : key = idx
      · subst key
        simp [makeVarls, setGlobals, elistGlobals, opGlobalBag, unionGlobalBag,
          emptyGlobalBag, bindingRangeBag]
      · have h' : idx ≠ key := Ne.symm h
        simp [makeVarls, setGlobals, elistGlobals, opGlobalBag, unionGlobalBag,
          emptyGlobalBag, bindingRangeBag, h, h']
    | cons y ys =>
      rw [show (x :: y :: ys).length = (y :: ys).length + 1 by simp]
      rw [bindingRangeBag_succ]
      simp only [makeVarls, setGlobals, elistGlobals, opGlobalBag, ih]
      funext key
      simp [unionGlobalBag, emptyGlobalBag]

private theorem unionEmptyL (bag : GlobalBag) : unionGlobalBag emptyGlobalBag bag = bag := by
  funext key
  simp [unionGlobalBag, emptyGlobalBag]

private theorem unionEmptyR (bag : GlobalBag) : unionGlobalBag bag emptyGlobalBag = bag := by
  funext key
  simp [unionGlobalBag, emptyGlobalBag]

/-- Declaration output writes precisely the consecutive allocated global slots. -/
theorem compileDecs_globals (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) :
    (ds : List Dec) → elistGlobals (compileDecs t n next env envs ds).2.2.2.2 =
      bindingRangeBag next.vidx (numBindingsList ds)
  | [] => by simp [compileDecs, elistGlobals, numBindingsList, bindingRangeBag_zero]
  | [d] => by
    cases d with
    | dlet loc p e =>
      cases h : simpleDlet p e with
      | some value =>
        obtain ⟨pv, v⟩ := value
        cases lookup : NamespaceHOL.nsLookup env.v v <;>
          simp [compileDecs, numBindingsList, numBindings, h, lookup, elistGlobals, bindingRangeBag_zero]
        case some name => cases name <;> simp [elistGlobals]
      | none =>
        have he := compileExp_globalSafe ((patBindings p).reverse ++ t) env e
        simp [compileDecs, h, numBindingsList, numBindings, elistGlobals, setGlobals,
          rowGlobals, setGlobals_makeVarls, he.2, unionEmptyL, unionEmptyR]
    | dletrec loc funs =>
      let names := funs.map Prod.fst
      let newEnv := NamespaceHOL.nsBindList (names.map fun x => (x, VarName.localName .none x)) env.v
      have hf := compileFuns_globalSafe t { env with v := newEnv } funs
      simp only [newEnv, names, List.map_map] at hf
      simp [compileDecs, numBindingsList, numBindings, elistGlobals, setGlobals,
        setGlobals_makeVarls, hf.2, unionEmptyR]
    | dtype loc types => simp [compileDecs, numBindingsList, numBindings, elistGlobals, bindingRangeBag_zero]
    | dtabbrev loc vars name typ => simp [compileDecs, numBindingsList, numBindings, elistGlobals, bindingRangeBag_zero]
    | dexn loc name types => simp [compileDecs, numBindingsList, numBindings, elistGlobals, bindingRangeBag_zero]
    | dmod name ds =>
      have h := compileDecs_globals (name :: t) n next env envs ds
      generalize hc : compileDecs (name :: t) n next env envs ds = result
      obtain ⟨n', next', env', envs', code⟩ := result
      simp only [hc] at h
      simpa [compileDecs, hc, numBindingsList, numBindings] using h
    | dlocal locals body =>
      have hlocal := compileDecs_globals t n next env envs locals
      have hcount := compileDecs_bindingCount t n next env envs locals
      generalize hc : compileDecs t n next env envs locals = first
      obtain ⟨n', next', env', envs', code⟩ := first
      simp only [hc] at hlocal hcount
      have hbody := compileDecs_globals t n' next' (extendEnv env' env) envs' body
      generalize hb : compileDecs t n' next' (extendEnv env' env) envs' body = second
      obtain ⟨n'', next'', env'', envs'', bodyCode⟩ := second
      simp only [hb] at hbody
      simp only [compileDecs, hc, hb, numBindingsList, numBindings, Nat.add_zero, elistGlobals_append]
      rw [hlocal, hbody, hcount, bindingRangeBag_add]
    | denv name =>
      simp [compileDecs, numBindingsList, numBindings, elistGlobals, setGlobals, opGlobalBag,
        envIdTuple, bindingRangeBag_succ, bindingRangeBag_zero, unionEmptyL, unionEmptyR]
  | d :: d2 :: ds => by
    have hfirst := compileDecs_globals t n next env envs [d]
    have hcount := compileDecs_bindingCount t n next env envs [d]
    generalize hc : compileDecs t n next env envs [d] = first
    obtain ⟨n', next', env', envs', code⟩ := first
    simp only [hc, numBindingsList, Nat.add_zero] at hfirst hcount
    have hrest := compileDecs_globals t n' next' (extendEnv env' env) envs' (d2 :: ds)
    generalize hr : compileDecs t n' next' (extendEnv env' env) envs' (d2 :: ds) = rest
    obtain ⟨n'', next'', env'', envs'', restCode⟩ := rest
    simp only [hr, numBindingsList] at hrest
    simp only [compileDecs, hc, hr, numBindingsList, elistGlobals_append]
    rw [hfirst, hrest, hcount, ← bindingRangeBag_add]
termination_by ds => sizeOf ds
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have positive : 0 < sizeOf d2 := by cases d2 <;> simp <;> omega
       omega)

/-- The generated declaration bag is exactly the source binding-count range. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_decs_elist_globals"]
theorem compileDecs_elistGlobals (t : List MlString) (n : Nat) (next : NextIndices)
    (env : Environment) (envs : EnvironmentGenerationStore) (ds : List Dec)
    (n' : Nat) (next' : NextIndices) (env' : Environment)
    (envs' : EnvironmentGenerationStore) (code : List FlatLang.Exp)
    (compiled : compileDecs t n next env envs ds = (n', next', env', envs', code)) :
    elistGlobals code = bindingRangeBag next.vidx (ds.map numBindings).sum := by
  have h := compileDecs_globals t n next env envs ds
  simp only [compiled] at h
  simpa only [numBindingsList_eq_sum] using h

/-- Elimination and pattern compilation cannot increase global-write counts. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_flat_sub_bag"]
theorem compileFlat_subBag (cfg : FlatPattern.Config) (p : List FlatLang.Exp) :
    ∀ key, elistGlobals (compileFlatTotal cfg p) key ≤ elistGlobals p key := by
  intro key
  have pattern := FlatPattern.compileDecs_elistGlobals cfg (FlatElim.removeFlatProgTotal p) key
  have elim := FlatElim.removeFlatProg_subBag p key
    (elistGlobals (FlatElim.removeFlatProgTotal p) key) (Nat.le_refl _)
  exact Nat.le_trans pattern elim

private theorem bindingRangeBag_distinct (start count : Nat) :
    ∀ key, bindingRangeBag start count key ≤ 1 := by
  have inj : Function.Injective (start + ·) := fun _ _ h => Nat.add_left_cancel h
  have nd : ((List.range count).map (start + ·)).Nodup := List.Nodup.map inj List.nodup_range
  exact List.nodup_iff_count.mp nd

private theorem bindingRangeBag_below (start count key : Nat) (below : key < start) :
    bindingRangeBag start count key = 0 := by
  apply List.count_eq_zero_of_not_mem
  intro member
  obtain ⟨i, _, equal⟩ := List.mem_map.mp member
  omega

/-- The complete source-to-flat compiler initializes each global at most once. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "compile_globals_BAG_ALL_DISTINCT"]
theorem compile_globals_distinct (c : Config) (p : List Dec) :
    FlatElim.globalBagDistinct (elistGlobals (compileTotal c p).2) := by
  let next := { c.next with vidx := c.next.vidx + 1 }
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have body := compileDecs_globals [] 1 next c.modEnv envs p
  generalize hc : compileDecs [] 1 next c.modEnv envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at body
  intro key
  have bound := compileFlat_subBag c.patternCfg (globAlloc next' c :: allocEnvRef :: code) key
  have program : (compileTotal c p).2 =
      compileFlatTotal c.patternCfg (globAlloc next' c :: allocEnvRef :: code) := by
    simp only [next, envs] at hc
    simp [compileTotal, compileProg, hc]
  rw [program]
  apply Nat.le_trans bound
  have distinct := bindingRangeBag_distinct next.vidx (numBindingsList p) key
  have zero := bindingRangeBag_below next.vidx (numBindingsList p) 0 (by simp [next])
  simp only [elistGlobals, globAlloc, allocEnvRef, setGlobals, opGlobalBag,
    body, unionGlobalBag, emptyGlobalBag]
  by_cases eq : key = 0
  · subst key
    simp [zero]
  · simp [eq]
    exact distinct

/-- Incremental source-to-flat compilation also initializes each slot at most once. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_globals_BAG_ALL_DISTINCT"]
theorem incCompile_globals_distinct (envId : Nat × Nat) (c : Config) (p : List Dec) :
    FlatElim.globalBagDistinct (elistGlobals (incCompile envId c p).2) := by
  let env := lookupEnvId envId c.envs
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have body := compileDecs_globals [] 1 c.next env envs p
  generalize hc : compileDecs [] 1 c.next env envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at body
  intro key
  have bound := FlatPattern.compileDecs_elistGlobals c.patternCfg
    (globAlloc next' c :: (code ++ [storeEnvId envs'.generation envs'.next])) key
  have program : (incCompile envId c p).2 =
      (globAlloc next' c :: (code ++ [storeEnvId envs'.generation envs'.next])).map
        (FlatPattern.compileDec c.patternCfg) := by
    simp only [env, envs] at hc
    simp [incCompile, incCompileProg, hc]
  rw [program]
  apply Nat.le_trans bound
  have distinct := bindingRangeBag_distinct c.next.vidx (numBindingsList p) key
  simp only [elistGlobals, globAlloc, storeEnvId, setGlobals, opGlobalBag,
    envIdTuple, elistGlobals_append, body, unionGlobalBag, emptyGlobalBag]
  simpa using distinct

end Flapjack.Compiler.Backend.SourceToFlat
