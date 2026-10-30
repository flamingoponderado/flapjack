import Flapjack.Compiler.Backend.SourceToFlat.Proofs.BindingGlobals
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic

/-! Monotonicity of global slots across stateful incremental compilation. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.BackendProps

private theorem rangeBag_member (start count key : Nat)
    (positive : 0 < bindingRangeBag start count key) : start ≤ key ∧ key < start + count := by
  have member : key ∈ (List.range count).map (start + ·) := List.count_pos_iff.mp positive
  obtain ⟨i, imem, rfl⟩ := List.mem_map.mp member
  have less : i < count := List.mem_range.mp imem
  omega

private theorem globals_append (xs ys : List FlatLang.Exp) :
    elistGlobals (xs ++ ys) = unionGlobalBag (elistGlobals xs) (elistGlobals ys) := by
  induction xs with
  | nil => funext key; simp [elistGlobals, emptyGlobalBag, unionGlobalBag]
  | cons x xs ih =>
    simp only [List.cons_append, elistGlobals, ih]
    funext key
    simp only [unionGlobalBag]
    omega

/-- Every incremental compilation initializes slots inside its allocated range. -/
theorem incCompile_globals_range (envId : Nat × Nat) (c : Config) (p : List Dec) :
    let result := incCompile envId c p
    c.next.vidx ≤ result.1.next.vidx ∧
      ∀ key, 0 < elistGlobals result.2 key →
        c.next.vidx ≤ key ∧ key < result.1.next.vidx := by
  let env := lookupEnvId envId c.envs
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have body := compileDecs_globals [] 1 c.next env envs p
  have count := compileDecs_bindingCount [] 1 c.next env envs p
  generalize hc : compileDecs [] 1 c.next env envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at body count
  have outCode : (incCompile envId c p).2 =
      (globAlloc next' c :: (code ++ [storeEnvId envs'.generation envs'.next])).map
        (FlatPattern.compileDec c.patternCfg) := by
    simp only [env, envs] at hc
    simp [incCompile, incCompileProg, hc]
  have outNext : (incCompile envId c p).1.next = next' := by
    simp only [env, envs] at hc
    simp [incCompile, incCompileProg, hc]
  change c.next.vidx ≤ (incCompile envId c p).1.next.vidx ∧
    ∀ key, 0 < elistGlobals (incCompile envId c p).2 key →
      c.next.vidx ≤ key ∧ key < (incCompile envId c p).1.next.vidx
  rw [outNext, outCode]
  constructor
  · omega
  · intro key positive
    have bound := FlatPattern.compileDecs_elistGlobals c.patternCfg
      (globAlloc next' c :: (code ++ [storeEnvId envs'.generation envs'.next])) key
    have h : 0 < bindingRangeBag c.next.vidx (numBindingsList p) key := by
      simp only [elistGlobals, globAlloc, storeEnvId, setGlobals, opGlobalBag, envIdTuple,
        globals_append, body, unionGlobalBag, emptyGlobalBag] at bound
      simp only [globAlloc, storeEnvId, envIdTuple] at positive
      omega
    have range := rangeBag_member c.next.vidx (numBindingsList p) key h
    omega

/-- Every initial compilation write is below its resulting variable counter. -/
theorem compileTotal_globals_range (c : Config) (p : List Dec) :
    ∀ key, 0 < elistGlobals (compileTotal c p).2 key → key < (compileTotal c p).1.next.vidx := by
  let next := { c.next with vidx := c.next.vidx + 1 }
  let envs : EnvironmentGenerationStore := { next := 0, generation := c.envs.next, envs := .ln }
  have body := compileDecs_globals [] 1 next c.modEnv envs p
  have count := compileDecs_bindingCount [] 1 next c.modEnv envs p
  generalize hc : compileDecs [] 1 next c.modEnv envs p = result
  obtain ⟨n', next', env', envs', code⟩ := result
  simp only [hc] at body count
  have outCode : (compileTotal c p).2 =
      compileFlatTotal c.patternCfg (globAlloc next' c :: allocEnvRef :: code) := by
    simp only [next, envs] at hc
    simp [compileTotal, compileProg, hc]
  have outNext : (compileTotal c p).1.next = next' := by
    simp only [next, envs] at hc
    simp [compileTotal, compileProg, hc]
  intro key positive
  rw [outCode] at positive
  rw [outNext]
  have bound := compileFlat_subBag c.patternCfg (globAlloc next' c :: allocEnvRef :: code) key
  simp only [elistGlobals, globAlloc, allocEnvRef, setGlobals, opGlobalBag, body,
    unionGlobalBag, emptyGlobalBag] at bound
  simp only [globAlloc, allocEnvRef] at positive
  by_cases zero : key = 0
  · subst key
    simp only [next] at count
    omega
  · have h : 0 < bindingRangeBag next.vidx (numBindingsList p) key := by
      simp only [zero, ↓reduceIte] at bound
      omega
    have range := rangeBag_member next.vidx (numBindingsList p) key h
    omega

/-- Successor-shifted global indices written by a flat declaration list. -/
def shiftedGlobalWrites (program : List FlatLang.Exp) : Set Nat :=
  { x | ∃ key, 0 < elistGlobals program key ∧ x = key + 1 }

/-- Successive incremental compilations allocate strictly increasing global slots. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "monotonic_globals_state_co_compile"]
theorem monotonicGlobals_stateCoCompile {C P : Type} (conf conf' : Config)
    (prog : List Dec) (p : List FlatLang.Exp) (transform : P → List Dec)
    (oracle : Nat → (Config × C) × ((Nat × Nat) × P))
    (premises : compileTotal conf prog = (conf', p) ∧ (oracle 0).1.1 = conf' ∧
      isStateOracle (fun c input => incCompile input.1 c (transform input.2)) oracle) :
    oracleMonotonic (fun entry : C × List FlatLang.Exp => shiftedGlobalWrites entry.2)
      (· < ·) (insert 0 (shiftedGlobalWrites p))
      (stateCo (fun c input => incCompile input.1 c (transform input.2)) oracle) := by
  obtain ⟨compiled, initial, isOracle⟩ := premises
  apply oracleMonotonic_stateWithInv (fun _ => True) (fun c : Config => c.next.vidx + 1)
  refine ⟨trivial, ?_, ?_, isOracle⟩
  · intro x member
    simp only [Set.mem_insert_iff] at member
    rcases member with rfl | ⟨key, positive, rfl⟩
    · omega
    · have h := compileTotal_globals_range conf prog key
      simp only [compiled] at h
      have bound := h positive
      rw [initial]
      omega
  · intro st input st' output h
    obtain ⟨equation, _⟩ := h
    have range := incCompile_globals_range input.1 st (transform input.2)
    simp only [equation] at range
    refine ⟨trivial, ?_, ?_⟩
    · omega
    · intro cfg x member
      obtain ⟨key, positive, rfl⟩ := member
      have limits := range.2 key positive
      omega

end Flapjack.Compiler.Backend.SourceToFlat
