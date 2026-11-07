import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialNames
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ProgramAgreement

/-! Initial state relation for the BVL-to-BVI compiler. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The initial source state and the target state produced by the global
initializer satisfy the BVL-to-BVI state relation. Untagged pending BVI
evaluator and dispatcher correspondence review. -/
theorem initial_stateRel {C F : Type} (start n counter clock : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp)) (oracle : BvlSem.CompileOracle (Nat × C))
    (compiler : BviSem.Compiler C) (relocate : Nat → Nat)
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : ∀ name arity body, (name, arity, body) ∈ programs → BvlHandle.Proofs.handleOk [body])
    (oracleHandlers : ∀ index name arity body,
      (name, arity, body) ∈ (oracle index).2 → BvlHandle.Proofs.handleOk [body])
    (counterBound : (compileIncSource counter programs).1 ≤ (oracle 0).1.1) :
    let compiled := (compileIncSource counter programs).2
    let source := BvlSem.initialState ffi (sptFromAList programs) oracle
      (BackendProps.stateCc compileIncSource compiler) clock
    let target : BviSem.BviState C F := {
      BviSem.initialState ffi (sptFromAList (stubs start n ++ compiled))
        (BackendProps.stateCo compileIncSource oracle) compiler clock with
      global := some 0
      refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
        (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }
    stateRel relocate source target := by
  let compiled := (compileIncSource counter programs).2
  let tree := sptFromAList (stubs start n ++ compiled)
  let source := BvlSem.initialState ffi (sptFromAList programs) oracle
    (BackendProps.stateCc compileIncSource compiler) clock
  let target : BviSem.BviState C F := { BviSem.initialState ffi tree (BackendProps.stateCo compileIncSource oracle) compiler clock with
    global := some 0
    refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
      (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }
  change stateRel relocate source target
  have stubLookups := lookup_staticStubs start n compiled
  have names := namesOk_initial start n counter programs oracle oracleHandlers counterBound
  have entries := initial_code_correspondence start n counter programs distinct handlers
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact refsRel_empty_source relocate target.refs
  · rfl
  · intro ptr global
    have ptrEq : ptr = 0 := by simpa [target] using global.symm
    subst ptr
    refine ⟨?_, initGlobalsCapacity n, ?_, ?_⟩
    · intro key present
      simp [source, BvlSem.initialState, HolFiniteMapExact.empty] at present
    · simp [target, source, BvlSem.initialState,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have positive := initGlobalsCapacity_positive n
      simp only [source, BvlSem.initialState, List.length_nil, Nat.zero_add]
      omega
  · rfl
  · rfl
  · rfl
  · exact stubLookups.1
  · exact stubLookups.2.1
  · exact stubLookups.2.2.1
  · exact stubLookups.2.2.2.1
  · exact stubLookups.2.2.2.2.1
  · exact stubLookups.2.2.2.2.2.1
  · exact stubLookups.2.2.2.2.2.2
  · exact names
  · exact entries

/-- Evaluation of the compiled initial program simulates the source entry
call, including initialization and top-level exception handling. Untagged
pending evaluator and dispatcher correspondence review. -/
theorem compileProgramEvaluate {C F : Type} (start n counter clock : Nat) (ffi : HolFfiState F)
    (programs : List (Nat × Nat × Bvl.Exp)) (oracle : BvlSem.CompileOracle (Nat × C))
    (compiler : BviSem.Compiler C) (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (next : BvlSem.State (Nat × C) F)
    (run : BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock) = (res, next))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : ∀ name arity body, (name, arity, body) ∈ programs → BvlHandle.Proofs.handleOk [body])
    (oracleHandlers : ∀ index name arity body,
      (name, arity, body) ∈ (oracle index).2 → BvlHandle.Proofs.handleOk [body])
    (counterBound : (compileIncSource counter programs).1 ≤ (oracle 0).1.1)
    (notTypeError : res ≠ .err (.abort .typeError)) :
    ∃ extra newRelocate targetNext,
      BviSem.evaluate [.call 0 (some initGlobalsLocation) [] none] []
        (BviSem.initialState ffi
          (sptFromAList (stubs (bvlNumStubs + bvlToBviNamespaces * start) n ++ (compileIncSource counter programs).2))
          (BackendProps.stateCo compileIncSource oracle) compiler (clock + extra)) =
      (mapSimulationResult newRelocate (match res with
        | .err (.raise value) => .val [value]
        | other => other), targetNext) ∧
      stateRel newRelocate next targetNext := by
  let source := BvlSem.initialState ffi (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock
  let entry := bvlNumStubs + bvlToBviNamespaces * start
  let compiled := (compileIncSource counter programs).2
  have related := initial_stateRel entry n counter clock ffi programs oracle compiler id distinct handlers oracleHandlers counterBound
  have sourceOk : stateOk source := initialState_ok ffi (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock
  obtain ⟨extra, newRelocate, targetNext, targetRun, finalRel⟩ :=
    compileEntryWithInit start n clock ffi compiled (BackendProps.stateCo compileIncSource oracle) compiler
      source next res id run sourceOk notTypeError related
  refine ⟨extra + 1, newRelocate, targetNext, ?_, finalRel⟩
  cases res with
  | val values => simpa [compiled, Nat.add_assoc, BviSem.initialState] using targetRun
  | err error => cases error <;> simpa [compiled, Nat.add_assoc, BviSem.initialState] using targetRun

/-- Executed whole-program compilation agrees with the source-shaped
incremental program and preserves its fresh-name counter. -/
theorem compileProgFuel_eq_source (fuel optFuel start counter : Nat) (programs : List (Nat × Nat × Bvl.Exp)) :
    compileProgFuel fuel optFuel start counter programs = some
      (initGlobalsLocation,
        stubs (bvlNumStubs + bvlToBviNamespaces * start)
          (globalCountList (programs.map (fun (_, _, body) => body))) ++ (compileIncSource counter programs).2,
        (compileIncSource counter programs).1) := by
  rcases sourceRun : compileProgramsSource counter programs with ⟨tree, next⟩
  have fuelRun := compileProgramsFuel_eq_flattened fuel optFuel counter programs
  simp only [sourceRun] at fuelRun
  simp [compileProgFuel, compileIncSource, sourceRun, fuelRun]

/-- The executed whole-program BVL-to-BVI compiler preserves evaluation from
initial states, including the initialization wrapper and top-level exception
handling. Untagged pending BVI evaluator and dispatcher review. -/
theorem compileProgFuelEvaluate {C F : Type} (fuel optFuel start counter clock : Nat)
    (ffi : HolFfiState F) (programs : List (Nat × Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle (Nat × C)) (compiler : BviSem.Compiler C)
    (targetStart targetNextName : Nat) (targetProgram : List (Nat × Nat × Bvi.Exp))
    (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (next : BvlSem.State (Nat × C) F)
    (compiled : compileProgFuel fuel optFuel start counter programs = some (targetStart, targetProgram, targetNextName))
    (run : BvlSem.evaluate [.call 0 (some start) []] []
      (BvlSem.initialState ffi (sptFromAList programs) oracle (BackendProps.stateCc compileIncSource compiler) clock) = (res, next))
    (distinct : (programs.map Prod.fst).Nodup)
    (handlers : BvlHandle.Proofs.handleOk (programs.map (fun (_, _, body) => body)))
    (oracleHandlers : ∀ index, BvlHandle.Proofs.handleOk ((oracle index).2.map (fun (_, _, body) => body)))
    (counterBound : targetNextName ≤ (oracle 0).1.1)
    (notTypeError : res ≠ .err (.abort .typeError)) :
    ∃ extra newRelocate targetNext,
      BviSem.evaluate [.call 0 (some targetStart) [] none] []
        (BviSem.initialState ffi (sptFromAList targetProgram)
          (BackendProps.stateCo compileIncSource oracle) compiler (clock + extra)) =
      (mapSimulationResult newRelocate (match res with
        | .err (.raise value) => .val [value]
        | other => other), targetNext) ∧
      stateRel newRelocate next targetNext := by
  rw [compileProgFuel_eq_source] at compiled
  simp only [Option.some.injEq, Prod.mk.injEq] at compiled
  obtain ⟨rfl, rfl, rfl⟩ := compiled
  have sourceHandlers : ∀ name arity body, (name, arity, body) ∈ programs → BvlHandle.Proofs.handleOk [body] := by
    intro name arity body member
    apply (BvlHandle.Proofs.handleOk_every _).1 handlers body
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  have futureHandlers : ∀ index name arity body,
      (name, arity, body) ∈ (oracle index).2 → BvlHandle.Proofs.handleOk [body] := by
    intro index name arity body member
    apply (BvlHandle.Proofs.handleOk_every _).1 (oracleHandlers index) body
    exact List.mem_map.mpr ⟨(name, arity, body), member, rfl⟩
  obtain ⟨extra, newRelocate, targetNext, targetRun, finalRel⟩ :=
    compileProgramEvaluate start (globalCountList (programs.map (fun (_, _, body) => body))) counter clock ffi
      programs oracle compiler res next run distinct sourceHandlers futureHandlers counterBound notTypeError
  refine ⟨extra, newRelocate, targetNext, ?_, finalRel⟩
  cases res with
  | val values => exact targetRun
  | err error => cases error <;> exact targetRun

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
