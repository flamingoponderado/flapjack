import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialStateRel
import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteSimulation

/-! Namespace conditions at the BVL-to-BVI and tail-recursion boundary. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BviTailrec

/-- A worker-namespace label cannot coincide with a name outside that
namespace. This Flapjack helper supports the pass-boundary invariant. -/
theorem freeNames_of_not_worker (next name : Nat)
    (worker : inWorkerNamespace next) (outside : ¬inWorkerNamespace name) : freeNames next name := by
  intro k equal
  apply outside
  rw [← equal]
  unfold inWorkerNamespace at worker ⊢
  simpa [Nat.add_mod, Flapjack.bvlToBviNamespaces] using worker

/-- Distinct program names outside the worker namespace satisfy the
tail-recursion input condition. Names below the stub boundary are already
below the next worker label. -/
theorem tailrec_inputCondition_of_names (next : Nat) (program : List (Nat × Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (nextBound : bvlNumStubs ≤ next) (worker : inWorkerNamespace next)
    (outside : ∀ entry ∈ program, bvlNumStubs ≤ entry.1 → ¬inWorkerNamespace entry.1) :
    inputCondition next program := by
  refine ⟨?_, distinct, ?_, nextBound, worker⟩
  · intro entry member
    by_cases below : entry.1 < bvlNumStubs
    · exact freeNames_of_lt next entry.1 (by omega)
    · exact freeNames_of_not_worker next entry.1 worker (outside entry member (by omega))
  · intro entry member
    obtain ⟨member, above⟩ := List.mem_filter.mp member
    exact outside entry member (by simpa using above)

/-- Incremental BVL-to-BVI compilation emits names only in the input and
auxiliary namespaces, never in the tail-recursion worker namespace. -/
theorem compileIncSource_outside_tailrec_namespace (counter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (name : Nat)
    (member : name ∈ (compileIncSource counter program).2.map Prod.fst) :
    ¬inWorkerNamespace name := by
  rcases compileIncSource_nameRange counter program name member with
    ⟨_, _, equal⟩ | ⟨_, _, _, equal⟩
  all_goals
    rw [equal]
    unfold inWorkerNamespace
    have stubMod := bvlNumStubMod
    simp only [bvlToBviNamespaces] at stubMod ⊢
    omega

/-- Incremental lowering supplies the tail-recursion input invariant when
the source function names are distinct and the worker counter is valid.
This source-shaped boundary result is untagged pending carrier review. -/
theorem compileIncSource_tailrec_inputCondition (counter next : Nat)
    (program : List (Nat × Nat × Bvl.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (nextBound : bvlNumStubs ≤ next) (worker : inWorkerNamespace next) :
    inputCondition next (compileIncSource counter program).2 := by
  apply tailrec_inputCondition_of_names next (compileIncSource counter program).2
    (compileIncSource_names_nodup counter program distinct) nextBound worker
  intro entry member _
  exact compileIncSource_outside_tailrec_namespace counter program entry.1
    (List.mem_map.mpr ⟨entry, member, rfl⟩)

/-- The runtime stubs occupy distinct labels. -/
theorem stubs_names_nodup (start count : Nat) :
    ((stubs start count).map Prod.fst).Nodup := by
  simp [stubs, allocGlobalLocation, copyGlobalsLocation, initGlobalsLocation, listLengthLocation,
    fromListByteLocation, toListByteLocation, sumListLengthLocation, concatByteLocation]
  omega

/-- Runtime stubs and lowered functions have pairwise distinct labels when
the original program does. -/
theorem stubs_append_compileIncSource_names_nodup (start count counter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (distinct : (program.map Prod.fst).Nodup) :
    ((stubs start count ++ (compileIncSource counter program).2).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨stubs_names_nodup start count, compileIncSource_names_nodup counter program distinct, ?_⟩
  intro name stubMember other compiledMember same
  subst other
  obtain ⟨stub, member, equal⟩ := List.mem_map.mp stubMember
  have upper := stubs_below_namespace start count stub member
  have lower : bvlNumStubs ≤ name := by
    rcases compileIncSource_nameRange counter program name compiledMember with
      ⟨_, _, label⟩ | ⟨_, _, _, label⟩ <;> rw [label] <;> omega
  omega

/-- The complete initial BVI program, including runtime stubs, meets the
tail-recursion namespace condition. -/
theorem initialProgram_tailrec_inputCondition (start count counter next : Nat)
    (program : List (Nat × Nat × Bvl.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (nextBound : bvlNumStubs ≤ next) (worker : inWorkerNamespace next) :
    inputCondition next (stubs start count ++ (compileIncSource counter program).2) := by
  apply tailrec_inputCondition_of_names next _
    (stubs_append_compileIncSource_names_nodup start count counter program distinct) nextBound worker
  intro entry member above
  rcases List.mem_append.mp member with stub | compiled
  · have below := stubs_below_namespace start count entry stub
    omega
  · exact compileIncSource_outside_tailrec_namespace counter program entry.1
      (List.mem_map.mpr ⟨entry, compiled, rfl⟩)

/-- An executed incremental lowering result meets the tail-recursion input
condition, including the future programs supplied by the compiler oracle. -/
theorem compileIncFuel_tailrec_inputCondition (fuel optFuel counter next last : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (nextBound : bvlNumStubs ≤ next) (worker : inWorkerNamespace next)
    (run : compileIncFuel fuel optFuel counter program = some (last, compiled)) :
    inputCondition next compiled := by
  have equal := (compileIncFuel_eq_source fuel optFuel counter program).symm.trans run
  have codeEq : (compileIncSource counter program).2 = compiled := congrArg Prod.snd (Option.some.inj equal)
  rw [← codeEq]
  exact compileIncSource_tailrec_inputCondition counter next program distinct nextBound worker

/-- The executed initial BVL-to-BVI program, including stubs, meets the
tail-recursion input condition. -/
theorem compileProgFuel_tailrec_inputCondition (fuel optFuel start counter next targetStart targetCounter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (nextBound : bvlNumStubs ≤ next) (worker : inWorkerNamespace next)
    (run : compileProgFuel fuel optFuel start counter program = some (targetStart, compiled, targetCounter)) :
    inputCondition next compiled := by
  have equal := (compileProgFuel_eq_source fuel optFuel start counter program).symm.trans run
  have codeEq :
      stubs (bvlNumStubs + bvlToBviNamespaces * start)
        (globalCountList (program.map (fun (_, _, body) => body))) ++ (compileIncSource counter program).2 =
        compiled := congrArg (fun p => p.2.1) (Option.some.inj equal)
  rw [← codeEq]
  exact initialProgram_tailrec_inputCondition _ _ counter next program distinct nextBound worker

/-- The production tail-recursion counter starts in worker namespace two. -/
theorem production_tailrec_start_valid :
    bvlNumStubs ≤ bvlNumStubs + 2 ∧ inWorkerNamespace (bvlNumStubs + 2) := by
  constructor
  · omega
  · unfold inWorkerNamespace
    have stubMod := bvlNumStubMod
    simp only [bvlToBviNamespaces] at stubMod ⊢
    omega

/-- The production BVL-to-BVI program is ready for tail-recursion
elimination when its source labels are distinct. -/
theorem compileProgFuel_production_tailrec_inputCondition
    (fuel optFuel start counter targetStart targetCounter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (distinct : (program.map Prod.fst).Nodup)
    (run : compileProgFuel fuel optFuel start counter program = some (targetStart, compiled, targetCounter)) :
    inputCondition (bvlNumStubs + 2) compiled :=
  compileProgFuel_tailrec_inputCondition fuel optFuel start counter (bvlNumStubs + 2)
    targetStart targetCounter program compiled distinct production_tailrec_start_valid.1
    production_tailrec_start_valid.2 run

/-- Every future BVL oracle program lowers to a tail-recursion input when
its labels are distinct and its worker counter is valid. -/
theorem lowered_oracle_tailrec_inputCondition {C : Type}
    (oracle : Nat → (Nat × (Nat × C)) × List (Nat × Nat × Bvl.Exp))
    (distinct : ∀ n, ((oracle n).2.map Prod.fst).Nodup)
    (nextBound : ∀ n, bvlNumStubs ≤ (oracle n).1.2.1)
    (worker : ∀ n, inWorkerNamespace (oracle n).1.2.1) :
    ∀ n, inputCondition (BackendProps.stateCo compileIncSource oracle n).1.1
      (BackendProps.stateCo compileIncSource oracle n).2 := by
  intro n
  exact compileIncSource_tailrec_inputCondition (oracle n).1.1 (oracle n).1.2.1
    (oracle n).2 (distinct n) (nextBound n) (worker n)

/-- Every worker-namespace label in a tail-recursion output is below the
returned worker counter, whether the pass is enabled or disabled. -/
theorem tailrec_output_worker_below_counter (fuel : Nat) (enabled : Bool) (next last : Nat)
    (program compiled : List (Nat × Nat × Bvi.Exp)) (condition : inputCondition next program)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, compiled)) :
    ∀ name ∈ compiled.map Prod.fst, inWorkerNamespace name → name < last := by
  cases enabled with
  | false =>
    simp only [BviTailrec.compileProgFuel, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    intro name member worker
    obtain ⟨entry, entryMember, nameEq⟩ := List.mem_map.mp member
    by_cases below : name < bvlNumStubs
    · exact Nat.lt_of_lt_of_le below condition.2.2.2.1
    · have notWorker := condition.2.2.1 entry (List.mem_filter.mpr ⟨entryMember, by simpa [nameEq] using (show bvlNumStubs ≤ name by omega)⟩)
      exact (notWorker (by simpa [nameEq] using worker)).elim
  | true =>
    have equal := (compileEachFuel_eq_source fuel next program).symm.trans (by simpa [BviTailrec.compileProgFuel] using run)
    have pairEq := Option.some.inj equal
    have codeEq : (compileEachSource next program).2 = compiled := congrArg Prod.snd pairEq
    have lastEq : (compileEachSource next program).1 = last := congrArg Prod.fst pairEq
    intro name member worker
    have treeMember : sptMem name (sptFromAList (compileEachSource next program).2) := by
      apply (sptFromAList_mem_iff _ name).mpr
      simpa [codeEq] using member
    have result := compileEachSource_install_worker_bound next program condition name ⟨treeMember, worker⟩
    simpa [lastEq] using result

/-- The actual BVL-to-BVI output can be passed to the production
tail-recursion compiler with its initial namespace conditions discharged.
The future oracle programs still require their own input conditions. -/
theorem lowering_tailrec_semantics {C F : Type}
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered compiled : List (Nat × Nat × Bvi.Exp))
    (last : Nat) (ffi : HolFfiState F) (oracle : BviSem.CompileOracle (Nat × C))
    (compiler : BviSem.Compiler C) (entry : Nat)
    (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : BvlToBvi.compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (last, compiled))
    (oracleCondition : ∀ n, inputCondition (oracle n).1.1 (oracle n).2)
    (counterBound : last ≤ (oracle 0).1.1)
    (notFail : BviSem.semantics ffi (sptFromAList lowered) oracle
      (BackendProps.stateCc (compileProgSource enabled) compiler) entry ≠ .fail) :
    BviSem.semantics ffi (sptFromAList lowered) oracle
        (BackendProps.stateCc (compileProgSource enabled) compiler) entry =
      BviSem.semantics ffi (sptFromAList compiled)
        (BackendProps.stateCo (compileProgSource enabled) oracle) compiler entry := by
  have condition := compileProgFuel_production_tailrec_inputCondition fuel optFuel start counter
    targetStart targetCounter program lowered distinct lowerRun
  have workerBound : ∀ n, n ∈ compiled.map Prod.fst → inWorkerNamespace n → n < (oracle 0).1.1 := by
    intro name member worker
    exact Nat.lt_of_lt_of_le (tailrec_output_worker_below_counter fuel enabled (bvlNumStubs + 2)
      last lowered compiled condition tailRun name member worker) counterBound
  exact BviTailrec.compileProgFuel_semantics fuel enabled (bvlNumStubs + 2) lowered ffi oracle compiler
    entry last compiled condition oracleCondition workerBound tailRun notFail

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
