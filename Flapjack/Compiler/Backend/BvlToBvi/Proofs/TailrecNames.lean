module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.InitialStateRel
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteSimulation
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Namespace

@[expose] public section


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

open Classical in
/-- Whole-program lowering preserves distinct names and the exact auxiliary namespace bounds. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_prog_distinct_locs"]
theorem compileProg_distinctLocs (start n loc final : Nat) (prog : List (Nat × Nat × Bvl.Exp)) (code : List (Nat × Nat × Bvi.Exp))
    (h : compileProgSource start n prog = (loc, code, final) ∧ (prog.map Prod.fst).Nodup) :
    (code.map Prod.fst).Nodup ∧
      (∀ x ∈ (code.map Prod.fst).filter (fun x => decide (inNs 1 (x - bvlNumStubs))),
        bvlToBviNamespaces * n + bvlNumStubs ≤ x ∧ x < bvlToBviNamespaces * final + bvlNumStubs) ∧
      (∀ x ∈ code.map Prod.fst, ¬inNs 2 (x - bvlNumStubs) ∧ ¬inNs 3 (x - bvlNumStubs)) := by
  obtain ⟨run, distinct⟩ := h
  have codeEq : stubs (bvlNumStubs + bvlToBviNamespaces * start)
      (allocGlobCount (prog.map (fun (_, _, body) => body))) ++ (compileIncSource n prog).2 = code := by
    simpa only [compileProgSource, compileIncSource] using congrArg (fun q => q.2.1) run
  have nodup : (code.map Prod.fst).Nodup := by
    rw [← codeEq]
    exact stubs_append_compileIncSource_names_nodup _ _ _ prog distinct
  have domain := compileProg_codeLabelsDomain start n prog loc code final 0 0 run
  have classify (x : Nat) (member : x ∈ code.map Prod.fst) :
      (∃ k, k ∈ prog.map Prod.fst ∧ x = bvlNumStubs + k * bvlToBviNamespaces) ∨
      (∃ k, x = bvlNumStubs + k * bvlToBviNamespaces + 1 ∧ n ≤ k ∧ k < final) ∨
      x ∈ (stubs 0 0).map Prod.fst := by
    have m : x ∈ {a | a ∈ code.map Prod.fst} := member
    rw [domain] at m
    simpa only [Set.mem_union, Set.mem_ofPred_eq, or_assoc] using m
  refine ⟨nodup, ?_, ?_⟩
  · intro x member
    obtain ⟨member, ns⟩ := List.mem_filter.mp member
    have nsProp : inNs 1 (x - bvlNumStubs) := of_decide_eq_true ns
    have nsValue : (x - bvlNumStubs) % 4 = 1 := by simpa [inNs, bvlToBviNamespaces] using nsProp
    rcases classify x member with ⟨k, _, eq⟩ | ⟨k, eq, lo, hi⟩ | stub
    · simp only [bvlToBviNamespaces] at eq
      omega
    · simp only [bvlToBviNamespaces] at eq ⊢
      omega
    · obtain ⟨entry, present, equal⟩ := List.mem_map.mp stub
      have below := stubs_below_namespace 0 0 entry present
      have sub : x - bvlNumStubs = 0 := by omega
      simp [sub] at nsValue
  · intro x member
    rcases classify x member with ⟨k, _, eq⟩ | ⟨k, eq, lo, hi⟩ | stub
    · simp only [inNs, bvlToBviNamespaces] at *
      omega
    · simp only [inNs, bvlToBviNamespaces] at *
      omega
    · obtain ⟨entry, present, equal⟩ := List.mem_map.mp stub
      have below := stubs_below_namespace 0 0 entry present
      have sub : x - bvlNumStubs = 0 := by omega
      simp [inNs, sub]

/-- Lowering avoids tail-recursion worker locations above the stub boundary. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_prog_avoids_nss_2"]
theorem compileProgSource_avoidsNss2 (start counter loc final name : Nat) (prog : List (Nat × Nat × Bvl.Exp))
    (code : List (Nat × Nat × Bvi.Exp))
    (h : compileProgSource start counter prog = (loc, code, final) ∧
      (prog.map Prod.fst).Nodup ∧ name % bvlToBviNamespaces = 2 ∧ name ∈ code.map Prod.fst) :
    name ≤ bvlNumStubs := by
  obtain ⟨run, _, ns, member⟩ := h
  have codeEq : stubs (bvlNumStubs + bvlToBviNamespaces * start)
      (allocGlobCount (prog.map (fun (_, _, body) => body))) ++ (compileIncSource counter prog).2 = code := by
    simpa only [compileProgSource, compileIncSource] using congrArg (fun q => q.2.1) run
  rw [← codeEq, List.map_append, List.mem_append] at member
  rcases member with stub | lowered
  · obtain ⟨entry, present, equal⟩ := List.mem_map.mp stub
    have bound := stubs_below_namespace _ _ entry present
    omega
  · have outside := compileIncSource_outside_tailrec_namespace counter prog name lowered
    exact False.elim (outside ns)

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
theorem tailrec_output_worker_below_counter (enabled : Bool) (next last : Nat)
    (program compiled : List (Nat × Nat × Bvi.Exp)) (condition : inputCondition next program)
    (run : BviTailrec.compileProgSource enabled next program = (last, compiled)) :
    ∀ name ∈ compiled.map Prod.fst, inWorkerNamespace name → name < last := by
  cases enabled with
  | false =>
    simp only [BviTailrec.compileProgSource, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    intro name member worker
    obtain ⟨entry, entryMember, nameEq⟩ := List.mem_map.mp member
    by_cases below : name < bvlNumStubs
    · exact Nat.lt_of_lt_of_le below condition.2.2.2.1
    · have notWorker := condition.2.2.1 entry (List.mem_filter.mpr ⟨entryMember, by simpa [nameEq] using (show bvlNumStubs ≤ name by omega)⟩)
      exact (notWorker (by simpa [nameEq] using worker)).elim
  | true =>
    have pairEq : compileEachSource next program = (last, compiled) := by
      simpa [BviTailrec.compileProgSource] using run
    have codeEq : (compileEachSource next program).2 = compiled := congrArg Prod.snd pairEq
    have lastEq : (compileEachSource next program).1 = last := congrArg Prod.fst pairEq
    intro name member worker
    have treeMember : sptMem name (sptFromAList (compileEachSource next program).2) := by
      apply (sptFromAList_mem_iff _ name).mpr
      simpa [codeEq] using member
    have result := compileEachSource_install_worker_bound next program condition name ⟨treeMember, worker⟩
    simpa [lastEq] using result

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
