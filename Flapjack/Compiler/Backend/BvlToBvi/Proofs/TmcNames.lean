import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TailrecNames
import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeNames

/-! Name conditions between BVI tail-recursion and tail-modulo-cons passes. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Lowered function and auxiliary labels do not occupy TMC's worker
namespace. -/
theorem compileIncSource_outside_tmc_namespace (counter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (name : Nat)
    (member : name ∈ (compileIncSource counter program).2.map Prod.fst) :
    ¬BviTmc.inWorkerNamespace name := by
  rcases compileIncSource_nameRange counter program name member with
    ⟨_, _, equal⟩ | ⟨_, _, _, equal⟩
  all_goals
    rw [equal]
    unfold BviTmc.inWorkerNamespace
    have stubMod := bvlNumStubMod
    simp only [bvlToBviNamespaces] at stubMod ⊢
    omega

/-- The executable initial BVL-to-BVI output has no non-stub labels in
TMC's worker namespace. -/
theorem compileProgFuel_outside_tmc_namespace (fuel optFuel start counter targetStart targetCounter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (run : BvlToBvi.compileProgFuel fuel optFuel start counter program = some (targetStart, compiled, targetCounter)) :
    ∀ name ∈ compiled.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name := by
  have equal := (compileProgFuel_eq_source fuel optFuel start counter program).symm.trans run
  have codeEq :
      stubs (bvlNumStubs + bvlToBviNamespaces * start)
        (globalCountList (program.map (fun (_, _, body) => body))) ++ (compileIncSource counter program).2 =
        compiled := congrArg (fun p => p.2.1) (Option.some.inj equal)
  intro name member above
  rw [← codeEq, List.map_append, List.mem_append] at member
  rcases member with stub | lowered
  · obtain ⟨entry, present, same⟩ := List.mem_map.mp stub
    have below := stubs_below_namespace _ _ entry present
    omega
  · exact compileIncSource_outside_tmc_namespace counter program name lowered

/-- The production TMC counter starts in worker namespace three. -/
theorem production_tmc_start_valid :
    bvlNumStubs ≤ bvlNumStubs + 3 ∧ BviTmc.inWorkerNamespace (bvlNumStubs + 3) := by
  constructor
  · omega
  · unfold BviTmc.inWorkerNamespace
    have stubMod := bvlNumStubMod
    simp only [bvlToBviNamespaces] at stubMod ⊢
    omega

/-- Tail-recursion workers use namespace two, so they cannot occupy the
namespace-three locations reserved for tail-modulo-cons workers. -/
theorem tailrec_output_outside_tmc_namespace (fuel : Nat) (enabled : Bool) (next last : Nat)
    (program output : List (Nat × Nat × Bvi.Exp))
    (worker : BviTailrec.inWorkerNamespace next)
    (outside : ∀ name ∈ program.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, output)) :
    ∀ name ∈ output.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name := by
  cases enabled with
  | false =>
    simp [BviTailrec.compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact outside
  | true =>
    have equal := (BviTailrec.compileEachFuel_eq_source fuel next program).symm.trans
      (by simpa [BviTailrec.compileProgFuel] using run)
    have outputEq : (BviTailrec.compileEachSource next program).2 = output :=
      congrArg Prod.snd (Option.some.inj equal)
    intro name member above
    have sourceMember : name ∈ (BviTailrec.compileEachSource next program).2.map Prod.fst := by
      simpa [outputEq] using member
    rcases BviTailrec.compileEachSource_mem program next name sourceMember with original | ⟨_, _, k, generated⟩
    · exact outside name original above
    · rw [generated]
      unfold BviTailrec.inWorkerNamespace at worker
      unfold BviTmc.inWorkerNamespace
      simp only [bvlToBviNamespaces] at worker ⊢
      omega

/-- Tail-recursion compilation preserves distinct labels under its input
condition. -/
theorem tailrec_output_names_nodup (fuel : Nat) (enabled : Bool) (next last : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (condition : BviTailrec.inputCondition next program)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, output)) :
    (output.map Prod.fst).Nodup := by
  cases enabled with
  | false =>
    simp [BviTailrec.compileProgFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact condition.2.1
  | true =>
    have equal := (BviTailrec.compileEachFuel_eq_source fuel next program).symm.trans
      (by simpa [BviTailrec.compileProgFuel] using run)
    have outputEq : (BviTailrec.compileEachSource next program).2 = output :=
      congrArg Prod.snd (Option.some.inj equal)
    rw [← outputEq]
    apply BviTailrec.compileEachSource_labels_nodup program next condition.2.1
    intro name member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact condition.1 entry entryMember

/-- The tail-recursion output satisfies the TMC input condition once its
no-mutable-allocation invariant is supplied. Establishing preservation of that
invariant by tail-recursion remains a separate proof obligation. -/
theorem tailrec_output_tmc_inputCondition (fuel : Nat) (enabled : Bool) (next last tmcNext : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (condition : BviTailrec.inputCondition next program)
    (outside : ∀ name ∈ program.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name)
    (noMutable : ∀ entry ∈ output, BviTmc.noMutcons entry.2.2)
    (tmcBound : bvlNumStubs ≤ tmcNext) (tmcWorker : BviTmc.inWorkerNamespace tmcNext)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, output)) :
    BviTmc.inputCondition tmcNext output := by
  apply BviTmc.inputCondition_of_names tmcNext output (tailrec_output_names_nodup fuel enabled next last program output condition run)
    noMutable tmcBound tmcWorker
  intro entry member above
  exact tailrec_output_outside_tmc_namespace fuel enabled next last program output condition.2.2.2.2 outside run
    entry.1 (List.mem_map.mpr ⟨entry, member, rfl⟩) above

/-- Production lowering followed by tail-recursion satisfies all TMC input
conditions except that no-mutable-allocation preservation is still supplied
as a premise. -/
theorem lowered_tailrec_tmc_inputCondition (fuel optFuel start counter targetStart targetCounter : Nat)
    (enabled : Bool) (program : List (Nat × Nat × Bvl.Exp))
    (lowered output : List (Nat × Nat × Bvi.Exp)) (last : Nat)
    (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : BvlToBvi.compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (last, output))
    (noMutable : ∀ entry ∈ output, BviTmc.noMutcons entry.2.2) :
    BviTmc.inputCondition (bvlNumStubs + 3) output := by
  have tailCondition := compileProgFuel_production_tailrec_inputCondition fuel optFuel start counter
    targetStart targetCounter program lowered distinct lowerRun
  have outside := compileProgFuel_outside_tmc_namespace fuel optFuel start counter targetStart targetCounter
    program lowered lowerRun
  exact tailrec_output_tmc_inputCondition fuel enabled (bvlNumStubs + 2) last (bvlNumStubs + 3)
    lowered output tailCondition outside noMutable production_tmc_start_valid.1 production_tmc_start_valid.2 tailRun

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
