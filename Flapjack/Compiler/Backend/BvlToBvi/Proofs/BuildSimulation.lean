import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileStringCmp

/-! Relocation simulation for BVL constant construction. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Building one constant part extends the relocation only when allocating a
string, and preserves the full state relation. -/
theorem doPart_simulation {C F : Type} (part : ClosLang.ConstPart) (m : Nat → Value)
    (relocate : Nat → Nat) (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target) (ok : stateOk source) :
    ∃ extended : Nat → Nat,
      (BvlSem.doPart (fun k => adjustBv relocate (m k)) part target.refs).1 =
        adjustBv extended (BvlSem.doPart m part source.refs).1 ∧
      stateRel extended { source with refs := (BvlSem.doPart m part source.refs).2 }
        { target with refs := (BvlSem.doPart (fun k => adjustBv relocate (m k)) part target.refs).2 } ∧
      (∀ key, source.refs.lookup key ≠ none → relocate key = extended key) := by
  cases part with
  | int number =>
    exact ⟨relocate, by simp [BvlSem.doPart, adjustBv], by simpa [BvlSem.doPart] using related, by simp⟩
  | w64 word =>
    exact ⟨relocate, by simp [BvlSem.doPart, adjustBv], by simpa [BvlSem.doPart] using related, by simp⟩
  | con tag indices =>
    refine ⟨relocate, ?_, by simpa [BvlSem.doPart] using related, by simp⟩
    simp [BvlSem.doPart, adjustBv_block, List.map_map]
  | str text =>
    obtain ⟨extended, keyEq, agree, allocated⟩ := stateRel_allocateFresh relocate source target
      (BvlSem.leastUnusedRef source.refs) (BvlSem.leastUnusedRef target.refs)
      (.byteArray true text.explode) related ok (BvlSem.leastUnusedRef_unused source.refs)
      (BvlSem.leastUnusedRef_unused target.refs)
    refine ⟨extended, ?_, ?_, agree⟩
    · simp [BvlSem.doPart, adjustBv, keyEq]
    · simpa [BvlSem.doPart, adjustRef] using allocated

/-- Sequential constant construction preserves relocation and the state
relation, including references introduced by earlier string parts. -/
theorem doBuild_simulation {C F : Type} (parts : List ClosLang.ConstPart)
    (m : Nat → Value) (index : Nat) (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (related : stateRel relocate source target) (ok : stateOk source)
    (valuesOk : ∀ key, bvOk source.refs (m key)) :
    ∃ extended : Nat → Nat,
      (BvlSem.doBuild (fun k => adjustBv relocate (m k)) index parts target.refs).1 =
        adjustBv extended (BvlSem.doBuild m index parts source.refs).1 ∧
      stateRel extended { source with refs := (BvlSem.doBuild m index parts source.refs).2 }
        { target with refs := (BvlSem.doBuild (fun k => adjustBv relocate (m k)) index parts target.refs).2 } ∧
      (∀ key, source.refs.lookup key ≠ none → relocate key = extended key) := by
  induction parts generalizing m index relocate source target with
  | nil =>
    exact ⟨relocate, by simp [BvlSem.doBuild], by simpa [BvlSem.doBuild] using related, by simp⟩
  | cons part parts ih =>
    rcases sourcePart : BvlSem.doPart m part source.refs with ⟨sourceValue, sourceRefs⟩
    rcases targetPart : BvlSem.doPart (fun k => adjustBv relocate (m k)) part target.refs with ⟨targetValue, targetRefs⟩
    obtain ⟨middleRelocate, valueEq, relatedPart, agreePart⟩ := doPart_simulation part m relocate source target related ok
    simp only [sourcePart, targetPart] at valueEq relatedPart
    have partOk := doPart_ok m part source ok valuesOk
    rw [sourcePart] at partOk
    have subset : ∀ key, source.refs.lookup key ≠ none → sourceRefs.lookup key ≠ none := by
      intro key present
      have growth := BvlProps.doPart_refs_mono m part source.refs key present
      simpa [sourcePart] using growth
    let nextMap := fun k => if k = index then sourceValue else m k
    have nextValuesOk : ∀ key, bvOk sourceRefs (nextMap key) := by
      intro key
      dsimp [nextMap]
      split
      · exact partOk.2
      · exact bvOk_domain_mono source.refs (m key) sourceRefs (valuesOk key) subset
    have mapEq : (fun k => if k = index then targetValue else adjustBv relocate (m k)) =
        (fun k => adjustBv middleRelocate (nextMap k)) := by
      funext key
      dsimp [nextMap]
      split
      · exact valueEq
      · exact adjustBv_eq_of_ok relocate (m key) middleRelocate source.refs (valuesOk key) agreePart
    obtain ⟨extended, valueResult, relatedResult, agreeResult⟩ :=
      ih nextMap (index + 1) middleRelocate { source with refs := sourceRefs }
        { target with refs := targetRefs } relatedPart partOk.1 nextValuesOk
    have agree : ∀ key, source.refs.lookup key ≠ none → relocate key = extended key := by
      intro key present
      exact (agreePart key present).trans (agreeResult key (subset key present))
    refine ⟨extended, ?_, ?_, agree⟩
    · simpa [BvlSem.doBuild, sourcePart, targetPart, mapEq, nextMap] using valueResult
    · simpa [BvlSem.doBuild, sourcePart, targetPart, mapEq, nextMap] using relatedResult

/-- A nullary constant build satisfies pass simulation, including all string
allocations. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_build_empty {C F : Type} (parts : List ClosLang.ConstPart) (env : List Value)
    (source : BvlSem.State (Nat × C) F) :
    simulation [.op (.blockOp (.build parts)) []] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases sourceBuild : BvlSem.doBuildConst parts source.refs with ⟨sourceValue, sourceRefs⟩
  rcases targetBuild : BvlSem.doBuildConst parts target.refs with ⟨targetValue, targetRefs⟩
  have zerosOk : ∀ key, bvOk source.refs ((fun _ : Nat => Value.number 0) key) := by simp [bvOk]
  obtain ⟨extended, valueEq, relatedBuild, agree⟩ :=
    doBuild_simulation parts (fun _ => .number 0) 0 relocate source target related sourceOk zerosOk
  simp only [adjustBv] at valueEq relatedBuild
  change (BvlSem.doBuildConst parts target.refs).1 = adjustBv extended (BvlSem.doBuildConst parts source.refs).1 at valueEq
  change stateRel extended { source with refs := (BvlSem.doBuildConst parts source.refs).2 }
    { target with refs := (BvlSem.doBuildConst parts target.refs).2 } at relatedBuild
  simp only [sourceBuild, targetBuild] at valueEq relatedBuild
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, sourceBuild] at run
  rcases run with ⟨rfl, rfl⟩
  simp [compileListSource, compileSingSource, compileOp, smartAppend] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have envEq := adjustMap_eq_of_ok relocate extended env source.refs envOk agree
  refine ⟨{ target with refs := targetRefs }, extended, 0, ?_, relatedBuild, envEq, agree⟩
  simp [BviSem.evaluate, BviSem.fixClock, BviProps.incClock, BviSem.doApp, BviSem.doAppFallback,
    BviSem.doAppAux, BvlSem.doApp, BvlSem.applyBlock, BviSem.toBvl, BviSem.fromBvl,
    targetBuild, mapSimulationResult, valueEq]

/-- Constant build satisfies pass simulation given operand simulation. Any
nonempty successful operand list is a source type error. -/
theorem simulation_build {C F : Type} (parts : List ClosLang.ConstPart) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.build parts)) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.blockOp (.build parts)) arguments env source middle error argsIH argsRun
    | val values =>
      have length := BvlSem.evaluate_length arguments env source middle values argsRun
      cases arguments with
      | nil => exact simulation_build_empty parts env source
      | cons first rest =>
        intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
        have nonempty : values ≠ [] := by intro eq; simp [eq] at length
        have reversed : values.reverse ≠ [] := by simpa using nonempty
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
        cases h : values.reverse with
        | nil => exact (reversed h).elim
        | cons firstValue restValues =>
          simp [BvlSem.doApp, BvlSem.applyBlock, h] at run
          exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
