module

public import Flapjack.Compiler.Backend.StackRawCall.Proofs.InstructionSimulation

/-! Shared tactic macros for the four `compCorrect*` assembly proofs of
`cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml`. The four files differ
only in their leaf predicate (`BasicLeaf`, `ControlLeaf`, `MemoryLeaf`, `StackLeaf`), so
the identical proof text lives here instead of being repeated four times. Each macro takes
the file-local lemma names it calls as parameters. Flapjack proof infrastructure: this file
ports no HOL declaration. -/

@[expose] public section

namespace Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect

/-- Shared proof script for the four `evaluate_code_eq` lemmas, one per leaf predicate.
`codeUpdate` is the file-local `evaluate_codeUpdate` for that leaf predicate. -/
macro "stackRawCall_codeEq" codeUpdate:ident program:ident leaf:ident source:ident : tactic =>
  `(tactic| (
  have transport := $codeUpdate $program $leaf $source ($source).code
  have unchanged : { $source with code := ($source).code } = $source := by
    simp
  rw [unchanged] at transport
  have projected := congrArg (fun outcome => outcome.2.code) transport
  exact projected))

/-- Shared proof script for the four `evaluate_stateRel` lemmas, one per leaf predicate.
`codeEq` and `codeUpdate` are the file-local lemmas for that leaf predicate. -/
macro "stackRawCall_stateRel" codeEq:ident codeUpdate:ident program:ident leaf:ident
    source:ident resultState:ident execution:ident relation:ident : tactic => `(tactic| (
  obtain ⟨code, domain, targetEq, frames, entries⟩ := $relation
  rw [targetEq]
  have codeEq' := $codeEq $program $leaf $source
  have hexec := $execution
  rw [hexec] at codeEq'
  change ($resultState).code = ($source).code at codeEq'
  refine ⟨{ $resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq'] using domain
    · simpa only [codeEq'] using frames
    · simpa only [codeEq'] using entries
  · rw [$codeUpdate $program $leaf, hexec]))

/-- Shared proof script for the four `compCorrect*` assembly theorems, one per leaf
predicate. `stateRelLemma` is the file-local `evaluate_stateRel` for that predicate. -/
macro "stackRawCall_compCorrect" stateRelLemma:ident program:ident leaf:ident info:ident
    source:ident target:ident resultState:ident result:ident hypothesis:ident : tactic =>
  `(tactic| (
  obtain ⟨execution, _, relation⟩ := $hypothesis
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    $stateRelLemma $program $leaf $info $source $target $resultState $result execution relation
  have clockSelf : { $target with clock := ($target).clock + 0 } = $target := by
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    simp
  have compSelf : comp $info $program = $program := by
    have hleaf := $leaf
    cases hleaf
    all_goals rfl
  have compTopSelf : compTop $info $program = $program := by
    have hleaf := $leaf
    cases hleaf
    all_goals rfl
  constructor
  all_goals refine ⟨0, targetState, targetState.stackSpace, postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution))

end Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect
