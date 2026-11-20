import Flapjack.HolRef.StateRelGcInhabitantsAudit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshRefProof

open Lean Meta Flapjack

private theorem good {β : Type} [Nonempty β] : ∃ (_p : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

private theorem used {β : Type} [Nonempty β] : ∃ (_p : β), _p = _p :=
  ⟨Classical.choice inferInstance, rfl⟩

private theorem wrongName {β : Type} [Nonempty β] : ∃ (_other : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

private theorem extraInstance {β γ : Type} [Nonempty β] [Nonempty γ] : ∃ (_p : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

run_meta do
  for (name, expected) in #[(``good, true), (``used, false), (``wrongName, false),
      (``extraInstance, false),
      (``Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.newRef, true)] do
    let info ← getConstInfo name
    let problems ← unusedExistentialInhabitantProblems info.type #[(`β, `_p)]
    unless problems.isEmpty == expected do
      throwError m!"fresh-reference inhabitance audit failed for {name}: {problems}"
