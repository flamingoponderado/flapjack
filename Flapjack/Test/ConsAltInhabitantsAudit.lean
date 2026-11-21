import Flapjack.HolRef.StateRelGcInhabitantsAudit
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsAltWritten
import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MakePtrBits

open Lean Meta Flapjack

private theorem good {β : Type} [Nonempty β] : ∃ (_unused : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

private theorem used {β : Type} [Nonempty β] : ∃ (_unused : β), _unused = _unused :=
  ⟨Classical.choice inferInstance, rfl⟩

private theorem wrongName {β : Type} [Nonempty β] : ∃ (_other : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

private theorem extraInstance {β γ : Type} [Nonempty β] [Nonempty γ] : ∃ (_unused : β), True :=
  ⟨Classical.choice inferInstance, trivial⟩

run_meta do
  for (name, expected) in #[(``good, true), (``used, false), (``wrongName, false),
      (``extraInstance, false),
      (``Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.memoryRel_consAlt, true),
      (``Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.makePtrBits_correct, true)] do
    let info ← getConstInfo name
    let problems ← unusedExistentialInhabitantProblems info.type #[(`β, `_unused)]
    unless problems.isEmpty == expected do
      throwError m!"constructor-memory inhabitance audit failed for {name}: {problems}"
