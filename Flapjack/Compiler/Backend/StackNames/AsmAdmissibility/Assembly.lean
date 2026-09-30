import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Inst
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.RegisterLeaves
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Recursive
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Defaults

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Full HOL assembler-admissibility theorem. Structural compiler induction
supplies each original child IH, discharging every constructor case internally. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (program : HolProg width) (config : AsmConfigExact width) :
    stackAsmName config program ∧ namesOkSptHOL names config.regCount config.avoidRegs ∧
      fixedNames names config → stackAsmOkExact config (progCompHOL names program) := by
  change stackNamesAsmGoal names config program
  induction program using progCompHOL.induct
  case case11 returns target handler ihReturn ihHandler =>
    apply stackNamesCompStackAsmOk_Call
    · intro body link l1 l2 hr
      rw [hr] at ihReturn
      exact ihReturn
    · intro body l1 l2 hh
      rw [hh] at ihHandler
      exact ihHandler
  case case17 program h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
    cases program <;> first
    | exact stackNamesCompStackAsmOk_OpCurrHeap names config _ _ _
    | exact stackNamesCompStackAsmOk_ShMemOp names config _ _ _
    | exact stackNamesCompStackAsmOk_Default names config _ (by trivial)
    | solve | grind
  all_goals first
  | exact stackNamesCompStackAsmOk_Inst names config _
  | exact stackNamesCompStackAsmOk_OpCurrHeap names config _ _ _
  | exact stackNamesCompStackAsmOk_CodeBufferWrite names config _ _
  | exact stackNamesCompStackAsmOk_Raise names config _
  | exact stackNamesCompStackAsmOk_Return names config _
  | exact stackNamesCompStackAsmOk_ShMemOp names config _ _ _
  | apply stackNamesCompStackAsmOk_Seq <;> assumption
  | apply stackNamesCompStackAsmOk_If <;> assumption
  | apply stackNamesCompStackAsmOk_Loop <;> assumption
  | exact stackNamesCompStackAsmOk_Default names config _ (by trivial)

/-- HOL EVERY is rendered as universal list membership, with the same input
list order and compiled entry bodies. This lifts the full constructor theorem. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesStackAsmOk {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (names : Flapjack.Spt Nat)
    (program : List (Nat × HolProg width)) :
    (∀ entry ∈ program, stackAsmName config entry.2) ∧
      namesOkSptHOL names config.regCount config.avoidRegs ∧ fixedNames names config →
    ∀ entry ∈ compileHOL names program, stackAsmOkExact config entry.2 := by
  intro ⟨hp, hn, hf⟩ entry hentry
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hentry
  exact stackNamesCompStackAsmOk names original.2 config ⟨hp original ho, hn, hf⟩

end Flapjack.Compiler.Backend.StackNames
