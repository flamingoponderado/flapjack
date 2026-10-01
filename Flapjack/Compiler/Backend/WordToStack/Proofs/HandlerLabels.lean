import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramCodeLabels
import Flapjack.Compiler.Backend.StackProps.LabelSafety

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original incremental handler-label safety theorem. The original
EVERY handler guard and complete actual output equation retain arbitrary
configuration, register count, input programs, frame list and bitmap state.
The target safety predicate is proved, with no additional bounds or premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_good_handler_labels_incr" (words_as_type_indexed_bitvec)]
theorem wordToStackGoodHandlerLabelsIncr {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (registers : Nat)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (bodies : List (Nat × HolProg width))
    (frames : List Nat) (bs' : AppList (BitVec width) × Nat)
    (good : rows.all (fun row => goodHandlersHOL row.1 row.2.2) = true)
    (compiled : compileWordToStackNative conf false registers rows bs = (bodies,frames,bs')) :
    stackGoodHandlerLabels bodies := by
  have bound := compileWordToStackCodeLabels conf false registers rows bs bodies (frames,bs')
    good rfl compiled
  unfold stackGoodHandlerLabels
  intro label member
  have present := bound member.1
  rcases present with h | h | h | h
  · subst label
    exact False.elim (member.2 rfl)
  · subst label
    exact False.elim (member.2 rfl)
  · rcases h with ⟨name, _, equation⟩
    subst label
    exact False.elim (member.2 rfl)
  · exact Or.inl h

end Flapjack.Compiler.Backend.WordToStack.Native
