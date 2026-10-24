import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive
import Flapjack.Compiler.Backend.StackProps.RemoveNames

namespace Flapjack.WordToStackProofs.AsmRemoveHelpers
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific implication between the two full native predicates.
No separate HOL declaration names this stronger uniform transport; it discharges
only register-name obligations that the complete register bound already checks. -/
private theorem removeOfBound {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (program : HolProg width) (bound : Nat)
    (bounded : regBound program bound)
    (room : bound ≤ conf.regCount - conf.avoidRegs.length) : stackAsmRemove conf program := by
  set_option tactic.fun_induction.unfolding false in
  fun_induction regBound program bound with
  | case15 returns target handler bound ih =>
      rcases returns with _ | ⟨body, register, l1, l2⟩ <;>
        rcases handler with _ | ⟨hbody, h1, h2⟩ <;>
        grind only [regBound, stackAsmRemove]
  | case11 cmp register right first second bound ihFirst ihSecond =>
      cases right <;> grind only [regBound, stackAsmRemove, regName]
  | _ => grind only [regBound, stackAsmRemove, regName]


/-- Entire original destination preparation implication, including both output
components and the original upper bound on the indirect destination register. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "call_dest_stack_asm_remove" (words_as_type_indexed_bitvec)]
theorem callDestStackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (dest : Option Nat) (args : List Nat)
    (frame : Nat × Nat × Nat) (setup : HolProg width) (target : Sum Nat Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (compiled : callDestNative dest args frame = (setup,target)) :
    stackAsmRemove conf setup ∧
      (match target with | .inr r => r ≤ frame.1 + 1 | .inl _ => True) := by
  have bounds := Flapjack.WordToStackProofs.RegisterBoundRecursive.callDestBound
    (width := width) dest args frame
  rw [compiled] at bounds
  refine ⟨removeOfBound conf setup (frame.1 + 2) bounds.1 (by omega), ?_⟩
  cases target <;> simp_all <;> omega

/-- Entire original live-bitmap output implication, retaining arbitrary source
cutsets, bitmap/frame inputs and the full original compiler output equality. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "wLive_stack_asm_remove" (words_as_type_indexed_bitvec)]
theorem wLiveStackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (setup : HolProg width) (residual : AppList (BitVec width) × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (compiled : wLiveNative live bs frame = (setup,residual)) :
    stackAsmRemove conf setup := by
  have bounds := Flapjack.WordToStackProofs.RegisterBoundFlat.liveBound live bs frame
  rw [compiled] at bounds
  exact removeOfBound conf setup (frame.1 + 2) bounds (by omega)

/-- Full original stack movement equivalence, preserving arbitrary continuation
and all unbounded natural slot offsets, with exactly the temporary-name premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "stack_move_stack_asm_remove" (words_as_type_indexed_bitvec)]
theorem stackMoveStackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (n start offset i : Nat) (p : HolProg width)
    (named : regName i conf) :
    stackAsmRemove conf (stackMoveNative n start offset i p) ↔ stackAsmRemove conf p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simpa only [stackMoveNative, stackAsmRemove, named, true_and, and_true] using ih (start + 1)

/-- Full original descending return-copy auxiliary bound from the sole
register-name premise; frame offsets and copy counts remain arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_aux_stack_asm_remove" (words_as_type_indexed_bitvec)]
theorem copyRetAuxStackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width]
    (conf : AsmConfigExact configWidth) (k f n : Nat) (named : regName k conf) :
    stackAsmRemove conf (copyRetAuxNative k f n : HolProg width) := by
  induction n with
  | zero => trivial
  | succ n ih => simpa only [copyRetAuxNative, listSeq, stackAsmRemove, named, true_and, and_true] using ih

/-- Entire original false-performance return wrapper equivalence. The original
value-list and unused frame-tail carriers are independent; the continuation is
arbitrary and no continuation convention is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "copy_ret_stack_asm_remove" (words_as_type_indexed_bitvec)]
theorem copyRetStackAsmRemove {configWidth : Nat} {width : Nat} [NeZero configWidth] [NeZero width] {β γ : Type}
    (conf : AsmConfigExact configWidth) (isHandle : Bool) (frame : Nat × Nat × γ)
    (values : List β) (kont : HolProg width) (named : regName frame.1 conf) :
    stackAsmRemove conf (copyRetNative false isHandle frame values kont) ↔
      stackAsmRemove conf kont := by
  simp only [copyRetNative]
  split
  · rfl
  · rename_i nonzero
    simp [nonzero, stackAsmRemove, copyRetAuxStackAsmRemove conf _ _ _ named, seqStackFreeNative]

end Flapjack.WordToStackProofs.AsmRemoveHelpers
