import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveHelpers
import Flapjack.Compiler.Backend.StackProps.ProgramNames

namespace Flapjack.WordToStackProofs.AsmNameHelpers
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Entire original destination helper implication, which has no count guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callDestStackAsmName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (frame : Nat × Nat × Nat) (setup : HolProg width) (target : Sum Nat Nat)
    (compiled : callDestNative dest args frame = (setup,target)) :
    stackAsmName conf setup ∧
      (match target with | .inr r => r ≤ frame.1 + 1 | .inl _ => True) := by
  have bounds := RegisterBoundRecursive.callDestBound (width := width) dest args frame
  rw [compiled] at bounds
  refine ⟨?_, ?_⟩
  · have safe : stackAsmName conf (callDestNative (width := width) dest args frame).1 := by
      cases dest
      all_goals simp only [callDestNative, wReg2]
      all_goals try split_ifs
      all_goals simp [wStackLoadNative, stackAsmName]
    simpa only [compiled] using safe
  · cases target <;> simp_all <;> omega

/-- Entire original live-bitmap naming implication; its reduced-count guard
is retained although other configuration fields remain arbitrary. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wLiveStackAsmName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (live : WordLangCutsetsHOL)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (setup : HolProg width) (residual : AppList (BitVec width) × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (compiled : wLiveNative live bs frame = (setup,residual)) :
    stackAsmName conf setup := by
  have safe : stackAsmName conf (wLiveNative live bs frame).1 := by
    simp only [wLiveNative]
    split <;> simp only [stackAsmName, instName, regName]
    all_goals first | trivial | (constructor <;> first | trivial | omega)
  simpa only [compiled] using safe

/-- Full movement equivalence at arbitrary offsets and continuation, with
no register-name premise in the original naming theorem. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackMoveStackAsmName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (n start offset i : Nat) (p : HolProg width) :
    stackAsmName conf (stackMoveNative n start offset i p) ↔ stackAsmName conf p := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simpa only [stackMoveNative, stackAsmName, and_true] using ih (start + 1)

/-- Entire auxiliary naming theorem, independent of all register/count guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem copyRetAuxStackAsmName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (k f n : Nat) :
    stackAsmName conf (copyRetAuxNative k f n : HolProg width) := by
  induction n with
  | zero => trivial
  | succ n ih => simpa only [copyRetAuxNative, listSeq, stackAsmName, true_and] using ih

/-- Entire return-wrapper naming equivalence, preserving arbitrary performance
and handler flags and independent original list/frame-tail types. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem copyRetStackAsmName {width : Nat} [NeZero width] {β γ : Type}
    (conf : AsmConfigExact width) (perf isHandle : Bool) (frame : Nat × Nat × γ)
    (values : List β) (kont : HolProg width) :
    stackAsmName conf (copyRetNative perf isHandle frame values kont) ↔
      stackAsmName conf kont := by
  simp only [copyRetNative]
  split
  · rfl
  · rename_i nonzero
    simp [nonzero, stackAsmName, copyRetAuxStackAsmName, seqStackFreeNative]

end Flapjack.WordToStackProofs.AsmNameHelpers
