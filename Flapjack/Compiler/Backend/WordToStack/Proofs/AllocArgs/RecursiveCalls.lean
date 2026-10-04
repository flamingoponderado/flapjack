import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Flat
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnAllocArgs

namespace Flapjack.WordToStackProofs.AllocArgs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific dispatch calculation inside the original Call proof.
No standalone HOL theorem names this intermediate predicate calculation. -/
private theorem callDestAllocArg {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    allocArg (callDestNative (width := width) dest args frame).1 := by
  cases dest with
  | some d => trivial
  | none =>
      simp only [callDestNative]
      split <;> simp [loadAllocArg, allocArg]

/-- Flapjack-specific argument-frame calculation from the original Call case;
the accepted full stack-movement implication discharges its continuation. -/
private theorem stackArgsAllocArg {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (n : Nat) (frame : Nat × Nat × Nat) :
    allocArg (stackArgsNative (width := width) dest n frame) := by
  simp only [stackArgsNative]
  exact Flapjack.WordToStackProofs.stackMoveAllocArg _ _ _ _ _ (by trivial)

/-- Full MustTerminate case. The hypothesis is exactly the compiler induction
claim for its body, with arbitrary bitmap and frame inputs and the same guard. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgMustTerminate {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false)
    (ih : ∀ bs frame, perf = false → allocArg (compNative conf perf body bs frame).1) :
    allocArg (compNative conf perf (.mustTerminate body) bs frame).1 := by
  simpa only [compNative] using ih bs frame plain

/-- Full Loop case, retaining both source cutsets and only the body induction
hypothesis. No bitmap or frame wellformedness restriction is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgLoop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (liveIn liveOut : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (plain : perf = false)
    (ih : ∀ bs frame, perf = false → allocArg (compNative conf perf body bs frame).1) :
    allocArg (compNative conf perf (.loop liveIn body liveOut) bs frame).1 := by
  simpa only [compNative, allocArg] using ih bs frame plain

/-- Full Seq case. The second induction hypothesis is instantiated with the
actual first compiler call's returned bitmap, rather than an assumed output. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgSeq {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (first second : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (plain : perf = false)
    (ih1 : ∀ bs frame, perf = false → allocArg (compNative conf perf first bs frame).1)
    (ih2 : ∀ bs frame, perf = false → allocArg (compNative conf perf second bs frame).1) :
    allocArg (compNative conf perf (.seq first second) bs frame).1 := by
  simp only [compNative, allocArg]
  exact ⟨ih1 bs frame plain, ih2 (compNative conf perf first bs frame).2 frame plain⟩

/-- Full If case, including register operands and both valid/invalid immediate
branches for an arbitrary original assembler configuration. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgIf {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (cmp : Cmp) (reg : Nat)
    (ri : WordRegImm (BitVec width)) (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (plain : perf = false)
    (ih1 : ∀ bs frame, perf = false → allocArg (compNative conf perf first bs frame).1)
    (ih2 : ∀ bs frame, perf = false → allocArg (compNative conf perf second bs frame).1) :
    allocArg (compNative conf perf (.ite cmp reg ri first second) bs frame).1 := by
  have h1 := ih1 bs frame plain
  have h2 := ih2 (compNative conf perf first bs frame).2 frame plain
  cases ri with
  | reg n => simp [compNative, loadAllocArg, allocArg, h1, h2]
  | imm i =>
      simp only [compNative]
      split <;> simp [loadAllocArg, allocArg, h1, h2]

/-- Full tail Call case. The arbitrary optional handler remains quantified and
is ignored by the original compiler when the return record is absent. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgCallTail {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (plain : perf = false) :
    allocArg (compNative conf perf (.call none dest args handler) bs frame).1 := by
  subst perf
  simp only [compNative, allocArg, callDestAllocArg, true_and, seqStackFreeNative]
  split <;> trivial

/-- Full returning Call without a handler. Its sole extra premise is the
original subprogram induction hypothesis for the return body. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgCallReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (values : List Nat)
    (live : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (plain : perf = false)
    (ih : ∀ bs frame, perf = false → allocArg (compNative conf perf retCode bs frame).1) :
    allocArg (compNative conf perf (.call (some (values,live,retCode,l1,l2)) dest args none)
      bs frame).1 := by
  subst perf
  have retSafe := ih (wLiveNative live bs frame).2 frame rfl
  simp [compNative, allocArg, callDestAllocArg, liveAllocArg,
    stackArgsAllocArg, Flapjack.WordToStackProofs.allocArgCopyRet, retSafe]

/-- Full returning Call with a handler. Both genuine subprogram induction
hypotheses are instantiated at the actual successive compiler bitmap outputs;
handler value and both label pairs remain arbitrary. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackAllocArgCallHandler {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (values : List Nat)
    (live : WordLangCutsetsHOL) (retCode handleCode : WordLangProgHOL (BitVec width))
    (l1 l2 handleValue h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (plain : perf = false)
    (ih1 : ∀ bs frame, perf = false → allocArg (compNative conf perf retCode bs frame).1)
    (ih2 : ∀ bs frame, perf = false → allocArg (compNative conf perf handleCode bs frame).1) :
    allocArg (compNative conf perf
      (.call (some (values,live,retCode,l1,l2)) dest args
        (some (handleValue,handleCode,h1,h2))) bs frame).1 := by
  subst perf
  have retSafe := ih1 (wLiveNative live bs frame).2 frame rfl
  have handlerSafe := ih2 (compNative conf false retCode (wLiveNative live bs frame).2 frame).2
    frame rfl
  simp [compNative, allocArg, callDestAllocArg, liveAllocArg,
    stackArgsAllocArg, stackHandlerArgsNative, pushHandlerNative, popHandlerNative,
    Flapjack.WordToStackProofs.allocArgCopyRet, retSafe, handlerSafe]

end Flapjack.WordToStackProofs.AllocArgs
