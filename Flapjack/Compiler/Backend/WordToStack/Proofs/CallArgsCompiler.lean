import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnCallArgs
import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Pancake.WordConvs

namespace Flapjack.WordToStackProofs.CallArgsCompiler
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/- Internal calculations below follow the original compiler case proof.
They have no separately named HOL original; the stronger internal traversal
uses only the call-convention conjunct, while the tagged theorem keeps HOL's
entire original post-allocation premise. -/
private theorem loadCallArgs {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) :
    callArgs (wStackLoadNative loads p) 1 2 3 4 0 ↔ callArgs p 1 2 3 4 0 := by
  induction loads with
  | nil => rfl
  | cons x xs ih => cases x; simpa only [wStackLoadNative, callArgs, true_and] using ih

private theorem writeCallArgs {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ r, callArgs (g r) 1 2 3 4 0) :
    callArgs (wRegWrite1Native g r frame) 1 2 3 4 0 := by
  simp only [wRegWrite1Native]
  split <;> simp [callArgs, h]

private theorem write2CallArgs {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ r, callArgs (g r) 1 2 3 4 0) :
    callArgs (wRegWrite2Native g r frame) 1 2 3 4 0 := by
  simp only [wRegWrite2Native]
  split <;> simp [callArgs, h]

private theorem instCallArgs {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    callArgs (wInstNative instruction frame) 1 2 3 4 0 := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      callArgs (wRegWrite1Native (fun r => .inst (g r)) r frame) 1 2 3 4 0 :=
    writeCallArgs _ _ _ (fun _ => trivial)
  have write21 (g : Nat → Nat → HolInst width) (r1 r2 : Nat) :
      callArgs (wRegWrite2Native
        (fun r2 => wRegWrite1Native (fun r1 => .inst (g r1 r2)) r1 frame)
        r2 frame) 1 2 3 4 0 :=
    write2CallArgs _ _ _ (fun r2 => write1 (fun r1 => g r1 r2) r1)
  cases instruction with
  | arith a =>
      cases a <;> try (rename_i op d src ri; cases ri)
      all_goals simp [wInstNative, loadCallArgs, write1, callArgs]
  | mem op d addr =>
      cases addr
      cases op <;> simp [wInstNative, loadCallArgs, write1, callArgs]
  | skip => trivial
  | const _ _ => simp [wInstNative, write1]

private theorem moveCallArgs {width : Nat} [NeZero width]
    (xs : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    callArgs (wMoveAuxNative xs frame : HolProg width) 1 2 3 4 0 := by
  have single (xy : Sum Nat Nat × Sum Nat Nat) :
      callArgs (wMoveSingleNative (width := width) xy frame) 1 2 3 4 0 := by
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> trivial
  induction xs with
  | nil => trivial
  | cons xy xs ih =>
      cases xs with
      | nil => exact single xy
      | cons y ys => simpa [wMoveAuxNative, callArgs, single] using ih

private theorem liveCallArgs {width : Nat} [NeZero width]
    (live : WordLangCutsetsHOL) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) : callArgs (wLiveNative live bs frame).1 1 2 3 4 0 := by
  simp only [wLiveNative]
  split <;> trivial

private theorem destCallArgs {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    callArgs (callDestNative (width := width) dest args frame).1 1 2 3 4 0 := by
  cases dest with
  | some d => trivial
  | none => simp only [callDestNative]; split <;> simp [loadCallArgs, callArgs]

private theorem shareCallArgs {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (addr : HolAddr width) (frame : Nat × Nat × Nat) :
    callArgs (wShareInstNative op v addr frame) 1 2 3 4 0 := by
  cases addr
  cases op <;> simp only [wShareInstNative, loadCallArgs]
  all_goals first | exact writeCallArgs _ _ _ (fun _ => trivial) | trivial

private theorem stackArgsCallArgs {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (n : Nat) (frame : Nat × Nat × Nat) :
    callArgs (stackArgsNative (width := width) dest n frame) 1 2 3 4 0 := by
  simp only [stackArgsNative]
  exact Flapjack.WordToStackProofs.stackMoveCallArgs _ _ _ _ _ (by trivial)

private theorem compilerCallArgs {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (convention : callArgConventionHOL program = true) (plain : perf = false) :
    callArgs (compNative conf perf program bs frame).1 1 2 3 4 0 := by
  subst perf
  cases program with
  | mustTerminate body =>
      simpa only [compNative, callArgs] using compilerCallArgs conf false body bs frame convention rfl
  | loop liveIn body liveOut =>
      simpa only [compNative, callArgs] using compilerCallArgs conf false body bs frame convention rfl
  | seq first second | ite cmp r ri first second =>
      have guards : callArgConventionHOL first = true ∧ callArgConventionHOL second = true := by
        simpa [callArgConventionHOL, Bool.and_eq_true] using convention
      have h1 := compilerCallArgs conf false first bs frame guards.1 rfl
      have h2 := compilerCallArgs conf false second (compNative conf false first bs frame).2
        frame guards.2 rfl
      first
      | simpa only [compNative, callArgs] using And.intro h1 h2
      | cases ri with
        | reg n => simp [compNative, loadCallArgs, callArgs, h1, h2]
        | imm i => simp only [compNative]; split <;> simp [loadCallArgs, callArgs, h1, h2]
  | call returns dest args handler =>
      cases returns with
      | none =>
          simp only [compNative, callArgs, destCallArgs, true_and, seqStackFreeNative]
          split <;> trivial
      | some record =>
          match hRet : record with
          | (values,live,retCode,l1,l2) =>
              cases handler with
              | none =>
                  simp only [callArgConventionHOL, Bool.and_eq_true] at convention
                  have guard := convention.1.2
                  have hret := compilerCallArgs conf false retCode (wLiveNative live bs frame).2 frame guard rfl
                  simp [compNative, callArgs, destCallArgs, liveCallArgs, stackArgsCallArgs,
                    Flapjack.WordToStackProofs.copyRetCallArgs, hret]
              | some record =>
                  match hHandle : record with
                  | (handleValue,handleCode,h1,h2) =>
                      simp only [callArgConventionHOL, Bool.and_eq_true] at convention
                      have hret := compilerCallArgs conf false retCode (wLiveNative live bs frame).2
                        frame convention.1.2 rfl
                      have hhandler := compilerCallArgs conf false handleCode
                        (compNative conf false retCode (wLiveNative live bs frame).2 frame).2
                        frame convention.2.2 rfl
                      simp [compNative, callArgs, destCallArgs, liveCallArgs, stackArgsCallArgs,
                        pushHandlerNative, stackHandlerArgsNative, popHandlerNative,
                        Flapjack.WordToStackProofs.copyRetCallArgs, hret, hhandler]
  | inst i => simp only [compNative]; exact instCallArgs _ _
  | move priority xs => simp only [compNative, wMoveNative]; exact moveCallArgs _ _
  | get destination name | locValue destination name =>
      simp only [compNative]
      exact writeCallArgs _ _ _ (fun _ => trivial)
  | opCurrHeap op destination source =>
      simp only [compNative, loadCallArgs]
      exact writeCallArgs _ _ _ (fun _ => trivial)
  | set name exp =>
      cases name <;> cases exp <;> simp [compNative, loadCallArgs, callArgs]
  | alloc destination live => simp [compNative, callArgs, liveCallArgs]
  | shareInst op v exp =>
      simp only [compNative]
      cases h : expToAddrHOL exp <;> simp only []
      · trivial
      · exact shareCallArgs _ _ _ _
  | install r1 r2 r3 r4 live =>
      simp [callArgConventionHOL, Bool.and_eq_true] at convention
      rcases convention with ⟨rfl,rfl⟩
      simp [compNative, loadCallArgs, callArgs]
  | ffi name r1 r2 r3 r4 live =>
      simp [callArgConventionHOL, Bool.and_eq_true] at convention
      rcases convention with ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩
      simp [compNative, callArgs]
  | «return» v vs =>
      simp only [compNative, loadCallArgs, seqStackFreeNative]
      split <;> trivial
  | codeBufferWrite r1 r2 | dataBufferWrite r1 r2 => simp [compNative, loadCallArgs, callArgs]
  | _ => simp [compNative, callArgs]
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

/-- Full original arbitrary-program compiler call-convention theorem. The
entire post-allocation guard and false-performance premise are retained; every
recursive hypothesis is discharged internally on actual native compiler outputs. -/
theorem wordToStackCallArgs {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (conventions : postAllocConventionsHOL frame.1 program = true) (plain : perf = false) :
    callArgs (compNative conf perf program bs frame).1 1 2 3 4 0 := by
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
  exact compilerCallArgs conf perf program bs frame conventions.2.2 plain

end Flapjack.WordToStackProofs.CallArgsCompiler
