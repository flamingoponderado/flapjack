import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstall
import Flapjack.Pancake.WordConvs.NoInstall
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
/-- Flapjack-specific structural infrastructure for the original Inst case.
HOL proves this fact inside comp_no_install rather than as a separate theorem.
All instruction constructors and arbitrary positive widths are retained. -/
theorem wInstNoInstall {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    noInstall (wInstNative instruction frame) = true := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      noInstall (wRegWrite1Native (fun reg => .inst (g reg)) r frame) = true :=
    wRegWrite1NoInstall _ r frame (fun _ => rfl)
  have write21 (g : Nat → Nat → HolInst width) (r1 r2 : Nat) :
      noInstall (wRegWrite2Native
        (fun reg2 => wRegWrite1Native (fun reg1 => .inst (g reg1 reg2)) r1 frame)
        r2 frame) = true :=
    wRegWrite2NoInstall _ r2 frame (fun reg2 => write1 (fun reg1 => g reg1 reg2) r1)
  cases instruction with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals simp [wInstNative, wStackLoadNoInstall, write1, noInstall]
  | mem op d addr =>
    cases addr
    cases op <;> simp [wInstNative, wStackLoadNoInstall,
      write1, noInstall]
  | fp f =>
    cases f
    all_goals
      by_cases hw : width = 64
      all_goals simp [wInstNative, hw, wStackLoadNoInstall,
        write1, write21, noInstall]
  | skip => rfl
  | const n c => simp [wInstNative, write1]

/-- Flapjack-specific dispatch calculation used inside the source Call case;
HOL has no separately named theorem for this intermediate calculation. -/
private theorem callDestNoInstall {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    noInstall (callDestNative (width := width) dest args frame).1 = true := by
  cases dest with
  | some d => rfl
  | none =>
    simp only [callDestNative]
    split <;> simp [wStackLoadNoInstall, noInstall]

/-- Flapjack-specific native lowering calculation; no standalone HOL theorem. -/
private theorem shareNoInstall {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (addr : HolAddr width) (frame : Nat × Nat × Nat) :
    noInstall (wShareInstNative op v addr frame) = true := by
  cases addr
  cases op <;> simp only [wShareInstNative, wStackLoadNoInstall]
  all_goals first
    | exact wRegWrite1NoInstall _ _ _ (fun _ => rfl)
    | rfl

/-- Full original arbitrary-program no-install preservation theorem. The
original performance equality is retained alongside the source predicate and
actual full compiler output equation. All recursive assumptions are internal. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_install" (words_as_type_indexed_bitvec)]
theorem compNoInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noInstallSubprogsHOL program = true)
    (compiled : compNative conf perf program bs frame = (output,residual))
    (plain : perf = false) : noInstall output = true := by
  subst perf
  have result := congrArg Prod.fst compiled
  cases program with
  | inst instruction =>
    simp only [compNative] at result
    rw [← result]
    exact wInstNoInstall _ frame
  | move priority moves =>
    simp only [compNative] at result
    rw [← result]
    exact wMoveAuxNoInstall _ frame
  | get destination name | locValue destination name =>
    simp only [compNative] at result
    rw [← result]
    exact wRegWrite1NoInstall _ _ _ (fun _ => rfl)
  | opCurrHeap operator destination source =>
    simp only [compNative] at result
    rw [← result, wStackLoadNoInstall]
    exact wRegWrite1NoInstall _ _ _ (fun _ => rfl)
  | set name exp =>
    cases name <;> cases exp <;>
      simp only [compNative] at result
    all_goals rw [← result]; first | rfl | rw [wStackLoadNoInstall]; rfl
  | install codeBuffer codeLength dataBuffer dataLength live =>
    simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at guard
  | shareInst operator name address =>
    simp only [compNative] at result
    cases h : expToAddrHOL address <;> simp only [h] at result
    all_goals rw [← result]
    · rfl
    · exact shareNoInstall _ _ _ frame
  | alloc destination live =>
    simp only [compNative] at result
    rw [← result]
    simp only [noInstall, wLiveNoInstall, Bool.true_and]
  | mustTerminate body =>
    have bodyGuard : noInstallSubprogsHOL body = true := by
      simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
    exact compNoInstall conf false body bs frame output residual bodyGuard
      (by simpa only [compNative] using compiled) rfl
  | loop liveIn body liveOut =>
    have bodyGuard : noInstallSubprogsHOL body = true := by
      simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
    have bodySafe := compNoInstall conf false body bs frame
      (compNative conf false body bs frame).1 (compNative conf false body bs frame).2 bodyGuard rfl rfl
    simp only [compNative] at result
    rw [← result]
    exact bodySafe
  | seq first second | ite cmp reg ri first second =>
    have guards : noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
      simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using guard
    have firstSafe := compNoInstall conf false first bs frame
      (compNative conf false first bs frame).1 (compNative conf false first bs frame).2 guards.1 rfl rfl
    have secondSafe := compNoInstall conf false second (compNative conf false first bs frame).2 frame
      (compNative conf false second (compNative conf false first bs frame).2 frame).1
      (compNative conf false second (compNative conf false first bs frame).2 frame).2 guards.2 rfl rfl
    simp only [compNative] at result
    rw [← result]
    first
      | simp only [noInstall, firstSafe, secondSafe, Bool.true_and]
      | cases ri with
        | reg n => simp [wStackLoadNoInstall, noInstall, firstSafe, secondSafe]
        | imm i =>
          simp only []
          split <;> simp [wStackLoadNoInstall, noInstall, firstSafe, secondSafe]
  | call returns destination args handler =>
    cases returns with
    | none =>
      simp only [compNative] at result
      rw [← result]
      simp only [noInstall, callDestNoInstall, Bool.true_and, seqStackFreeNative]
      split <;> simp [noInstall]
    | some record =>
      match hRetRecord : record with
      | (values,live,retCode,label1,label2) =>
        cases handler with
        | none =>
          have retGuard : noInstallSubprogsHOL retCode = true := by
            simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using guard
          have retSafe := compNoInstall conf false retCode (wLiveNative live bs frame).2 frame
            (compNative conf false retCode (wLiveNative live bs frame).2 frame).1
            (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 retGuard rfl rfl
          simp only [compNative] at result
          rw [← result]
          simp [noInstall, callDestNoInstall, wLiveNoInstall,
            stackArgsNative, stackMoveNoInstall, copyRetNoInstall, retSafe]
        | some record =>
          match hHandlerRecord : record with
          | (handleValue,handleCode,handleLabel1,handleLabel2) =>
            have guards : noInstallSubprogsHOL retCode = true ∧ noInstallSubprogsHOL handleCode = true := by
              simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using guard
            have retSafe := compNoInstall conf false retCode (wLiveNative live bs frame).2 frame
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).1
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 guards.1 rfl rfl
            have handlerSafe := compNoInstall conf false handleCode
              (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame
              (compNative conf false handleCode (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame).1
              (compNative conf false handleCode (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame).2 guards.2 rfl rfl
            simp only [compNative] at result
            rw [← result]
            simp [noInstall, callDestNoInstall, wLiveNoInstall,
              pushHandlerNative, stackHandlerArgsNative, stackArgsNative,
              stackMoveNoInstall, copyRetNoInstall, popHandlerNative, retSafe, handlerSafe]
  | skip =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | assign _ _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | store _ _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | raise _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | «break» _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | «continue» _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | tick =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | «return» _ _ =>
    simp only [compNative] at result
    rw [← result]
    simp only [wStackLoadNoInstall, seqStackFreeNative]
    split <;> simp [noInstall]
  | storeConsts _ _ _ _ _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
  | codeBufferWrite _ _ =>
    simp only [compNative] at result
    rw [← result]
    rw [wStackLoadNoInstall]
    rfl
  | dataBufferWrite _ _ =>
    simp only [compNative] at result
    rw [← result]
    rw [wStackLoadNoInstall]
    rfl
  | ffi _ _ _ _ _ _ =>
    simp only [compNative] at result
    rw [← result]
    rfl
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega
end Flapjack.Compiler.Backend.WordToStack.Native
