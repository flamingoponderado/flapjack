import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameFlat
import Mathlib.Tactic.Tauto

namespace Flapjack.WordToStackProofs.AsmNameCompiler
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.WordToStackProofs.AsmNameFlat
open Flapjack.WordToStackProofs.AsmNameInstructions
open Flapjack.WordToStackProofs.AsmNameShare
open Flapjack.WordToStackProofs.AsmNameHelpers

/-- Flapjack-only conjunction interface for the seven source premises. HOL has
no separately named declaration for this proof-organization interface. -/
private def nameGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (p : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat) : Prop :=
  perf = false ∧ postAllocConventionsHOL frame.1 p = true ∧ fullInstOkLessExact conf p = true ∧
    (conf.twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) p = true) ∧
    (noShareInstSubprogsHOL p = true ∨ conf.isa ≠ .ag32) ∧
    frame.1 + 1 < conf.regCount - conf.avoidRegs.length ∧ 4 < frame.1

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem mustTerminateGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (p : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.mustTerminate p) frame) : nameGuards conf perf p frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at h ⊢
  tauto

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem loopGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (liveIn liveOut : WordLangNumSetHOL) (p : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.loop liveIn p liveOut) frame) : nameGuards conf perf p frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at h ⊢
  tauto

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem seqGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (p q : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.seq p q) frame) : nameGuards conf perf p frame ∧ nameGuards conf perf q frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at h ⊢
  tauto

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem ifGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width)) (p q : WordLangProgHOL (BitVec width)) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.ite cmp r ri p q) frame) : nameGuards conf perf p frame ∧ nameGuards conf perf q frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at h ⊢
  tauto

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem returnGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (values : List Nat) (live : WordLangCutsetsHOL) (p : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.call (some (values,live,p,l1,l2)) dest args none) frame) : nameGuards conf perf p frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true, Bool.true_and] at h ⊢
  tauto

/- Internal source-clause calculation; no separately named HOL theorem. -/
private theorem handlerGuards {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (perf : Bool) (values : List Nat) (live : WordLangCutsetsHOL) (p q : WordLangProgHOL (BitVec width)) (l1 l2 handleValue h1 h2 : Nat) (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat)
    (h : nameGuards conf perf (.call (some (values,live,p,l1,l2)) dest args (some (handleValue,q,h1,h2))) frame) : nameGuards conf perf p frame ∧ nameGuards conf perf q frame := by
  simp only [nameGuards, postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, fullInstOkLessExact, fullInstOkLessWith, everyInst, noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true, Bool.true_and] at h ⊢
  tauto

/- Internal Call naming calculations; no separately named HOL originals. -/
private theorem preparedDestNames {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmName conf (callDestNative dest args frame).1 ∧
      (match (callDestNative (width := width) dest args frame).2 with
       | .inr r => regName r conf | _ => True) := by
  have h := callDestStackAsmName conf dest args frame
    (callDestNative dest args frame).1 (callDestNative dest args frame).2 rfl
  refine ⟨h.1, ?_⟩
  cases result : (callDestNative (width := width) dest args frame).2 with
  | inl _ => trivial
  | inr r =>
      have bound := (Flapjack.WordToStackProofs.RegisterBoundRecursive.callDestBound (width := width) dest args frame).2
      simp only [result] at bound
      simp only [regName]
      omega

private theorem stackArgsName {width : Nat} [NeZero width] {α β : Type}
    (conf : AsmConfigExact width) (dest : Sum α β) (n : Nat) (frame : Nat × Nat × Nat) :
    stackAsmName conf (stackArgsNative dest n frame) := by
  simp only [stackArgsNative, stackMoveStackAsmName, stackAsmName]

private theorem handlerArgsName {width : Nat} [NeZero width] {α β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (dest : Sum α β) (n : Nat) (frame : Nat × Nat × Nat) :
    stackAsmName conf (stackHandlerArgsNative perf dest n frame) := by
  exact stackArgsName conf dest n _

private theorem pushHandlerName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (l1 l2 : Nat) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmName conf (pushHandlerNative false l1 l2 frame) := by
  simp [pushHandlerNative, stackAsmName, instName, regName]
  omega

private theorem popHandlerName {width : Nat} [NeZero width] {β γ : Type}
    (conf : AsmConfigExact width) (perf : Bool) (frame : Nat × β × γ) (p : HolProg width) :
    stackAsmName conf (popHandlerNative perf frame p) ↔ stackAsmName conf p := by
  simp [popHandlerNative, stackAsmName]

private theorem freeName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (n : Nat) (p : HolProg width) :
    stackAsmName conf (seqStackFreeNative n p) ↔ stackAsmName conf p := by
  by_cases h : n = 0 <;> simp [seqStackFreeNative, stackAsmName, h]

/-- Entire original all-program naming theorem, with all seven source guards.
Recursion uses only proper subprograms and actual threaded bitmap states; no
target naming/result/simulation premise is assumed. Full assembler conventions
and compiler simulation remain separate results. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackStackAsmName {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) (conventions : postAllocConventionsHOL frame.1 program = true)
    (valid : fullInstOkLessExact conf program = true)
    (twoReg : conf.twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) program = true)
    (noShare : noShareInstSubprogsHOL program = true ∨ conf.isa ≠ .ag32)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) (minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf program bs frame).1 := by
  subst perf
  have guards : nameGuards conf false program frame := ⟨rfl, conventions, valid, twoReg, noShare, room, minimum⟩
  cases program with
  | skip  => exact wordToStackStackAsmNameSkip conf false  bs frame rfl conventions valid twoReg noShare room minimum
  | move _ _ => exact wordToStackStackAsmNameMove conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | inst _ => exact wordToStackStackAsmNameInst conf false _ bs frame rfl conventions valid twoReg noShare room minimum
  | assign _ _ => exact wordToStackStackAsmNameAssign conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | get _ _ => exact wordToStackStackAsmNameGet conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | set _ _ => exact wordToStackStackAsmNameSet conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | store _ _ => exact wordToStackStackAsmNameStore conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | alloc _ _ => exact wordToStackStackAsmNameAlloc conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | storeConsts _ _ _ _ _ => exact wordToStackStackAsmNameStoreConsts conf false _ _ _ _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | raise _ => exact wordToStackStackAsmNameRaise conf false _ bs frame rfl conventions valid twoReg noShare room minimum
  | «return» _ _ => exact wordToStackStackAsmNameReturn conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | «break» _ => exact wordToStackStackAsmNameBreak conf false _ bs frame rfl conventions valid twoReg noShare room minimum
  | «continue» _ => exact wordToStackStackAsmNameContinue conf false _ bs frame rfl conventions valid twoReg noShare room minimum
  | tick  => exact wordToStackStackAsmNameTick conf false  bs frame rfl conventions valid twoReg noShare room minimum
  | opCurrHeap _ _ _ => exact wordToStackStackAsmNameOpCurrHeap conf false _ _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | locValue _ _ => exact wordToStackStackAsmNameLocValue conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | install _ _ _ _ _ => exact wordToStackStackAsmNameInstall conf false _ _ _ _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | codeBufferWrite _ _ => exact wordToStackStackAsmNameCodeBufferWrite conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | dataBufferWrite _ _ => exact wordToStackStackAsmNameDataBufferWrite conf false _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | ffi _ _ _ _ _ _ => exact wordToStackStackAsmNameFfi conf false _ _ _ _ _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | shareInst _ _ _ => exact wordToStackStackAsmNameShareInst conf false _ _ _ bs frame rfl conventions valid twoReg noShare room minimum
  | mustTerminate p =>
      have h := mustTerminateGuards conf false p frame guards
      simpa only [compNative] using wordToStackStackAsmName conf false p bs frame h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  | loop liveIn p liveOut =>
      have h := loopGuards conf false liveIn liveOut p frame guards
      simpa only [compNative, stackAsmName] using wordToStackStackAsmName conf false p bs frame h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
  | seq p q =>
      have h := seqGuards conf false p q frame guards
      have hp := wordToStackStackAsmName conf false p bs frame h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2
      have hq := wordToStackStackAsmName conf false q (compNative conf false p bs frame).2 frame h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
      simpa only [compNative, stackAsmName] using And.intro hp hq
  | ite cmp r ri p q =>
      have h := ifGuards conf false cmp r ri p q frame guards
      have hp := wordToStackStackAsmName conf false p bs frame h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2
      have hq := wordToStackStackAsmName conf false q (compNative conf false p bs frame).2 frame h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
      cases ri
      all_goals simp only [compNative, wReg1, wReg2]
      all_goals try split_ifs
      all_goals simp only [loadName, stackAsmName, instName, regName]
      all_goals repeat' apply And.intro
      all_goals first | exact hp | exact hq | omega
  | call returns dest args handler =>
      have hd := preparedDestNames conf dest args frame room
      cases returns with
      | none =>
          simp only [compNative, freeName, stackAsmName, and_true]
          refine ⟨hd.1, ?_⟩
          cases result : (callDestNative (width := width) dest args frame).2 <;> simp_all only
      | some record =>
          match hRet : record with
          | (values,live,p,l1,l2) =>
              have hl := wLiveStackAsmName conf live bs frame _ _ room rfl
              cases handler with
              | none =>
                  have h := returnGuards conf false values live p l1 l2 dest args frame guards
                  have hp := wordToStackStackAsmName conf false p (wLiveNative live bs frame).2 frame h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
                  simp only [compNative, Bool.false_eq_true, if_false, stackAsmName]
                  repeat' apply And.intro
                  all_goals first
                    | exact hd.1
                    | exact hd.2
                    | exact hl
                    | exact stackArgsName conf _ _ _
                    | trivial
                    | (simpa only [copyRetStackAsmName, stackAsmName, true_and] using hp)
              | some record =>
                  match hHandle : record with
                  | (handleValue,q,h1,h2) =>
                      have h := handlerGuards conf false values live p q l1 l2 handleValue h1 h2 dest args frame guards
                      have hp := wordToStackStackAsmName conf false p (wLiveNative live bs frame).2 frame h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2.1 h.1.2.2.2.2.2.2
                      have hq := wordToStackStackAsmName conf false q (compNative conf false p (wLiveNative live bs frame).2 frame).2 frame h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
                      simp only [compNative, Bool.false_eq_true, if_false, stackAsmName]
                      repeat' apply And.intro
                      all_goals first
                        | exact hd.1
                        | exact hd.2
                        | exact hl
                        | exact handlerArgsName conf _ _ _ _
                        | exact pushHandlerName conf _ _ _ room
                        | (change frame.1 < conf.regCount - conf.avoidRegs.length; omega)
                        | exact hq
                        | trivial
                        | (simpa only [copyRetStackAsmName, stackAsmName, true_and, popHandlerName] using hp)
termination_by sizeOf program
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Flapjack.WordToStackProofs.AsmNameCompiler
