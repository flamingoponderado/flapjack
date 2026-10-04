import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmRemoveCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackConventions

namespace Flapjack.WordToStackProofs.AsmConventions
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

/- Proof organization only: HOL has no separately named four-guard bundle.
Every field is precisely one conjunct of the original per-program EVERY. -/
private def sourceGuards {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (k : Nat) (p : WordLangProgHOL (BitVec width)) : Prop :=
  fullInstOkLessExact conf p = true ∧
  (conf.twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) p = true) ∧
  (noShareInstSubprogsHOL p = true ∨ conf.isa ≠ .ag32) ∧
  postAllocConventionsHOL k p = true

/- Literal StackAlloc-prefix calculation from the source list proof.
This conjunction has no separate named HOL original. -/
private theorem compileProgSafe {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (count k : Nat) (bs : AppList (BitVec width) × Nat)
    (guards : sourceGuards conf k program) (minimum : 4 < k)
    (room : k + 1 < conf.regCount - conf.avoidRegs.length) :
    stackAsmName conf (compileProgNative conf false program count k bs).1 ∧
    stackAsmRemove conf (compileProgNative conf false program count k bs).1 ∧
    allocArg (compileProgNative conf false program count k bs).1 ∧
    regBound (compileProgNative conf false program count k bs).1 (k + 2) ∧
    callArgs (compileProgNative conf false program count k bs).1 1 2 3 4 0 := by
  simp only [compileProgNative, stackAsmName, stackAsmRemove, allocArg, regBound, callArgs, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact AsmNameCompiler.wordToStackStackAsmName conf false program bs _ rfl
      guards.2.2.2 guards.1 guards.2.1 guards.2.2.1 room minimum
  · exact AsmRemoveCompiler.wordToStackStackAsmRemove conf false program bs _ room rfl
  · exact AllocArgs.wordToStackAllocArg conf false program bs _ rfl
  · exact RegisterBoundCompiler.wordToStackRegBound conf false program bs _
      guards.2.2.2 (by omega) rfl
  · exact CallArgsCompiler.wordToStackCallArgs conf false program bs _ guards.2.2.2 rfl

/- Internal list induction over the actual residual bitmap after each row.
No target convention is assumed and no separate HOL theorem names this helper. -/
private theorem compileListSafe {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat)
    (guards : ∀ row ∈ programs, sourceGuards conf k row.2.2)
    (minimum : 4 < k) (room : k + 1 < conf.regCount - conf.avoidRegs.length) :
    ∀ row ∈ (compileWordToStackNative conf false k programs bs).1,
      stackAsmName conf row.2 ∧ stackAsmRemove conf row.2 ∧ allocArg row.2 ∧
      regBound row.2 (k + 2) ∧ callArgs row.2 1 2 3 4 0 := by
  induction programs generalizing bs with
  | nil => simp [compileWordToStackNative]
  | cons row programs ih =>
      rcases row with ⟨identifier,count,program⟩
      have headSafe := compileProgSafe conf program count k bs
        (guards (identifier,count,program) (List.mem_cons_self)) minimum room
      have tailGuards : ∀ row ∈ programs, sourceGuards conf k row.2.2 :=
        fun row membership => guards row (List.mem_cons_of_mem _ membership)
      have tailSafe := ih (compileProgNative conf false program count k bs).2.2 tailGuards
      simp only [compileWordToStackNative]
      intro row membership
      rcases List.mem_cons.mp membership with equal | membership
      · subst row
        exact headSafe
      · exact tailSafe row membership

/-- Entire original compile_word_to_stack_convs, with arbitrary identifier type
and actual compiler-result tuple equality. Source EVERY is represented by its
equivalent membership quantifier. The result contains all five original
predicates; only source validity/conventions and the two frame guards are used.
The residual pair retains both original frame sizes and bitmaps. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileWordToStackConvs {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (outputs : List (β × HolProg width))
    (rest : List Nat × (AppList (BitVec width) × Nat))
    (compiled : compileWordToStackNative conf false k programs bs = (outputs,rest))
    (guards : ∀ row ∈ programs,
      fullInstOkLessExact conf row.2.2 = true ∧
      (conf.twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) row.2.2 = true) ∧
      (noShareInstSubprogsHOL row.2.2 = true ∨ conf.isa ≠ .ag32) ∧
      postAllocConventionsHOL k row.2.2 = true)
    (minimum : 4 < k) (room : k + 1 < conf.regCount - conf.avoidRegs.length) :
    ∀ row ∈ outputs,
      stackAsmName conf row.2 ∧ stackAsmRemove conf row.2 ∧ allocArg row.2 ∧
      regBound row.2 (k + 2) ∧ callArgs row.2 1 2 3 4 0 := by
  have result : (compileWordToStackNative conf false k programs bs).1 = outputs :=
    congrArg Prod.fst compiled
  rw [← result]
  exact compileListSafe conf k programs bs guards minimum room

/-- Entire original word_to_stack_stack_asm_convs for the actual top-level
compiler's output, including both prepended stubs. The register count is the
original natural subtraction, and its strict minimum derives the naming/removal
room guard internally. No extra frame or target-safety premise is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackStackAsmConvs {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (guards : ∀ row ∈ programs,
      fullInstOkLessExact conf row.2.2 = true ∧
      (conf.twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) row.2.2 = true) ∧
      (noShareInstSubprogsHOL row.2.2 = true ∨ conf.isa ≠ .ag32) ∧
      postAllocConventionsHOL (conf.regCount - (conf.avoidRegs.length + 5)) row.2.2 = true)
    (minimum : 4 < conf.regCount - (conf.avoidRegs.length + 5)) :
    ∀ row ∈ (compileNative conf false programs).2.2.2,
      stackAsmName conf row.2 ∧ stackAsmRemove conf row.2 := by
  let k := conf.regCount - (5 + conf.avoidRegs.length)
  have minimum' : 4 < k := by simpa only [k, Nat.add_comm] using minimum
  have room : k + 1 < conf.regCount - conf.avoidRegs.length := by
    dsimp [k] at *
    omega
  have input : ∀ row ∈ programs, sourceGuards conf k row.2.2 := by
    simpa only [sourceGuards, k, Nat.add_comm] using guards
  have bodySafe := compileListSafe conf k programs (.list [4],1) input minimum' room
  have raiseSafe : stackAsmName conf (raiseStubNative (width := width) false k) ∧
      stackAsmRemove conf (raiseStubNative (width := width) false k) := by
    simp [raiseStubNative, stackAsmName, stackAsmRemove, regName]
    omega
  have storeSafe : stackAsmName conf (storeConstsStubNative (width := width) k) ∧
      stackAsmRemove conf (storeConstsStubNative (width := width) k) := by
    simp [storeConstsStubNative, stackAsmName, stackAsmRemove, regName]
    omega
  simp only [compileNative, Bool.false_eq_true, if_false]
  intro row membership
  rcases List.mem_cons.mp membership with equal | membership
  · subst row
    exact raiseSafe
  · rcases List.mem_cons.mp membership with equal | membership
    · subst row
      exact storeSafe
    · exact ⟨(bodySafe row membership).1, (bodySafe row membership).2.1⟩

end Flapjack.WordToStackProofs.AsmConventions
