import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundCompiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.Compiler
import Flapjack.Compiler.Backend.WordToStack.Proofs.CallArgsCompiler

namespace Flapjack.WordToStackProofs.StackConventions
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

/-- Internal single-row calculation in the original whole-program proof.
There is no standalone HOL theorem for this local conjunction; the actual
frame calculation and unconditional StackAlloc prefix remain intact. -/
private theorem compileProgConventions {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (count k : Nat) (bs : AppList (BitVec width) × Nat)
    (conventions : postAllocConventionsHOL k program = true) (room : 4 ≤ k) :
    allocArg (compileProgNative conf false program count k bs).1 ∧
    regBound (compileProgNative conf false program count k bs).1 (k + 2) ∧
    callArgs (compileProgNative conf false program count k bs).1 1 2 3 4 0 := by
  simp only [compileProgNative, allocArg, regBound, callArgs, true_and]
  exact ⟨Flapjack.WordToStackProofs.AllocArgs.wordToStackAllocArg conf false program bs _ rfl,
    Flapjack.WordToStackProofs.RegisterBoundCompiler.wordToStackRegBound conf false program bs _ conventions room rfl,
    Flapjack.WordToStackProofs.CallArgsCompiler.wordToStackCallArgs conf false program bs _ conventions rfl⟩

/-- Internal original list-induction calculation. Identifier types remain
arbitrary and the actual residual bitmap from each row feeds the next row.
There is no separate HOL declaration for this three-predicate conjunction. -/
private theorem compileListConventions {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat)
    (conventions : (programs.all fun row => postAllocConventionsHOL k row.2.2) = true)
    (room : 4 ≤ k) :
    ∀ row ∈ (compileWordToStackNative conf false k programs bs).1,
      allocArg row.2 ∧ regBound row.2 (k + 2) ∧ callArgs row.2 1 2 3 4 0 := by
  induction programs generalizing bs with
  | nil => simp [compileWordToStackNative]
  | cons row programs ih =>
      rcases row with ⟨identifier,count,program⟩
      have guards : postAllocConventionsHOL k program = true ∧
          (programs.all fun row => postAllocConventionsHOL k row.2.2) = true := by
        apply Bool.and_eq_true_iff.mp
        simpa only [List.all_cons] using conventions
      simp only [compileWordToStackNative]
      intro row membership
      rcases List.mem_cons.mp membership with equal | membership
      · subst row
        exact compileProgConventions conf program count k bs guards.1 room
      · exact ih (compileProgNative conf false program count k bs).2.2 guards.2 row membership

/-- Entire original top-level compiled-program conventions theorem, including
both prepended stubs. Source EVERY is rendered through Bool-valued List.all;
conclusion EVERY predicates use their equivalent membership quantifiers on
MAP SND. Every compiler output field is arbitrary under the original tuple
equality. No target convention, target evaluation or successful pass is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_convs" (words_as_type_indexed_bitvec)]
theorem wordToStackStackConvs {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bytes : List (BitVec width)) (config : Config) (frames : List Nat)
    (outputs : List (Nat × HolProg width)) (k : Nat)
    (compiled : compileNative conf false programs = (bytes,config,frames,outputs))
    (conventions : (programs.all fun row => postAllocConventionsHOL k row.2.2) = true)
    (registers : k = conf.regCount - (5 + conf.avoidRegs.length)) (room : 4 ≤ k) :
    (∀ p ∈ outputs.map Prod.snd, allocArg p) ∧
    (∀ p ∈ outputs.map Prod.snd, regBound p (k + 2)) ∧
    (∀ p ∈ outputs.map Prod.snd, callArgs p 1 2 3 4 0) := by
  have raiseSafe : allocArg (raiseStubNative (width := width) false k) ∧
      regBound (raiseStubNative (width := width) false k) (k + 2) ∧
      callArgs (raiseStubNative (width := width) false k) 1 2 3 4 0 := by
    simp [raiseStubNative, allocArg, regBound, callArgs]
  have storeSafe : allocArg (storeConstsStubNative (width := width) k) ∧
      regBound (storeConstsStubNative (width := width) k) (k + 2) ∧
      callArgs (storeConstsStubNative (width := width) k) 1 2 3 4 0 := by
    simp [storeConstsStubNative, allocArg, regBound, callArgs]
    omega
  have result := congrArg (fun r => r.2.2.2) compiled
  simp only [compileNative, ← registers, Bool.false_eq_true, if_false] at result
  have bodySafe := compileListConventions conf k programs (.list [4],1) conventions room
  have allSafe : ∀ p ∈ outputs.map Prod.snd,
      allocArg p ∧ regBound p (k + 2) ∧ callArgs p 1 2 3 4 0 := by
    rw [← result]
    simp only [List.map_cons, List.mem_cons]
    intro p membership
    rcases membership with equal | equal | membership
    · subst p
      exact raiseSafe
    · subst p
      exact storeSafe
    · rcases List.mem_map.mp membership with ⟨row,inList,rfl⟩
      exact bodySafe row inList
  exact ⟨fun p membership => (allSafe p membership).1,
    fun p membership => (allSafe p membership).2.1,
    fun p membership => (allSafe p membership).2.2⟩

end Flapjack.WordToStackProofs.StackConventions
