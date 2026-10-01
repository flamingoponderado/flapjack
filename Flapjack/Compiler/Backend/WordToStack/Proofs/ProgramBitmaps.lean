import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompilePrefix
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompLength

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- The source single-program prefix result, with its actual output equation.
The only carrier translation is the positive HOL word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_prog_isPREFIX" (words_as_type_indexed_bitvec)]
theorem compileProgIsPrefix {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width)) (arguments registers : Nat)
    (bs : AppList (BitVec width) × Nat) (body : HolProg width) (frame : Nat)
    (output : AppList (BitVec width) × Nat)
    (h : compileProgNative conf perf program arguments registers bs = (body, frame, output)) :
    (appListAppend bs.1).IsPrefix (appListAppend output.1) := by
  let variables := max ((maxVarHOL program / 2 + 1) - registers) (arguments - registers)
  let f := if variables = 0 then 0 else variables + 1
  let result := compNative conf perf program bs (registers, f, variables)
  have equation : result.2 = output := by
    simpa only [compileProgNative, variables, f, result] using
      congrArg (fun value => value.2.2) h
  have hp := compImpIsPrefix conf perf program bs (registers, f, variables)
    result.1 result.2 rfl
  simpa only [equation] using hp

/-- The source single-program length bound and bitmap-gap equality.
No frame convention or compilation-success premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_prog_LENGTH" (words_as_type_indexed_bitvec)]
theorem compileProgLength {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width)) (arguments registers : Nat)
    (bm : AppList (BitVec width)) (index : Nat) (body : HolProg width) (frame : Nat)
    (output : AppList (BitVec width)) (nextIndex : Nat)
    (h : compileProgNative conf perf program arguments registers (bm, index) =
      (body, frame, output, nextIndex) ∧ (appListAppend bm).length ≤ index) :
    (appListAppend output).length ≤ nextIndex ∧
      index - (appListAppend bm).length = nextIndex - (appListAppend output).length := by
  obtain ⟨compiledEquation, bound⟩ := h
  let variables := max ((maxVarHOL program / 2 + 1) - registers) (arguments - registers)
  let f := if variables = 0 then 0 else variables + 1
  let result := compNative conf perf program (bm, index) (registers, f, variables)
  have equation : result.2 = (output, nextIndex) := by
    simpa only [compileProgNative, variables, f, result] using
      congrArg (fun value => value.2.2) compiledEquation
  have accounting := compImpLength conf perf program (bm, index)
    (registers, f, variables) result.1 result.2 ⟨rfl, bound⟩
  simpa only [equation] using accounting

/-- Projection helper following the actual left-to-right row traversal.
This proof packaging has no separate HOL original. -/
private theorem compileRowsPrefix {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) :
    (appListAppend bs.1).IsPrefix
      (appListAppend (compileWordToStackNative conf perf registers rows bs).2.2.1) := by
  induction rows generalizing bs with
  | nil => exact List.prefix_refl _
  | cons row rows ih =>
    rcases row with ⟨identifier, arguments, program⟩
    rcases hp : compileProgNative conf perf program arguments registers bs with
      ⟨body, frame, next⟩
    have before := compileProgIsPrefix conf perf program arguments registers bs body frame next hp
    have after := ih next
    simpa only [compileWordToStackNative, hp] using before.trans after

/-- Full source list compiler prefix theorem, retaining arbitrary identifiers
and the actual compiler output equation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_isPREFIX" (words_as_type_indexed_bitvec)]
theorem compileWordToStackIsPrefix {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (bodies : List (β × HolProg width))
    (frames : List Nat) (output : AppList (BitVec width) × Nat)
    (h : compileWordToStackNative conf perf registers rows bs = (bodies, frames, output)) :
    (appListAppend bs.1).IsPrefix (appListAppend output.1) := by
  have hpref := compileRowsPrefix conf perf registers rows bs
  simpa only [h] using hpref

/-- Projection packaging for bitmap accounting along the actual row traversal.
There is no separate HOL original for this internal induction helper. -/
private theorem compileRowsLength {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (bound : (appListAppend bs.1).length ≤ bs.2) :
    let output := (compileWordToStackNative conf perf registers rows bs).2.2
    (appListAppend output.1).length ≤ output.2 ∧
      bs.2 - (appListAppend bs.1).length = output.2 - (appListAppend output.1).length := by
  induction rows generalizing bs with
  | nil => exact ⟨bound, rfl⟩
  | cons row rows ih =>
    rcases row with ⟨identifier, arguments, program⟩
    rcases bs with ⟨bm, index⟩
    rcases hp : compileProgNative conf perf program arguments registers (bm, index) with
      ⟨body, frame, nextBm, nextIndex⟩
    obtain ⟨nextBound, gap⟩ := compileProgLength conf perf program arguments registers
      bm index body frame nextBm nextIndex ⟨hp, bound⟩
    obtain ⟨finalBound, finalGap⟩ := ih (nextBm, nextIndex) nextBound
    simpa only [compileWordToStackNative, hp] using ⟨finalBound, gap.trans finalGap⟩

/-- Complete source list compiler accounting statement. Its only numerical
premise is the original bound on the initial bitmap length. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_IMP_LENGTH" (words_as_type_indexed_bitvec)]
theorem compileWordToStackImpLength {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bm : AppList (BitVec width)) (index : Nat) (bodies : List (β × HolProg width))
    (frames : List Nat) (output : AppList (BitVec width)) (nextIndex : Nat)
    (h : compileWordToStackNative conf perf registers rows (bm, index) =
      (bodies, frames, output, nextIndex) ∧ (appListAppend bm).length ≤ index) :
    (appListAppend output).length ≤ nextIndex ∧
      index - (appListAppend bm).length = nextIndex - (appListAppend output).length := by
  have accounting := compileRowsLength conf perf registers rows (bm, index) h.2
  simpa only [h.1] using accounting

end Flapjack.Compiler.Backend.WordToStack.Native
