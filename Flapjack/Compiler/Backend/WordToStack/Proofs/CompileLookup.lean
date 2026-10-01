import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps
import Flapjack.Pancake.Semantics.PanProps

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Full first-match compiled lookup with existential intermediate bitmap
states. `DecidableEq` implements propositional equality only; no `BEq`, unique
identifier, frame convention or output lookup assumption is imposed. The
existing equality-based lookup is the literal empty/cons first-match traversal.
Only HOL's positive word dimension uses a different carrier representation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_IMP_ALOOKUP" (words_as_type_indexed_bitvec)]
theorem compileWordToStackImpALookup {width : Nat} [NeZero width]
    {β : Type} [DecidableEq β]
    (conf : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bm : AppList (BitVec width)) (index : Nat)
    (bodies : List (β × HolProg width)) (frames : List Nat)
    (output : AppList (BitVec width)) (nextIndex : Nat)
    (identifier : β) (arguments : Nat) (program : WordLangProgHOL (BitVec width))
    (x : List (BitVec width))
    (compiled : compileWordToStackNative conf perf registers rows (bm,index) =
      (bodies,frames,output,nextIndex))
    (source : panPropsALookupEq identifier rows = some (arguments,program))
    (bound : (appListAppend bm).length ≤ index)
    (gapBound : index - (appListAppend bm).length ≤ x.length)
    (finalPrefix : (appListAppend output).IsPrefix
      (x.drop (index - (appListAppend bm).length))) :
    ∃ (start : AppList (BitVec width)) (startIndex : Nat)
      (finish : AppList (BitVec width)) (finishIndex frame : Nat) (body : HolProg width),
      compileProgNative conf perf program arguments registers (start,startIndex) =
        (body,frame,finish,finishIndex) ∧
      (appListAppend start).length ≤ startIndex ∧
      startIndex - (appListAppend start).length ≤ x.length ∧
      (appListAppend finish).IsPrefix
        (x.drop (startIndex - (appListAppend start).length)) ∧
      panPropsALookupEq identifier bodies = some body := by
  induction rows generalizing bm index bodies frames output nextIndex with
  | nil => simp [panPropsALookupEq] at source
  | cons row rows ih =>
    rcases row with ⟨name,argc,prog⟩
    rcases hp : compileProgNative conf perf prog argc registers (bm,index) with
      ⟨body,frame,nextBm,nextI⟩
    rcases ht : compileWordToStackNative conf perf registers rows (nextBm,nextI) with
      ⟨tailBodies,tailFrames,finalBm,finalI⟩
    have equation : ((name,body)::tailBodies,frame::tailFrames,finalBm,finalI) =
        (bodies,frames,output,nextIndex) := by
      simpa only [compileWordToStackNative,hp,ht] using compiled
    cases equation
    by_cases heq : name = identifier
    · have selected : argc = arguments ∧ prog = program := by
        simpa [panPropsALookupEq,heq] using source
      rcases selected with ⟨rfl,rfl⟩
      have tailPrefix := compileWordToStackIsPrefix conf perf registers rows
        (nextBm,nextI) tailBodies tailFrames (output,nextIndex) ht
      refine ⟨bm,index,nextBm,nextI,frame,body,hp,bound,gapBound,
        tailPrefix.trans finalPrefix,?_⟩
      simp [panPropsALookupEq,heq]
    · have tailSource : panPropsALookupEq identifier rows = some (arguments,program) := by
        simpa [panPropsALookupEq,heq] using source
      obtain ⟨nextBound,gap⟩ := compileProgLength conf perf prog argc registers
        bm index body frame nextBm nextI ⟨hp,bound⟩
      have nextGapBound : nextI - (appListAppend nextBm).length ≤ x.length := by
        simpa only [← gap] using gapBound
      have nextPrefix : (appListAppend output).IsPrefix
          (x.drop (nextI - (appListAppend nextBm).length)) := by
        simpa only [← gap] using finalPrefix
      obtain ⟨start,startI,finish,finishI,f,result,hc,hb,hg,hpfx,hl⟩ :=
        ih nextBm nextI tailBodies tailFrames output nextIndex ht tailSource
          nextBound nextGapBound nextPrefix
      refine ⟨start,startI,finish,finishI,f,result,hc,hb,hg,hpfx,?_⟩
      simpa [panPropsALookupEq,heq] using hl

end Flapjack.Compiler.Backend.WordToStack.Native
