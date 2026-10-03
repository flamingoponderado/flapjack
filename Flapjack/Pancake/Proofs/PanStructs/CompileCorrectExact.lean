import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAtomic
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDec
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectAssign
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectPrimitive
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectStore
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectStoreWords
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemLoad
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectShMemStore
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectSeqIf
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectWhile
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectReturnRaise
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectTickAnnot
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectCall
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectDecCall
import Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExtCall
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
namespace Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExact
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Whole original PanStructs program correctness over the faithful clocked evaluator.
All ten original hypotheses and seven conclusions are retained. The fixed full
property is established by all 21 original evaluate_ind minors; Call, DecCall,
While, Seq, If and Dec receive exactly their source-guarded recursive IHs.
There is no public induction hypothesis, supplied target run or post-map premise.
Canonical finite-support maps and positive type-indexed words are the only
carrier translations. The whole statement and complete original evaluate_ind
are kernel-captured in pan_structs_program_call_probe.out. Production routing
of the reviewed compiler definitions remains separate open inventory work. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileCorrectExact {width : Nat} {σ : Type} [NeZero width]
    (program : ProgHOL width) (source : PanSemStateFiniteExact width σ) :
  ∀ (post : PanSemStateFiniteExact width σ) (context : ContextExact)
    (res : Option (PanSemResultExact width)),
    ( PanSemStateFiniteExact.evaluateHOLFiniteState source program = (res, post) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      res ≠ some .error) →
    PanSemStateFiniteExact.evaluateHOLFiniteState (convertStateExact context source)
      (compileProgExact context program) = (convertResHOL res, convertStateExact context post) ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.locals ∧
    feveryHOL (fun entry => valueFldsOkHOLExact post.structs entry.2) post.globals ∧
    shapeMap context.globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
    (isContResHOL res = true →
      shapeMap context.locals = post.locals.map2 (fun entry => shapeOfHOLExact entry.2)) ∧
    (∀ value ∈ resVsHOL res, valueFldsOkHOLExact post.structs value = true) ∧
    (∀ value ∈ resVsHOL res, isWfShapeValueHOLExact post.structs value = true) := by
  have hall : ∀ (p : ProgHOL width) (s : PanSemStateFiniteExact width σ),
      CompileCorrectCall.CallProperty s p := by
    apply evaluateIndHOL (fun pair => CompileCorrectCall.CallProperty pair.2 pair.1)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      intro post ctx res h
      exact CompileCorrectAtomic.compileCorrectSkip s post ctx res h
    · intro v sh e p s ih
      intro post ctx res h
      exact CompileCorrectDec.compileCorrectDec s post ctx v sh e p res ih h
    · intro vk v e s
      intro post ctx res h
      exact CompileCorrectAssign.compileCorrectAssign s post ctx vk v e res h
    · intro v op es s
      intro post ctx res h
      exact CompileCorrectPrimitive.compileCorrectPrimitive s post ctx v op es res h
    · intro dst src s
      intro post ctx res h
      exact CompileCorrectStore.compileCorrectStore s post ctx dst src res h
    · intro dst src s
      intro post ctx res h
      exact CompileCorrectStoreWords.compileCorrectStore32 s post ctx dst src res h
    · intro dst src s
      intro post ctx res h
      exact CompileCorrectStoreWords.compileCorrectStoreByte s post ctx dst src res h
    · intro op vk v ad s
      intro post ctx res h
      exact CompileCorrectShMemLoad.compileCorrectShMemLoad s post ctx op vk v ad res h
    · intro op ad e s
      intro post ctx res h
      exact CompileCorrectShMemStore.compileCorrectShMemStore s post ctx op ad e res h
    · intro c1 c2 s ih
      intro post ctx res h
      exact CompileCorrectSeqIf.compileCorrectSeq s post ctx c1 c2 res ih.2 ih.1 h
    · intro e c1 c2 s ih
      intro post ctx res h
      exact CompileCorrectSeqIf.compileCorrectIf s post ctx e c1 c2 res ih h
    · intro s
      intro post ctx res h
      exact CompileCorrectAtomic.compileCorrectBreak s post ctx res h
    · intro s
      intro post ctx res h
      exact CompileCorrectAtomic.compileCorrectContinue s post ctx res h
    · intro e c s ih
      intro post ctx res h
      exact CompileCorrectWhile.compileCorrectWhile s post ctx e c res ih.1 ih.2.1 ih.2.2 h
    · intro e s
      intro post ctx res h
      exact CompileCorrectReturnRaise.compileCorrectReturn s post ctx e res h
    · intro eid e s
      intro post ctx res h
      exact CompileCorrectReturnRaise.compileCorrectRaise s post ctx eid e res h
    · intro s
      intro post ctx res h
      exact CompileCorrectTickAnnot.compileCorrectTick s post ctx res h
    · intro v0 v1 s
      intro post ctx res h
      exact CompileCorrectTickAnnot.compileCorrectAnnot s post ctx v0 v1 res h
    · intro ct fnm es s ih
      intro post ctx res h
      exact CompileCorrectCall.compileCorrectCall s post ctx ct fnm es res ih.1 ih.2 h
    · intro rt sh fnm es p s ih
      intro post ctx res h
      exact CompileCorrectDecCall.compileCorrectDecCall s post ctx rt sh fnm es p res ih.1 ih.2 h
    · intro idx ptr1 len1 ptr2 len2 s
      intro post ctx res h
      exact CompileCorrectExtCall.compileCorrectExtCall s post ctx idx ptr1 len1 ptr2 len2 res h
  exact hall program source
end Flapjack.Pancake.Proofs.PanStructs.CompileCorrectExact
