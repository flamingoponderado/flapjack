import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticPrimitives
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticMove
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRegisterWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticStateWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticAllocCase
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticStoreConsts
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticRaise
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticReturn
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticHeap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInstallCase
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticBufferWrites
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticFFI
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticShareInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticMustTerminate
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticIf
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticLoop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallTail
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallCase

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack induction motive for the original all-program simulation; no
independent HOL declaration. -/
private def programSimulation {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) : Prop :=
  ∀ (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)),
    Flapjack.WordAlloc.wordStateEqRel source target ∧
    ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
    everyVarHOL (fun key => decide (key < next)) prog = true ∧
    ssaMapOK next ssa ∧ ltOK tables → ssaSimulation prog source target ssa next tables

namespace SemanticCorrectWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticCorrectWitnesses

/-- All native program constructors establish the original evaluator simulation;
no induction hypothesis or target evaluation is a public premise. Inherits
reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrect {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) prog = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation prog source target ssa next tables := by
  have all : ∀ (p : WordLangProgHOL (BitVec width)), programSimulation (C := C) (F := F) p := by
    intro p
    apply WordLangProgHOL.rec
      (motive_1 := programSimulation (C := C) (F := F))
      (motive_2 := fun ret => match ret with | none => True | some r => programSimulation (C := C) (F := F) r.2.2.1)
      (motive_3 := fun exc => match exc with | none => True | some r => programSimulation (C := C) (F := F) r.2.1)
      (motive_4 := fun r => programSimulation (C := C) (F := F) r.2.2.1)
      (motive_5 := fun r => programSimulation (C := C) (F := F) r.2.1)
      (motive_6 := fun r => programSimulation (C := C) (F := F) r.2.1)
      (motive_7 := fun r => programSimulation (C := C) (F := F) r.1) (t := p)
    case skip =>
      intro st ct map counter lt h
      apply ssaCcTransCorrectSkip; assumption
    case move =>
      intro priority moves st ct map counter lt h
      apply ssaCcTransCorrectMove; assumption
    case inst =>
      intro instruction st ct map counter lt h
      apply ssaCcTransCorrectInst; assumption
    case assign =>
      intro name exp st ct map counter lt h
      apply ssaCcTransCorrectAssign; assumption
    case get =>
      intro destination store st ct map counter lt h
      apply ssaCcTransCorrectGet; assumption
    case set =>
      intro store exp st ct map counter lt h
      apply ssaCcTransCorrectSet; assumption
    case store =>
      intro exp name st ct map counter lt h
      apply ssaCcTransCorrectStore; assumption
    case alloc =>
      intro destination cutsets st ct map counter lt h
      apply ssaCcTransCorrectAlloc; assumption
    case storeConsts =>
      intro a b c d ws st ct map counter lt h
      apply ssaCcTransCorrectStoreConsts; assumption
    case raise =>
      intro name st ct map counter lt h
      apply ssaCcTransCorrectRaise; assumption
    case «return» =>
      intro label values st ct map counter lt h
      apply ssaCcTransCorrectReturn; assumption
    case «break» =>
      intro label st ct map counter lt h
      apply ssaCcTransCorrectBreak; assumption
    case «continue» =>
      intro label st ct map counter lt h
      apply ssaCcTransCorrectContinue; assumption
    case tick =>
      intro st ct map counter lt h
      apply ssaCcTransCorrectTick; assumption
    case opCurrHeap =>
      intro operator destination sourceName st ct map counter lt h
      apply ssaCcTransCorrectOpCurrHeap; assumption
    case locValue =>
      intro destination sourceName st ct map counter lt h
      apply ssaCcTransCorrectLocValue; assumption
    case install =>
      intro ptr len dptr dlen cutsets st ct map counter lt h
      apply ssaCcTransCorrectInstall; assumption
    case codeBufferWrite =>
      intro address value st ct map counter lt h
      apply ssaCcTransCorrectCodeBufferWrite; assumption
    case dataBufferWrite =>
      intro address value st ct map counter lt h
      apply ssaCcTransCorrectDataBufferWrite; assumption
    case ffi =>
      intro function configuration configurationLength array arrayLength cutsets st ct map counter lt h
      apply ssaCcTransCorrectFFI; assumption
    case shareInst =>
      intro operator destination exp st ct map counter lt h
      apply ssaCcTransCorrectShareInst; assumption
    case mustTerminate =>
      intro body bodyIH st ct map counter lt h
      apply ssaCcTransCorrectMustTerminate <;> assumption
    case seq =>
      intro first second firstIH secondIH st ct map counter lt h
      apply ssaCcTransCorrectSeq <;> assumption
    case ite =>
      intro cmp condition right yes no yesIH noIH st ct map counter lt h
      apply ssaCcTransCorrectIf <;> assumption
    case loop =>
      intro names body exits bodyIH st ct map counter lt h
      apply ssaCcTransCorrectLoop <;> assumption
    case call =>
      intro returns dest args handler retIH excIH st ct map counter lt h
      cases returns with
      | none => apply ssaCcTransCorrectCallTail; assumption
      | some ret =>
        rcases ret with ⟨returns, cutsets, body, l1, l2⟩
        rcases cutsets with ⟨firstNames, secondNames⟩
        cases handler with
        | none => apply ssaCcTransCorrectCallReturningNone <;> assumption
        | some handler =>
          rcases handler with ⟨exceptionVar, handlerBody, handlerL1, handlerL2⟩
          apply ssaCcTransCorrectCallReturningSome <;> assumption
    case none => exact True.intro
    case some => intro value ih; exact ih
    case none => exact True.intro
    case some => intro value ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro fst snd ih; exact ih
    case mk => intro body rest ih; exact ih
  exact all prog source target ssa next tables premises

end Flapjack.Compiler.Backend.WordAlloc
