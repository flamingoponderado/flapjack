import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Arithmetic
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Constant
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Memory
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation.Skip

namespace Flapjack.WordToStackProofs.InstSimulation
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Every integer or memory instruction satisfying the register, frame and
argument conventions is simulated by its compiled StackSem program. The
instruction carrier is restricted on riscv-mi and intentionally differs from
HOL's carrier. The conclusion preserves the state relation and stack resources. -/
theorem evaluateWInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (instruction : HolInst width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (executed : WordSemStateFiniteExact.inst instruction.toWordLangInst source = some sourcePost)
    (physical : everyVarInstHOL isPhyVar instruction.toWordLangInst)
    (bound : maxVarInstHOL instruction.toWordLangInst < 2*frame+2*k)
    (convention : instArgConventionExact instruction)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wInstNative instruction (k,f,frame),target) = (none,post) ∧
      stateRel ac k f frame sourcePost post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace := by
  cases instruction with
  | skip =>
    exact Skip.evaluateWInstSkip ac k f frame source sourcePost target lens
      executed physical bound convention related
  | const destination value =>
    exact Constant.evaluateWInstConst ac destination k f frame value
      source sourcePost target lens executed physical bound convention related
  | arith operation =>
    exact Arithmetic.evaluateWInstArith ac operation k f frame source sourcePost target lens
      executed physical bound convention related
  | mem operation register address =>
    cases address with
    | addr base offset =>
      exact Memory.evaluateWInstMemory operation ac register base k f frame offset
        source sourcePost target lens executed physical bound convention related
end Flapjack.WordToStackProofs.InstSimulation
