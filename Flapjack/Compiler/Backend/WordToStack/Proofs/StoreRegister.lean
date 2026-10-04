import Flapjack.Compiler.Backend.WordToStack.NativeStackStore
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterWrite
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.WordToStackProofs.StoreRegister
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

/-- Flapjack infrastructure: the actual native trailing Skip preserves the
whole evaluation pair for arbitrary programs/states and all results. -/
private theorem evaluateSeqSkip {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq program .skip,target) =
      StackSemEvaluate.evaluate (program,target) := by
  rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate]
  rcases run : StackSemEvaluate.evaluate (program,target) with ⟨result,post⟩
  cases result <;> simp [StackSemEvaluate.evaluate_skip]

/-- Full original unconditional write-continuation equation (4656–4670). No callback execution law or successful-result premise. The evaluator inherits
reals_as_rational_cuts; this law claims no independent real-analysis agreement. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateWRegWrite1Seq {width : Nat} [NeZero width] {C F : Type}
    (kont : Nat → HolProg width) (register k f frame : Nat)
    (target : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (wRegWrite1Native kont register (k,f,frame),target) =
      (let (loads,physical) := wReg1 register (k,f,frame)
       StackSemEvaluate.evaluate (.seq (kont physical) (wStackStoreNative loads .skip),target)) := by
  by_cases physical : register/2 < k
  · simp only [wRegWrite1Native,wReg1,physical,if_true,wStackStoreNative]
    exact (evaluateSeqSkip _ _).symm
  · simp only [wRegWrite1Native,wReg1,physical,if_false,wStackStoreNative]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate]
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate]
    rcases run : StackSemEvaluate.evaluate (kont k,target) with ⟨result,post⟩
    cases result
    · simp [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip,
        StackSemControl.fixClock]
    · rfl

/-- Full original store-through-Reg1 update law (4527–4548).
Retains arbitrary stack length/space naming equalities and original EVEN/range/
full relation premises, deriving the actual store run and entire updated relation.
The evaluator inherits reals_as_rational_cuts; no independent real-analysis
agreement is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateWStackStoreWReg1 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register physical k f frame : Nat)
    (loads : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (value : WordLocW width) (stackLength stackSpace : Nat)
    (compiled : wReg1 register (k,f,frame) = (loads,physical))
    (even : register%2=0) (bound : register < 2*frame+2*k)
    (related : stateRel ac k f frame source target lens 0)
    (lengthEq : target.stack.length=stackLength) (spaceEq : target.stackSpace=stackSpace) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackStoreNative loads .skip,
        StackSemStateOps.setVar physical value target) = (none,post) ∧
      stateRel ac k f frame (WordSemStateFiniteExact.setVar register value source) post lens 0 ∧
      post.stack.length=stackLength ∧ post.stackSpace=stackSpace := by
  have registerEq : 2*(register/2)=register := by omega
  by_cases inReg : register/2 < k
  · simp only [wReg1,inReg,if_true,Prod.mk.injEq] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    refine ⟨StackSemStateOps.setVar (register/2) value target,?_,?_,lengthEq,spaceEq⟩
    · exact StackSemEvaluate.evaluate_skip _
    · have updated := StateRelRegisterUpdate.stateRelSetVar (register/2) value related inReg
      simpa only [registerEq] using updated
  · simp only [wReg1,inReg,if_false,Prod.mk.injEq] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    have halfBound : register/2 < frame+k := by omega
    have shape : if frame=0 then f=0 else f=frame+1 :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have frameShape : f=frame+1 := by split at shape <;> omega
    have resource : target.stackSpace+f ≤ target.stack.length :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have slot : f-1-(register/2-k) = f+k-(register/2+1) := by omega
    have slotBound : target.stackSpace+(f-1-(register/2-k)) < target.stack.length := by omega
    have useStack : target.useStack = true := related.2.2.2.2.1
    let post := {StackSemStateOps.setVar k value target with
      stack := target.stack.set (target.stackSpace+(f-1-(register/2-k))) value}
    refine ⟨post,?_,?_,?_,spaceEq⟩
    · simp [wStackStoreNative,StackSemEvaluate.evaluate_seq,StackSemEvaluate.evaluate_stackStore,
        StackSemControl.fixClock,StackSemStateOps.setVar,StackSemStateOps.getVar,
        HolFiniteMapExact.updateEq,FUPDATE_HOL,useStack,slotBound,StackSemEvaluate.evaluate_skip,post]
    · have scratch := CallDest.stateRel_setVar_of_ge k (Nat.le_refl k) value related
      have updated := StateRelRegisterUpdate.wordToStackStateRelSetVar2 (register/2) value
        target.stack target.stackSpace scratch inReg halfBound rfl rfl
      simpa only [post,slot,registerEq] using updated
    · simpa [post] using lengthEq

end Flapjack.WordToStackProofs.StoreRegister
