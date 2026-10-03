import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
namespace Flapjack.WordToStackProofs.RegisterWrite
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
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



/-- Full original wRegWrite1_thm1 (3722–3743), including the arbitrary
continuation callback and all existential run/relation/resource conclusions.
The callback run is HOL’s original premise, not an assumed compiler result. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wRegWrite1_thm1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]

theorem wRegWrite1Thm1 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame m : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (value : WordLocW width) (kont : Nat → HolProg width)
    (related : stateRel ac k f frame source target lens 0)
    (bound : m < frame+k)
    (run : ∀ n, n ≤ k → StackSemEvaluate.evaluate (kont n,target) =
      (none,StackSemStateOps.setVar n value target)) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wRegWrite1Native kont (2*m) (k,f,frame),target) =
        (none,post) ∧
      stateRel ac k f frame (WordSemStateFiniteExact.setVar (2*m) value source)
        post lens 0 ∧ post.stack.length = target.stack.length ∧
      post.stackSpace = target.stackSpace := by
  have half : 2*m/2 = m := by omega
  by_cases physical : m < k
  · simp only [wRegWrite1Native,half,if_pos physical]
    exact ⟨StackSemStateOps.setVar m value target,run m (by omega),
      StateRelRegisterUpdate.stateRelSetVar m value related physical,rfl,rfl⟩
  · have shape : if frame=0 then f=0 else f=frame+1 :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have frameShape : f=frame+1 := by split at shape <;> omega
    have resource : target.stackSpace+f ≤ target.stack.length :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have slot : f-1-(m-k) = f+k-(m+1) := by omega
    have slotBound : target.stackSpace+(f-1-(m-k)) < target.stack.length := by omega
    have useStack : target.useStack = true := related.2.2.2.2.1
    let post := {StackSemStateOps.setVar k value target with
      stack := target.stack.set (target.stackSpace+(f-1-(m-k))) value}
    refine ⟨post,?_,?_,by simp [post],rfl⟩
    · simp only [wRegWrite1Native,half,if_neg physical,StackSemEvaluate.evaluate_seq,
        run k (Nat.le_refl k)]
      simp [StackSemControl.fixClock,StackSemStateOps.setVar,
        StackSemEvaluate.evaluate_stackStore,useStack,slotBound,
        StackSemStateOps.getVar,HolFiniteMapExact.updateEq,FUPDATE_HOL,post]
    · have scratch := CallDest.stateRel_setVar_of_ge k (Nat.le_refl k) value related
      have preserved := StateRelRegisterUpdate.wordToStackStateRelSetVar2 m value
        target.stack target.stackSpace scratch physical bound rfl rfl
      simpa only [post,slot] using preserved
end Flapjack.WordToStackProofs.RegisterWrite
