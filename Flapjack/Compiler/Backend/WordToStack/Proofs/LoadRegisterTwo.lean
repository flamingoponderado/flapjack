import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegister

namespace Flapjack.WordToStackProofs.LoadRegisterTwo
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



/-- Complete original second-register stack load, preserving every original
clock/bitmap/state relation/stack/resource/register/additive expression
conjunct. The actual source lookup and full relation derive spill bounds;
only the original wReg2 equation, EVEN, source read and relation are premises.
No target execution, range or postrelation assumption is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateWStackLoadWReg2 {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame r reg : Nat) (loads : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (value : WordLocW width)
    (compiled : wReg2 r (k,f,frame) = (loads,reg))
    (even : r % 2 = 0)
    (sourceRead : WordSemStateFiniteExact.getVar r source = some value)
    (related : stateRel ac k f frame source target lens 0) :
    ∃ post : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (wStackLoadNative loads .skip,target) = (none,post) ∧
      target.clock = post.clock ∧ target.bitmaps = post.bitmaps ∧
      stateRel ac k f frame source post lens 0 ∧
      post.stack.length = target.stack.length ∧ post.stackSpace = target.stackSpace ∧
      (∀ register, register ≠ k+1 → StackSemStateOps.getVar register post =
        StackSemStateOps.getVar register target) ∧
      (∀ register (constant : BitVec width), register ≠ k+1 →
        StackSemExpressions.wordExp post (.op .add [.var register,.const constant]) =
        StackSemExpressions.wordExp target (.op .add [.var register,.const constant])) ∧
      StackSemStateOps.getVar reg post = some value := by
  by_cases below : r / 2 < k
  · simp only [wReg2,below,if_true,Prod.mk.injEq] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    refine ⟨target,StackSemEvaluate.evaluate_skip target,rfl,rfl,related,rfl,rfl,
      (fun _ _ => rfl),(fun _ _ _ => rfl),?_⟩
    exact StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 r value
      ⟨related,sourceRead,even,below⟩
  · simp only [wReg2,below,if_false,Prod.mk.injEq] at compiled
    obtain ⟨rfl,rfl⟩ := compiled
    have placement := StateRelGetVar.stateRel_locals related r value sourceRead
    rw [if_neg below] at placement
    obtain ⟨_,slot,bound⟩ := placement
    rw [Nat.add_zero,List.getElem?_take,List.getElem?_drop] at slot
    split at slot
    swap
    · cases slot
    have stackBound := (List.getElem?_eq_some_iff.mp slot).1
    have stackValue := (List.getElem?_eq_some_iff.mp slot).2
    have useStack : target.useStack = true := related.2.2.2.2.1
    refine ⟨StackSemStateOps.setVar (k+1) value target,?_,rfl,rfl,
      CallDest.stateRel_setVar_of_ge (k+1) (by omega) value related,rfl,rfl,?_,?_,?_⟩
    · rw [wStackLoadNative,StackSemEvaluate.evaluate_seq,StackSemEvaluate.evaluate_stackLoad,
        if_neg (by simp [useStack]),dif_pos stackBound]
      simp only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self]
      rw [wStackLoadNative,StackSemEvaluate.evaluate_skip,stackValue]
    · intro register different
      simp [StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,
        FUPDATE_HOL,different]
    · intro register constant different
      have read : (StackSemStateOps.setVar (k+1) value target).regs.lookup register =
          target.regs.lookup register := by
        simp [StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL,different]
      simp only [StackSemExpressions.wordExp,List.attach_cons,List.attach_nil,List.map_cons,List.map_nil]
      rw [read]
    · simp [StackSemStateOps.getVar,StackSemStateOps.setVar,HolFiniteMapExact.updateEq,FUPDATE_HOL]

end Flapjack.WordToStackProofs.LoadRegisterTwo
