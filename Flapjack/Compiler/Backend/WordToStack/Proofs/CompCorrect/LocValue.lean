import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterWrite
namespace Flapjack.WordToStackProofs.CompCorrect.LocValue
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



/-- Full original LocValue constructor (6905–6924). Complete original
simulation premises and conclusion retained. Target label validity is derived
from source success and the full code-domain relation; no targetrun or label
premise is added. Evaluator closure inherits reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register location : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Seq.Simulation ac (.locValue register location) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  by_cases present : sptMem location source.code
  swap
  · simp [present] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  · simp only [present,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have codeDomain : sptDomain target.code =
        (fun n => n=raiseStubLocation ∨ n=storeConstsStubLocation ∨ sptDomain source.code n) :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have valid : StackSem.locCheckExact target.code (location,0) := by
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change sptDomain target.code location
      rw [codeDomain]
      exact Or.inr (Or.inr present)
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.locValue r location 0,target) =
        (none,StackSemStateOps.setVar r (.loc location 0) target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_locValue,valid]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens (.loc location 0) (fun r => .locValue r location 0)
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0,post,none,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel
end Flapjack.WordToStackProofs.CompCorrect.LocValue
