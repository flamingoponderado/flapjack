import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
import Flapjack.Misc.Sptree.Subspt

namespace Flapjack.WordToStackProofs.LocationLabels
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

/-- Full original code-domain inclusion from the complete state relation.
Arbitrary source/target/frame/lens/extra are retained; no code inclusion or
successful execution is supplied as an extra premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stateRelCodeDomain {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra : Nat)
    (related : stateRel ac k f frame source target lens extra) :
    ∀ key, sptDomain source.code key → sptDomain target.code key := by
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, domains, _⟩
  intro key member
  rw [domains]
  exact Or.inr (Or.inr member)

/-- Full original location-check set inclusion under native sptree extension.
All code trees/labels are arbitrary; the sole premise is subspt, with no
well-formedness, successful lookup or evaluation premise added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem locCheckSubset {width : Nat} [NeZero width]
    (source target : Spt (HolProg width)) (extension : sptSubspt source target) :
    ∀ label, StackSem.locCheckExact source label → StackSem.locCheckExact target label := by
  intro label checked
  rcases checked with ⟨zero, member⟩ | ⟨key, program, lookup, labels⟩
  · exact Or.inl ⟨zero, (extension label.1 member).1⟩
  · exact Or.inr ⟨key, program, (sptSubsptLookup source target).1 extension key program lookup, labels⟩

end Flapjack.WordToStackProofs.LocationLabels
