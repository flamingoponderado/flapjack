import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness


/-- Flapjack infrastructure: replacing both equal code buffers preserves the
original full relation; no independent HOL declaration is claimed. -/
theorem stateRelCodeBuffer {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (buffer : WordSemBuffer width 8)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with codeBuffer := buffer}
      {target with codeBuffer := buffer} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,True.intro,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩

/-- Genuine original CodeBufferWrite case, retaining the original four
premises and full existential native target run/post-state relation. Operand
lookups and buffer success on the target are proved from the source relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.codeBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.codeBufferWrite first second : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.codeBufferWrite first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have buffers : target.codeBuffer = source.codeBuffer := relation.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [evaluate_codeBufferWrite] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          cases write : wordSemBufferWrite source.codeBuffer left (right.setWidth 8) with
          | none =>
            simp only [write] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some buffer =>
            simp only [write] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
            have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
            refine ⟨0, {target with codeBuffer := buffer}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                (evaluate_codeBufferWrite first second target).trans (by
                  simp only [getVar, targetFirst, targetSecond, buffers, write])
            · exact stateRelCodeBuffer jump bounds pointer source target buffer relation
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite
