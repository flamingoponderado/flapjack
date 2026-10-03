import Flapjack.Compiler.Backend.WordToStack.Proofs.CallDest
import Flapjack.Misc.Sptree.Wf
namespace Flapjack.WordToStackProofs.StateRelRegisterUpdate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
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



/-- Full original physical-register update law (2930–2951). Every stateRel
conjunct, arbitrary extra offset and Word/Loc payload is retained. The inherited
real carrier is unchanged; this structural update asserts no FP equivalence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem stateRelSetVar {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (x : Nat) (value : WordLocW width)
    (related : stateRel ac k f frame source target lens extra) (physical : x < k) :
    stateRel ac k f frame (WordSemStateFiniteExact.setVar (2*x) value source)
      (StackSemStateOps.setVar x value target) lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,?_,
    h37,h38,?_⟩
  · exact sptWfInsert (2*x) value source.locals h36
  · intro n v found
    change sptLookup n (sptInsert (2*x) value source.locals) = some v at found
    by_cases same : n = 2*x
    · subst n
      rw [sptLookup_sptInsert_same] at found
      have valueEq : value = v := Option.some.inj found
      subst v
      have half : 2*x/2 = x := by omega
      simp [half, physical, StackSemStateOps.setVar, HolFiniteMapExact.updateEq,
        FUPDATE_HOL]
    · rw [sptLookup_sptInsert_ne (2*x) n value source.locals same] at found
      obtain ⟨even, placement⟩ := hloc n v found
      refine ⟨even, ?_⟩
      by_cases inReg : n/2 < k
      · rw [if_pos inReg] at placement ⊢
        have different : n/2 ≠ x := by omega
        simpa [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL,
          different] using placement
      · rw [if_neg inReg] at placement ⊢
        exact placement
end Flapjack.WordToStackProofs.StateRelRegisterUpdate
