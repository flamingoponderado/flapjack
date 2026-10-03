import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocSimulation
namespace Flapjack.WordToStackProofs.StateRelStoreUpdate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open WordSemStateFiniteExact
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



/-- Full original state_rel_set_store (5132–5147). Arbitrary frame/extra,
store name and Word/Loc value are retained, with the original nonHandler guard.
Every stateRel conjunct is preserved. This structural relation asserts no
numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "state_rel_set_store"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]

theorem stateRelSetStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (s5 : WordSemStateFiniteExact width (Nat × C) F)
    (t5 : StackSemStateFiniteExact width C F) (len : List Nat) (extra : Nat)
    (name : WordStoreHOL) (w : WordLocW width) (notHandler : name ≠ .handler) :
    stateRel ac k f frame s5 t5 len extra →
      stateRel ac k f frame (setStore name w s5)
        (StackSemStateOps.setStore name w t5) len extra := by
  intro h
  unfold stateRel at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38⟩ := h
  have hhandler : (t5.store.updateEq (name, w)).lookup .handler =
      t5.store.lookup .handler := by
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, Ne.symm notHandler]
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15, h16, ?_, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, ?_⟩
  · show s5.store.updateEq (name, w) =
      (t5.store.updateEq (name, w)).eraseEq .handler
    rw [h12]
    apply AllocSimulation.fmap_ext
    intro key
    by_cases hk : key = .handler
    · subst hk; simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL, Ne.symm notHandler]
    · by_cases ha : key = .allocSize
      · subst ha
        simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL]
      · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL, hk]
  · show (t5.store.updateEq (name, w)).lookup .handler ≠ none
    rw [hhandler]; exact h17
  · show (stackRel k s5.handler s5.stack
        ((t5.store.updateEq (name, w)).lookup .handler) _ _ _ len ∧ _)
    rw [hhandler]
    exact h38

end Flapjack.WordToStackProofs.StateRelStoreUpdate
