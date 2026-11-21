module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvLookup
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation

@[expose] public section

/-! Code locations stored for reference-pointer locals
(`data_to_wordProofScript.sml` lines 136-169). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A word related through `Forall₂` has a related root. Flapjack-specific
list helper. -/
private theorem forall₂_exists_left {α β : Type} (R : α → β → Prop) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil => by simp
  | _, _, .cons (a := a) (b := b) (l₁ := l₁) (l₂ := l₂) hab rest => by
    intro y member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨x, inXs, hx⟩ := forall₂_exists_left R l₁ l₂ rest y inTail
      exact ⟨x, List.mem_cons_of_mem a inXs, hx⟩

namespace reviewedStateRelGetVarRefPtrLocMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRelGetVarRefPtrLocMap

/-- A target local related to a source reference pointer that holds a code
location has a zero offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_get_var_RefPtr_Loc"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVar_refPtr_loc {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (v1 : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (n : Nat) (b : Bool) (p n1 n2 : Nat)
    (premises : stateRel c l1 l2 s t v1 locs ∧
      DataSem.getVar n s.locals = some (.refPtr b p) ∧
      WordSemStateFiniteExact.getVar (adjustVar n) t = some (.loc n1 n2)) :
    n2 = 0 := by
  obtain ⟨related, sourceFound, targetFound⟩ := premises
  have hmem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, _, hinv, _, _⟩ := hmem
  have added := wordMlInv_lookup heap t.be a sp sp1 gens limit (holThe s.tstamps)
    c s.refs (v1.getD []) ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    s.locals t.locals n (.refPtr b p) (.loc n1 n2)
    ⟨by simpa [List.append_assoc] using hinv, sourceFound, targetFound⟩
  obtain ⟨roots, _, addresses⟩ := added
  have inSnd : WordLocW.loc n1 n2 ∈
      (v1.getD [] ++ [(DataSem.Value.refPtr b p, WordLocW.loc n1 n2)] ++
        joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
        ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)).map
          Prod.snd := by
    simp
  obtain ⟨root, _, rootAddr⟩ := forall₂_exists_left _ _ _ addresses _ inSnd
  cases root with
  | pointer index word => simp [wordAddr] at rootAddr
  | data word =>
    cases word with
    | word word => simp [wordAddr] at rootAddr
    | loc label offset =>
      simp [wordAddr] at rootAddr
      exact rootAddr.2.symm

end Flapjack.Compiler.Backend.DataToWord.Proofs
