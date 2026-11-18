module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InterInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AdjustedSet

@[expose] public section

/-! State relation invariance under reserved target-local insertions. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord Classical

namespace stateInsertMap
/-- Canonical target-state finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end stateInsertMap

private theorem stateRel_insertOdd {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (key : Nat) (x : WordLocW width) (odd : key % 2 = 1) :
    stateRel conf l1 l2 s {t with locals := sptInsert key x t.locals} v locs =
      stateRel conf l1 l2 s t v locs := by
  have h0 : sptLookup 0 (sptInsert key x t.locals) = sptLookup 0 t.locals := by
    apply sptLookup_sptInsert_ne
    omega
  have hadj (n : Nat) : sptLookup (adjustVar n) (sptInsert key x t.locals) =
      sptLookup (adjustVar n) t.locals := by
    apply sptLookup_sptInsert_ne
    simp only [adjustVar]
    omega
  have hi : sptInter (sptInsert key x t.locals) (adjustSet s.locals) =
      sptInter t.locals (adjustSet s.locals) := by
    rw [inter_insert]
    have absent := lookup_odd_adjustSet key s.locals odd
    simp [sptDomain, absent]
  simp only [stateRel, h0, hadj, hi]

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_insert_1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_insert_1 {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (x : WordLocW width) :
    stateRel conf l1 l2 s {t with locals := sptInsert 1 x t.locals} v locs =
      stateRel conf l1 l2 s t v locs :=
  stateRel_insertOdd conf l1 l2 s t v locs 1 x rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_insert_3"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_insert_3 {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (x : WordLocW width) :
    stateRel conf l1 l2 s {t with locals := sptInsert 3 x t.locals} v locs =
      stateRel conf l1 l2 s t v locs :=
  stateRel_insertOdd conf l1 l2 s t v locs 3 x rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_insert_7"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_insert_7 {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (x : WordLocW width) :
    stateRel conf l1 l2 s {t with locals := sptInsert 7 x t.locals} v locs =
      stateRel conf l1 l2 s t v locs :=
  stateRel_insertOdd conf l1 l2 s t v locs 7 x rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_insert_3_1"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_insert_3_1 {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (v : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (x y : WordLocW width) :
    stateRel conf l1 l2 s {t with locals := sptInsert 3 x (sptInsert 1 y t.locals)} v locs =
      stateRel conf l1 l2 s t v locs := by
  calc
    _ = stateRel conf l1 l2 s {t with locals := sptInsert 1 y t.locals} v locs :=
      stateRel_insert_3 conf l1 l2 s {t with locals := sptInsert 1 y t.locals} v locs x
    _ = stateRel conf l1 l2 s t v locs := stateRel_insert_1 conf l1 l2 s t v locs y

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_incClock {width : Nat} [NeZero width] {C F : Type} (conf : Config) (l1 l2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (h : stateRel conf l1 l2 s t none locs) :
    stateRel conf l1 l2 {s with clock := s.clock + 1} {t with clock := t.clock + 1} none locs := by
  have hc : t.clock = s.clock := h.2.1
  simpa [hc] using stateRel_withClock conf l1 l2 s t none locs (s.clock + 1) h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
