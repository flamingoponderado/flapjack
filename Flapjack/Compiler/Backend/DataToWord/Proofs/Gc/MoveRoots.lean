module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.LocMerge
public import Flapjack.Compiler.Backend.WordGcFunctions.Roots

@[expose] public section

/-! Collector traversal of location roots and word roots. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.WordGcFunctions

/-- Code-location roots must refer to entry offset zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "loc_ok_def"
  (words_as_type_indexed_bitvec)]
def locOk {width : Nat} [NeZero width] : WordLocW width → Bool
  | .loc _ offset => decide (offset = 0)
  | .word _ => true

/-- Moving all roots is equivalent to moving only the word roots and
reinstating the original code locations. -/
theorem wordGcMoveRoots_filter_eq {width : Nat} [NeZero width]
    (conf : Config) (roots : List (WordLocW width))
    (valid : roots.all locOk = true) (i pa old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) :
    wordGcMoveRoots conf (roots, i, pa, old, memory, domain) =
      let (moved, i', pa', memory', ok) :=
        wordGcMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, old, memory, domain)
      (locMerge roots moved, i', pa', memory', ok) := by
  induction roots generalizing i pa memory with
  | nil => simp [wordGcMoveRoots, locMerge]
  | cons root roots ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    cases root with
    | loc a b =>
      have zero : b = 0 := by simpa [locOk] using valid.1
      subst b
      simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte,
        wordGcMoveRoots, wordGcMove, decide_true, Bool.true_and]
      have h := ih valid.2 i pa memory
      cases result : wordGcMoveRoots conf (List.filter wordSemIsWordLoc roots, i, pa, old, memory, domain) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', memory', ok⟩
        simp only [result] at h ⊢
        rw [h]
        rfl
    | word w =>
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte, wordGcMoveRoots]
      cases move : wordGcMove conf (.word w, i, pa, old, memory, domain) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', memory', ok⟩
        have h := ih valid.2 i' pa' memory'
        cases result : wordGcMoveRoots conf (List.filter wordSemIsWordLoc roots, i', pa', old, memory', domain) with
        | mk movedRoots rest =>
          rcases rest with ⟨i'', pa'', memory'', ok'⟩
          simp only [result] at h ⊢
          rw [h]
          rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gc_move_roots_IMP_FILTER"
  (words_as_type_indexed_bitvec)]
theorem wordGcMoveRoots_imp_filter {width : Nat} [NeZero width]
    (roots : List (WordLocW width)) (i pa old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (moved : List (WordLocW width)) (i' pa' : BitVec width)
    (memory' : BitVec width → WordLocW width) (ok : Bool) (conf : Config)
    (filtered : wordGcMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, old, memory, domain) =
      (moved, i', pa', memory', ok))
    (valid : roots.all locOk = true) :
    wordGcMoveRoots conf (roots, i, pa, old, memory, domain) =
      (locMerge roots moved, i', pa', memory', ok) := by
  rw [wordGcMoveRoots_filter_eq conf roots valid i pa old memory domain, filtered]

/-- The partial generational collector also skips valid code locations
without changing its memory or generation bounds. -/
theorem wordGenGcPartialMoveRoots_filter_eq {width : Nat} [NeZero width]
    (conf : Config) (roots : List (WordLocW width))
    (valid : roots.all locOk = true) (i pa old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (gs rs : BitVec width) :
    wordGenGcPartialMoveRoots conf (roots, i, pa, old, memory, domain, gs, rs) =
      let (moved, i', pa', memory', ok) :=
        wordGenGcPartialMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, old, memory, domain, gs, rs)
      (locMerge roots moved, i', pa', memory', ok) := by
  induction roots generalizing i pa memory with
  | nil => simp [wordGenGcPartialMoveRoots, locMerge]
  | cons root roots ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    cases root with
    | loc a b =>
      have zero : b = 0 := by simpa [locOk] using valid.1
      subst b
      simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte,
        wordGenGcPartialMoveRoots, wordGenGcPartialMove, decide_true, Bool.true_and]
      have h := ih valid.2 i pa memory
      cases result : wordGenGcPartialMoveRoots conf
          (List.filter wordSemIsWordLoc roots, i, pa, old, memory, domain, gs, rs) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', memory', ok⟩
        simp only [result] at h ⊢
        rw [h]
        rfl
    | word w =>
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte, wordGenGcPartialMoveRoots]
      cases move : wordGenGcPartialMove conf (.word w, i, pa, old, memory, domain, gs, rs) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', memory', ok⟩
        have h := ih valid.2 i' pa' memory'
        cases result : wordGenGcPartialMoveRoots conf
            (List.filter wordSemIsWordLoc roots, i', pa', old, memory', domain, gs, rs) with
        | mk movedRoots rest =>
          rcases rest with ⟨i'', pa'', memory'', ok'⟩
          simp only [result] at h ⊢
          rw [h]
          rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_partial_move_roots_IMP_FILTER" 6325
  (words_as_type_indexed_bitvec)]
theorem wordGenGcPartialMoveRoots_imp_filter {width : Nat} [NeZero width]
    (roots : List (WordLocW width)) (i pa old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (gs rs : BitVec width)
    (moved : List (WordLocW width)) (i' pa' : BitVec width)
    (memory' : BitVec width → WordLocW width) (ok : Bool) (conf : Config)
    (filtered : wordGenGcPartialMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, old, memory, domain, gs, rs) =
      (moved, i', pa', memory', ok))
    (valid : roots.all locOk = true) :
    wordGenGcPartialMoveRoots conf (roots, i, pa, old, memory, domain, gs, rs) =
      (locMerge roots moved, i', pa', memory', ok) := by
  rw [wordGenGcPartialMoveRoots_filter_eq conf roots valid i pa old memory domain gs rs, filtered]

/-- Full generational root traversal preserves the same filtered execution,
including both allocation areas. -/
theorem wordGenGcMoveRoots_filter_eq {width : Nat} [NeZero width]
    (conf : Config) (roots : List (WordLocW width))
    (valid : roots.all locOk = true) (i pa ib pb old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) :
    wordGenGcMoveRoots conf (roots, i, pa, ib, pb, old, memory, domain) =
      let (moved, i', pa', ib', pb', memory', ok) :=
        wordGenGcMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, ib, pb, old, memory, domain)
      (locMerge roots moved, i', pa', ib', pb', memory', ok) := by
  induction roots generalizing i pa ib pb memory with
  | nil => simp [wordGenGcMoveRoots, locMerge]
  | cons root roots ih =>
    simp only [List.all_cons, Bool.and_eq_true] at valid
    cases root with
    | loc a b =>
      have zero : b = 0 := by simpa [locOk] using valid.1
      subst b
      simp only [List.filter_cons, wordSemIsWordLoc, Bool.false_eq_true, ↓reduceIte,
        wordGenGcMoveRoots, wordGenGcMove, decide_true, Bool.true_and]
      have h := ih valid.2 i pa ib pb memory
      cases result : wordGenGcMoveRoots conf
          (List.filter wordSemIsWordLoc roots, i, pa, ib, pb, old, memory, domain) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', ib', pb', memory', ok⟩
        simp only [result] at h ⊢
        rw [h]
        rfl
    | word w =>
      simp only [List.filter_cons, wordSemIsWordLoc, ↓reduceIte, wordGenGcMoveRoots]
      cases move : wordGenGcMove conf (.word w, i, pa, ib, pb, old, memory, domain) with
      | mk moved rest =>
        rcases rest with ⟨i', pa', ib', pb', memory', ok⟩
        have h := ih valid.2 i' pa' ib' pb' memory'
        cases result : wordGenGcMoveRoots conf
            (List.filter wordSemIsWordLoc roots, i', pa', ib', pb', old, memory', domain) with
        | mk movedRoots rest =>
          rcases rest with ⟨i'', pa'', ib'', pb'', memory'', ok'⟩
          simp only [result] at h ⊢
          rw [h]
          rfl

@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_roots_IMP_FILTER"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveRoots_imp_filter {width : Nat} [NeZero width]
    (roots : List (WordLocW width)) (i pa ib pb old : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (moved : List (WordLocW width)) (i' pa' ib' pb' : BitVec width)
    (memory' : BitVec width → WordLocW width) (ok : Bool) (conf : Config)
    (filtered : wordGenGcMoveRoots conf (roots.filter wordSemIsWordLoc, i, pa, ib, pb, old, memory, domain) =
      (moved, i', pa', ib', pb', memory', ok))
    (valid : roots.all locOk = true) :
    wordGenGcMoveRoots conf (roots, i, pa, ib, pb, old, memory, domain) =
      (locMerge roots moved, i', pa', ib', pb', memory', ok) := by
  rw [wordGenGcMoveRoots_filter_eq conf roots valid i pa ib pb old memory domain, filtered]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
